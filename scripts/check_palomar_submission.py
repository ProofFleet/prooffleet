#!/usr/bin/env python3
"""Toolchain-free pre-submission checks for the Palomar registry entry (docs/edp-release.md).

Palomar rejects a submission on mechanical grounds before it builds anything if the repository
breaks one of its intake rules (PalomarRegistry/PalomarPolicy CONTRIBUTING.md sections 2 and 3,
implemented in PalomarRegistry/PalomarSubmission scripts/verify_submission.py). This script
checks the rules that can be decided from the checkout alone:

- comparator.json: the four required keys, no keys Palomar rejects, distinct module names that
  resolve to committed files, and only the three standard axioms;
- lean-toolchain: a Lean release no older than Palomar's minimum, equal to the lean-toolchain of
  the pinned Mathlib revision;
- lake-manifest.json: every Git dependency a credential-free public GitHub URL pinned to a full
  lowercase commit, and (when the packages are materialised) exactly Mathlib's own pins;
- packaging: one Lakefile, one root licence file, no submodules, no Git LFS, no committed build
  artifacts, and a checkout under 500 MiB;
- PalomarEDP/Challenge.lean: within the size limits, importing Mathlib only, with exactly one
  statement hole;
- formalization.yaml: valid YAML without duplicate keys, version v0.4, no retained TEMPLATE
  values, and an Apache-2.0 licence matching LICENSE. With --formalization-schema it is also
  validated against the upstream v0.4 JSON schema, and with --palomar-submission against
  Palomar's own intake validator and taxonomies.

This rehearses Palomar's intake rules; it is not Palomar's verdict. The reusable preflight
workflow described in docs/edp-release.md is the closest predictor, and it needs the repository
to be public. Exit status 1 means at least one check failed.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
import urllib.request
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent

# SHA-256 of the canonical Apache License 2.0 text (https://www.apache.org/licenses/LICENSE-2.0.txt).
APACHE_2_0_SHA256 = "cfc7749b96f63bd31c3c42b5c471bf756814053e847c10f3eb003417bc523d30"
DEFAULT_TOOLCHAIN_MINIMUM = "v4.35.0-rc2"
PERMITTED_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
COMPARATOR_REQUIRED = {"challenge_module", "solution_module", "theorem_names", "permitted_axioms"}
COMPARATOR_OPTIONAL = {"definition_names", "enable_nanoda"}
MODULE_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(\.[A-Za-z_][A-Za-z0-9_']*)*")
TOOLCHAIN_RE = re.compile(r"leanprover/lean4:v(\d+)\.(\d+)\.(\d+)(?:-rc(\d+))?")
GITHUB_URL_RE = re.compile(r"https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+")
LICENSE_NAME_RE = re.compile(r"(licen[cs]e|copying|unlicense|ofl)(\.md|\.markdown|\.txt)?", re.I)
ARTIFACT_SUFFIXES = (".a", ".bc", ".dll", ".dylib", ".ilean", ".ir", ".o", ".obj", ".olean",
                     ".so", ".trace", ".olean.private", ".olean.server")
SENTINEL_RE = re.compile(r"\ATEMPLATE(?::|\Z)")
CHALLENGE_HARD = (100 * 1024, 1000)
CHALLENGE_SOFT = (32 * 1024, 300)

failures: list[str] = []
warnings: list[str] = []


def ok(message: str) -> None:
    print(f"PASS  {message}")


def fail(message: str) -> None:
    failures.append(message)
    print(f"FAIL  {message}")


def warn(message: str) -> None:
    warnings.append(message)
    print(f"WARN  {message}")


def git(*args: str) -> str:
    return subprocess.run(["git", *args], cwd=REPO, check=True, capture_output=True,
                          text=True).stdout


def toolchain_key(spec: str) -> tuple[int, int, int, int] | None:
    match = TOOLCHAIN_RE.fullmatch(spec)
    if not match:
        return None
    major, minor, patch, rc = match.groups()
    # A release candidate sorts before the release it precedes.
    return int(major), int(minor), int(patch), int(rc) if rc else 1 << 30


def module_path(module: str) -> Path:
    return REPO.joinpath(*module.split(".")).with_suffix(".lean")


def check_comparator() -> dict:
    start = len(failures)
    path = REPO / "comparator.json"
    try:
        config = json.loads(path.read_text(encoding="utf-8"),
                            object_pairs_hook=_reject_duplicate_keys)
    except (OSError, ValueError) as error:
        fail(f"comparator.json is not one valid JSON object: {error}")
        return {}
    if not isinstance(config, dict):
        fail("comparator.json must contain one JSON object")
        return {}
    keys = set(config)
    if missing := COMPARATOR_REQUIRED - keys:
        fail(f"comparator.json lacks required keys {sorted(missing)}")
    if extra := keys - COMPARATOR_REQUIRED - COMPARATOR_OPTIONAL:
        fail(f"comparator.json has keys Palomar rejects: {sorted(extra)}")
    challenge, solution = config.get("challenge_module"), config.get("solution_module")
    for role, module in (("challenge", challenge), ("solution", solution)):
        if not isinstance(module, str) or not MODULE_RE.fullmatch(module):
            fail(f"comparator.json {role}_module is not a dotted Lean module name: {module!r}")
        elif not module_path(module).is_file():
            fail(f"{role} module {module} has no source file {module_path(module).relative_to(REPO)}")
    if challenge == solution:
        fail("comparator.json challenge and solution modules must differ")
    theorems = config.get("theorem_names")
    if not isinstance(theorems, list) or not theorems or not all(
            isinstance(name, str) and MODULE_RE.fullmatch(name) for name in theorems):
        fail("comparator.json theorem_names must be a nonempty list of declaration names")
    definitions = config.get("definition_names", [])
    if not isinstance(definitions, list) or not all(
            isinstance(name, str) and MODULE_RE.fullmatch(name) for name in definitions):
        fail("comparator.json definition_names must be a list of declaration names")
    axioms = config.get("permitted_axioms")
    if not isinstance(axioms, list) or not set(axioms) <= PERMITTED_AXIOMS:
        fail(f"comparator.json permitted_axioms must be a subset of {sorted(PERMITTED_AXIOMS)}")
    if len(failures) == start:
        ok(f"comparator.json: {challenge} vs {solution}, theorems {theorems}, "
           f"definition holes {definitions}, axioms {axioms}")
    return config


def _reject_duplicate_keys(pairs):
    keys = [key for key, _ in pairs]
    if len(keys) != len(set(keys)):
        raise ValueError(f"duplicate keys {sorted({k for k in keys if keys.count(k) > 1})}")
    return dict(pairs)


def check_toolchain(minimum: str, offline: bool) -> None:
    spec = (REPO / "lean-toolchain").read_text(encoding="utf-8").strip()
    key, floor = toolchain_key(spec), toolchain_key(f"leanprover/lean4:{minimum}")
    if key is None:
        fail(f"lean-toolchain is not a leanprover/lean4 release: {spec!r}")
        return
    if floor is None or key < floor:
        fail(f"lean-toolchain {spec} is older than Palomar's minimum {minimum}")
    else:
        ok(f"lean-toolchain {spec} is at least Palomar's minimum {minimum}")
    manifest = json.loads((REPO / "lake-manifest.json").read_text(encoding="utf-8"))
    mathlib = next((p for p in manifest.get("packages", []) if p.get("name") == "mathlib"), None)
    if mathlib is None:
        warn("no mathlib package in lake-manifest.json; toolchain match not checked")
        return
    rev = mathlib.get("rev", "")
    local = REPO / ".lake" / "packages" / "mathlib"
    mathlib_spec = None
    try:
        if (local / "lean-toolchain").is_file() and subprocess.run(
                ["git", "-C", str(local), "rev-parse", "HEAD"], capture_output=True,
                text=True).stdout.strip() == rev:
            mathlib_spec = (local / "lean-toolchain").read_text(encoding="utf-8").strip()
        elif not offline:
            url = f"https://raw.githubusercontent.com/leanprover-community/mathlib4/{rev}/lean-toolchain"
            with urllib.request.urlopen(url, timeout=30) as response:
                mathlib_spec = response.read().decode("utf-8").strip()
    except OSError as error:
        warn(f"could not read Mathlib's lean-toolchain at {rev}: {error}")
    if mathlib_spec is None:
        warn("Mathlib's lean-toolchain not checked (offline, and packages not materialised)")
    elif mathlib_spec != spec:
        fail(f"lean-toolchain {spec} differs from Mathlib {rev[:12]}'s {mathlib_spec}")
    else:
        ok(f"lean-toolchain equals the lean-toolchain of Mathlib {rev}")


def check_manifest() -> None:
    manifest = json.loads((REPO / "lake-manifest.json").read_text(encoding="utf-8"))
    if manifest.get("packagesDir", ".lake/packages") != ".lake/packages":
        fail(f"lake-manifest.json packagesDir must be .lake/packages, not {manifest.get('packagesDir')!r}")
    packages = manifest.get("packages")
    if not isinstance(packages, list):
        fail("lake-manifest.json has no packages list")
        return
    names = [p.get("name") for p in packages]
    if len(names) != len(set(names)):
        fail(f"lake-manifest.json names a package twice: {names}")
    bad = []
    for package in packages:
        if package.get("type") != "git":
            bad.append(f"{package.get('name')}: type {package.get('type')!r} (only git is expected here)")
            continue
        url = package.get("url", "").rstrip("/").removesuffix(".git")
        if not GITHUB_URL_RE.fullmatch(url):
            bad.append(f"{package.get('name')}: URL {package.get('url')!r} is not a public GitHub HTTPS URL")
        if not re.fullmatch(r"[0-9a-f]{40}", package.get("rev", "")):
            bad.append(f"{package.get('name')}: rev {package.get('rev')!r} is not a full lowercase commit")
    for problem in bad:
        fail(f"lake-manifest.json {problem}")
    if not bad:
        ok(f"lake-manifest.json: {len(packages)} Git dependencies, all public GitHub URLs pinned to full commits")
    upstream = REPO / ".lake" / "packages" / "mathlib" / "lake-manifest.json"
    if upstream.is_file():
        ours = {p["name"]: p for p in packages}
        theirs = json.loads(upstream.read_text(encoding="utf-8")).get("packages", [])
        drift = [p["name"] for p in theirs
                 if p["name"] not in ours or ours[p["name"]].get("rev") != p.get("rev")]
        if drift:
            fail(f"lake-manifest.json disagrees with Mathlib's own pins for {drift}")
        else:
            ok(f"lake-manifest.json repeats Mathlib's own pins for all {len(theirs)} of its dependencies")
    else:
        warn("Mathlib's own manifest not checked (run `lake exe cache get` to materialise packages)")


def check_packaging() -> None:
    lakefiles = [name for name in ("lakefile.toml", "lakefile.lean") if (REPO / name).is_file()]
    if len(lakefiles) != 1:
        fail(f"the project root must hold exactly one Lakefile, found {lakefiles}")
    elif (REPO / lakefiles[0]).stat().st_size > 1 << 20:
        fail(f"{lakefiles[0]} exceeds 1 MiB")
    else:
        ok(f"one Lakefile ({lakefiles[0]}) and a committed lake-manifest.json")
    licences = [p for p in REPO.iterdir() if p.is_file() and LICENSE_NAME_RE.fullmatch(p.name)]
    if len(licences) != 1:
        fail(f"the repository root must hold exactly one licence file, found {[p.name for p in licences]}")
    else:
        licence = licences[0]
        digest = hashlib.sha256(licence.read_bytes()).hexdigest()
        if licence.is_symlink() or licence.stat().st_size == 0 or licence.stat().st_size > 1 << 20:
            fail(f"{licence.name} must be a regular nonempty file of at most 1 MiB")
        elif digest != APACHE_2_0_SHA256:
            warn(f"{licence.name} is not byte-identical to the canonical Apache-2.0 text; "
                 "confirm with Licensee 10.0.0 that it is detected as Apache-2.0")
        else:
            ok(f"{licence.name} is the canonical Apache License 2.0 text (sha256 {digest[:16]}…)")
    tracked = git("ls-files", "-s", "-z").split("\0")
    entries = [line.split("\t", 1) for line in tracked if line]
    submodules = [path for meta, path in entries if meta.startswith("160000")]
    symlinks = {path for meta, path in entries if meta.startswith("120000")}
    paths = [path for _, path in entries]
    if submodules:
        fail(f"Git submodules are not accepted: {submodules}")
    lfs = [line for line in git("check-attr", "--cached", "filter", "--", *paths).splitlines()
           if line.endswith(": filter: lfs")] if paths else []
    if lfs:
        fail(f"Git LFS files are not accepted: {lfs[:5]}")
    artifacts = [path for path in paths if path.lower().endswith(ARTIFACT_SUFFIXES)]
    if artifacts:
        fail(f"committed build artifacts are not accepted: {artifacts[:10]}")
    size = sum((REPO / path).stat().st_size for path in paths
               if path not in symlinks and (REPO / path).is_file())
    if size > 500 << 20:
        fail(f"tracked files total {size / 2**20:.1f} MiB, over Palomar's 500 MiB limit")
    if not (submodules or lfs or artifacts) and size <= 500 << 20:
        ok(f"{len(paths)} tracked files, {size / 2**20:.1f} MiB; no submodules, Git LFS files "
           "or build artifacts")


def check_challenge(config: dict) -> None:
    module = config.get("challenge_module")
    if not isinstance(module, str) or not module_path(module).is_file():
        return
    path = module_path(module)
    text = path.read_text(encoding="utf-8")
    size, lines = len(text.encode("utf-8")), text.count("\n") + (not text.endswith("\n"))
    if size > CHALLENGE_HARD[0] or lines > CHALLENGE_HARD[1]:
        fail(f"{path.name}: {size} bytes, {lines} lines exceeds Palomar's hard limit")
    elif size > CHALLENGE_SOFT[0] or lines > CHALLENGE_SOFT[1]:
        warn(f"{path.name}: {size} bytes, {lines} lines draws Palomar's size warning")
    else:
        ok(f"{path.relative_to(REPO)}: {size} bytes, {lines} lines (inline display needs <= 100 lines)")
    imports = re.findall(r"^import\s+(\S+)", text, re.M)
    if not imports or any(not re.fullmatch(r"Mathlib(\.[A-Za-z0-9_.]+)?", name) for name in imports):
        fail(f"{path.name} must import Mathlib only, imports {imports}")
    else:
        ok(f"{path.name} imports {imports} only")
    holes = len(re.findall(r"(?<![\w.'])sorry(?![\w'])", text))
    if holes != 1:
        fail(f"{path.name} must state its theorem with exactly one statement hole, found {holes}")


def check_metadata(schema_dir: Path | None, palomar_dir: Path | None) -> None:
    try:
        import yaml
    except ImportError:
        fail("PyYAML is required to check formalization.yaml (pip install pyyaml)")
        return

    class UniqueKeyLoader(yaml.SafeLoader):
        pass

    def construct_mapping(loader, node, deep=False):
        seen = set()
        for key_node, _ in node.value:
            key = loader.construct_object(key_node, deep=deep)
            if key in seen:
                raise yaml.constructor.ConstructorError(None, None, f"duplicate key {key!r}",
                                                        key_node.start_mark)
            seen.add(key)
        return loader.construct_mapping(node, deep=deep)

    UniqueKeyLoader.add_constructor(yaml.resolver.BaseResolver.DEFAULT_MAPPING_TAG,
                                    construct_mapping)
    start = len(failures)
    path = REPO / "formalization.yaml"
    if not path.is_file():
        fail("formalization.yaml is missing")
        return
    if path.stat().st_size > 256 * 1024:
        fail("formalization.yaml exceeds 256 KiB")
    try:
        data = yaml.load(path.read_text(encoding="utf-8"), Loader=UniqueKeyLoader)
    except yaml.YAMLError as error:
        fail(f"formalization.yaml is not valid YAML: {error}")
        return
    if not isinstance(data, dict):
        fail("formalization.yaml must contain one top-level mapping")
        return
    if data.get("version") != "v0.4":
        fail(f"formalization.yaml version must be v0.4, not {data.get('version')!r}")

    def sentinels(value, where="$"):
        if isinstance(value, dict):
            return [s for key, child in value.items() for s in sentinels(child, f"{where}.{key}")]
        if isinstance(value, list):
            return [s for i, child in enumerate(value) for s in sentinels(child, f"{where}[{i}]")]
        return [where] if isinstance(value, str) and SENTINEL_RE.match(value.lstrip()) else []

    if retained := sentinels(data):
        fail(f"formalization.yaml retains TEMPLATE values at {retained}")
    project = data.get("project") or {}
    if project.get("license") != "Apache-2.0":
        fail(f"formalization.yaml project.license must be Apache-2.0, not {project.get('license')!r}")
    description = project.get("description")
    if not isinstance(description, str) or not description.strip() or len(description) > 10_000:
        fail("formalization.yaml project.description must be nonempty text of at most 10000 characters")
    if len(failures) == start:
        ok("formalization.yaml parses, declares v0.4 and Apache-2.0, and retains no TEMPLATE values")

    if schema_dir is not None:
        try:
            import jsonschema
        except ImportError:
            fail("jsonschema is required for --formalization-schema (pip install jsonschema)")
        else:
            schema = json.loads((schema_dir / "schema" / "v0.4.schema.json").read_text(encoding="utf-8"))
            errors = sorted(jsonschema.Draft7Validator(schema).iter_errors(data),
                            key=lambda e: list(e.absolute_path))
            for error in errors:
                fail(f"formalization.yaml schema: {'/'.join(map(str, error.absolute_path))}: {error.message}")
            if not errors:
                ok(f"formalization.yaml validates against the upstream v0.4 schema "
                   f"({_revision(schema_dir)})")

    if palomar_dir is not None:
        sys.path.insert(0, str(palomar_dir))
        try:
            from scripts.submission_contract import load_formalization_metadata
            from scripts.verification_errors import VerificationError
        except ImportError as error:
            fail(f"cannot import Palomar's validator from {palomar_dir}: {error}")
            return
        try:
            load_formalization_metadata(path)
        except VerificationError as error:
            detail = getattr(error, "issues", None) or [error]
            for issue in detail:
                fail(f"formalization.yaml (Palomar intake): {issue}")
        else:
            ok(f"formalization.yaml passes Palomar's intake validator and taxonomies "
               f"({_revision(palomar_dir)})")


def _revision(directory: Path) -> str:
    try:
        return subprocess.run(["git", "-C", str(directory), "rev-parse", "HEAD"], check=True,
                              capture_output=True, text=True).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        return "revision unknown"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--palomar-submission", type=Path,
                        help="checkout of PalomarRegistry/PalomarSubmission: validate formalization.yaml "
                             "with Palomar's own intake code and read its toolchain minimum")
    parser.add_argument("--formalization-schema", type=Path,
                        help="checkout of mathlib-initiative/formalization.yaml: validate against its v0.4 schema")
    parser.add_argument("--offline", action="store_true",
                        help="do not fetch Mathlib's lean-toolchain over the network")
    args = parser.parse_args()

    minimum = DEFAULT_TOOLCHAIN_MINIMUM
    if args.palomar_submission is not None:
        minimum = json.loads((args.palomar_submission / "toolchains.json").read_text())["minimum"]
    config = check_comparator()
    check_toolchain(minimum, args.offline)
    check_manifest()
    check_packaging()
    check_challenge(config)
    check_metadata(args.formalization_schema, args.palomar_submission)
    print(f"\n{len(failures)} failure(s), {len(warnings)} warning(s)")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
