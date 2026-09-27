#!/usr/bin/env bash
# Judge PalomarEDP.Solution against PalomarEDP.Challenge the way Palomar does: with the
# `lake comparator` that ships in this project's own toolchain, replaying the proof through
# Lean's kernel and the toolchain's bundled independent kernels (NanoDa and con-ron).
#
# Adapted from PalomarRegistry/PalomarTemplate scripts/verify-comparator.sh at commit
# cb5c79b69a740d2dc299071fc35994627050d77a (Apache-2.0). Changes: the tool versions are
# printed for the verification record, and the comparator exit code is reported explicitly.
#
# Requirements: Linux with bubblewrap (`bwrap`), which `lake comparator` uses to sandbox the
# build it judges, plus `lake`, `lean` and `python3` on PATH. The judge comes from
# `lean-toolchain`, which Palomar requires to be v4.35.0-rc2 or later. See docs/edp-release.md.
#
# This is a local rehearsal, not Palomar's verdict: Palomar builds the Solution from scratch
# under its own sandbox, and its reusable preflight workflow is the closest predictor.
set -euo pipefail

repository_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repository_root"

for required_command in bwrap lake lean python3; do
  if ! command -v "$required_command" >/dev/null 2>&1; then
    echo "error: $required_command is required to run lake comparator" >&2
    exit 1
  fi
done

toolchain=$(tr -d '[:space:]' < lean-toolchain)
prefix=$(lean --print-prefix)
for tool in lake leanexport leanchecker nanoda_bin con-ron; do
  if [ ! -x "$prefix/bin/$tool" ]; then
    echo "error: toolchain $toolchain does not bundle $tool" >&2
    echo "Palomar requires leanprover/lean4:v4.35.0-rc2 or later" >&2
    exit 1
  fi
done

echo "== verification environment"
echo "toolchain: $toolchain"
lean --version
lake --version
bwrap --version
echo "commit: $(git rev-parse HEAD 2>/dev/null || echo unknown)"

# Palomar ignores `enable_nanoda` and rejects `external_kernels` in a submitted
# comparator.json: it registers the toolchain's bundled kernels itself. This
# generated copy does the same, so the local check judges as the registry does.
config=$(mktemp "${TMPDIR:-/tmp}/palomar-comparator.XXXXXX")
trap 'rm -f "$config"' EXIT
python3 - comparator.json "$config" "$prefix" <<'PY'
import json
import pathlib
import sys

source, destination, prefix = sys.argv[1:]
try:
    config = json.loads(pathlib.Path(source).read_text(encoding="utf-8"))
except (OSError, UnicodeError, json.JSONDecodeError) as error:
    print(f"error: cannot read valid Comparator config {source}: {error}", file=sys.stderr)
    raise SystemExit(1)
if not isinstance(config, dict):
    print(f"error: {source} must contain one JSON object", file=sys.stderr)
    raise SystemExit(1)
if "external_kernels" in config:
    print(f"error: {source}: external_kernels is not a submitter field; Palomar rejects it", file=sys.stderr)
    raise SystemExit(1)
config.pop("enable_nanoda", None)
config["external_kernels"] = {
    "nanoda": [f"{prefix}/bin/nanoda_bin"],
    "con-ron": [f"{prefix}/bin/con-ron"],
}
pathlib.Path(destination).write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")
print("== comparator configuration (as judged)")
print(json.dumps(config, indent=2))
PY

lake exe cache get
status=0
lake comparator --config "$config" || status=$?
echo "== lake comparator exit code: $status (0 accepted, 1 rejected, 2 could not start)"
exit "$status"
