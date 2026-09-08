#!/usr/bin/env bash
set -euo pipefail

# Independent aarch64 rebuild and endpoint audit for saasom/Erdos1144 v1.0.0.
#
# A fresh run needs roughly 12 GiB for the source tree, dependency cache, and
# project build.  Override ERDOS1144_VERIFY_ROOT to retain or reuse a specific
# work directory.  Override ERDOS1144_LEANTAR if the Lean v4.33.0 toolchain is
# not installed; the supplied binary must be an aarch64 build of leantar.

readonly claim_repo="https://github.com/saasom/Erdos1144.git"
readonly claim_tag="v1.0.0"
readonly claim_commit="a0050daf4bf4992355b5ab189ee9c75cd44795a3"
readonly mathlib_commit="5450b53e5ddc75d46418fabb605edbf36bd0beb6"
readonly lean_version="4.30.0-rc2"
readonly lean_archive="lean-${lean_version}-linux_aarch64.tar.zst"
readonly lean_url="https://github.com/leanprover/lean4/releases/download/v${lean_version}/${lean_archive}"

if [[ "$(uname -m)" != "aarch64" ]]; then
  echo "This verification script is the aarch64 reproduction; host is $(uname -m)." >&2
  exit 1
fi

verify_root="${ERDOS1144_VERIFY_ROOT:-$(mktemp -d "${TMPDIR:-/tmp}/erdos1144-verify.XXXXXX")}"
source_dir="${verify_root}/Erdos1144"
toolchain_dir="${ERDOS1144_TOOLCHAIN:-${verify_root}/lean-v${lean_version}-aarch64}"
overlay_bin="${verify_root}/bin"
audit_file="${verify_root}/axiom-audit.txt"

mkdir -p "${verify_root}" "${overlay_bin}"

if [[ ! -d "${source_dir}/.git" ]]; then
  git clone --branch "${claim_tag}" --depth 1 "${claim_repo}" "${source_dir}"
fi

actual_claim_commit="$(git -C "${source_dir}" rev-parse HEAD)"
if [[ "${actual_claim_commit}" != "${claim_commit}" ]]; then
  echo "Unexpected claim commit: ${actual_claim_commit}" >&2
  exit 1
fi
actual_claim_tag="$(git -C "${source_dir}" describe --tags --exact-match HEAD)"
if [[ "${actual_claim_tag}" != "${claim_tag}" ]]; then
  echo "Unexpected claim tag: ${actual_claim_tag}" >&2
  exit 1
fi
if [[ -n "$(git -C "${source_dir}" status --short)" ]]; then
  echo "Claim checkout has local changes; refusing a non-pristine rebuild." >&2
  exit 1
fi

if [[ ! -x "${toolchain_dir}/bin/lean" ]]; then
  archive_path="${verify_root}/${lean_archive}"
  extracted_dir="${verify_root}/lean-${lean_version}-linux"
  curl --fail --location --retry 3 --output "${archive_path}" "${lean_url}"
  tar --zstd --extract --file "${archive_path}" --directory "${verify_root}"
  mv "${extracted_dir}" "${toolchain_dir}"
  rm "${archive_path}"
fi

if [[ -n "${ERDOS1144_LEANTAR:-}" ]]; then
  leantar_source="${ERDOS1144_LEANTAR}"
else
  elan_root="${ELAN_HOME:-${HOME}/.elan}"
  leantar_source="${elan_root}/toolchains/leanprover--lean4---v4.33.0/bin/leantar"
fi

if [[ ! -x "${leantar_source}" ]]; then
  echo "Set ERDOS1144_LEANTAR to an executable aarch64 leantar binary." >&2
  exit 1
fi
if [[ "$(file -b "${leantar_source}")" != *"ARM aarch64"* ]]; then
  echo "leantar is not an aarch64 binary: ${leantar_source}" >&2
  exit 1
fi
if [[ ! -e "${overlay_bin}/leantar" ]]; then
  ln -s "${leantar_source}" "${overlay_bin}/leantar"
fi

export PATH="${overlay_bin}:${toolchain_dir}/bin:${PATH}"

"${toolchain_dir}/bin/lean" --version
"${overlay_bin}/leantar" --version

cd "${source_dir}"
sha256sum --check verification/source-snapshot.sha256
"${toolchain_dir}/bin/lake" exe cache get

actual_mathlib_commit="$(git -C .lake/packages/mathlib rev-parse HEAD)"
if [[ "${actual_mathlib_commit}" != "${mathlib_commit}" ]]; then
  echo "Unexpected Mathlib commit: ${actual_mathlib_commit}" >&2
  exit 1
fi

"${toolchain_dir}/bin/lake" build
"${toolchain_dir}/bin/lake" env lean Audit.lean | tee "${audit_file}"
python3 scripts/check_axioms.py "${audit_file}"

echo "Verified ${claim_tag} (${claim_commit}) on aarch64; audit: ${audit_file}"

# Commands used for the resumed rd1 run on 2026-09-08, after the interrupted
# run had cloned the tag, downloaded the toolchain/cache, and left no project
# .lake/build directory:
#
#   ERDOS1144_VERIFY_ROOT=/tmp/erdos1144-rd1.MyX60s
#   ln -s /home/nvidia/.elan/toolchains/leanprover--lean4---v4.33.0/bin/leantar \
#     /tmp/erdos1144-rd1.MyX60s/bin/leantar
#   cd /tmp/erdos1144-rd1.MyX60s/Erdos1144
#   git rev-parse HEAD
#   git describe --tags --exact-match HEAD
#   git status --short
#   sha256sum --check verification/source-snapshot.sha256
#   /tmp/erdos1144-rd1.MyX60s/lean-v4.30.0-rc2-aarch64/bin/lean --version
#   /tmp/erdos1144-rd1.MyX60s/bin/leantar --version
#   env PATH=/tmp/erdos1144-rd1.MyX60s/bin:/tmp/erdos1144-rd1.MyX60s/lean-v4.30.0-rc2-aarch64/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin \
#     /tmp/erdos1144-rd1.MyX60s/lean-v4.30.0-rc2-aarch64/bin/lake exe cache get
#   git -C .lake/packages/mathlib rev-parse HEAD
#   env PATH=/tmp/erdos1144-rd1.MyX60s/bin:/tmp/erdos1144-rd1.MyX60s/lean-v4.30.0-rc2-aarch64/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin \
#     /tmp/erdos1144-rd1.MyX60s/lean-v4.30.0-rc2-aarch64/bin/lake build
#   env PATH=/tmp/erdos1144-rd1.MyX60s/bin:/tmp/erdos1144-rd1.MyX60s/lean-v4.30.0-rc2-aarch64/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin \
#     /tmp/erdos1144-rd1.MyX60s/lean-v4.30.0-rc2-aarch64/bin/lake env lean Audit.lean \
#     > /tmp/erdos1144-rd1.MyX60s/axiom-audit.txt
#   python3 scripts/check_axioms.py /tmp/erdos1144-rd1.MyX60s/axiom-audit.txt
