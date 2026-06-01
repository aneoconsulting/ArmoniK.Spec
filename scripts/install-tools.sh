#!/usr/bin/env bash
#
# Installs / updates the TLA+ toolchain into ./.tlatools.
#
# What gets installed:
#   .tlatools/tla2tools.jar              TLC / SANY / PCal
#   .tlatools/CommunityModules-deps.jar  TLC operator overrides (jar)
#   .tlatools/CommunityModules/          CommunityModules sources (for tlapm -I)
#   .tlatools/tlapm/                     prebuilt tlapm release
#                                          bin/{tlapm,tlapm_lsp,translate}
#                                          lib/tlapm/stdlib/{TLAPS.tla,...}
#   .tlatools/VERSIONS                   resolved versions of the above
#
# Linux-only. tlapm_lsp (used by the tlaplus.vscode-ide extension) ships in
# the prebuilt tarball, so opam / a local switch are not needed.
#
# Flags:
#   --check   verify presence + runnability without re-downloading
#   --help

set -euo pipefail

# ----- pinned versions (bump to update) ---------------------------------------
TLA2TOOLS_VERSION="1.8.0"
COMMUNITY_MODULES_REF="202604221529"   # CommunityModules release tag
TLAPM_RELEASE_TAG="1.6.0-pre"          # prebuilt tarball tag
# ------------------------------------------------------------------------------

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TOOLS_DIR="${REPO_ROOT}/.tlatools"
TLAPM_DIR="${TOOLS_DIR}/tlapm"

MODE="install"
for arg in "$@"; do
    case "$arg" in
        --check) MODE="check" ;;
        -h|--help)
            sed -n '2,20p' "$0" | sed 's/^# \{0,1\}//'
            exit 0 ;;
        *)
            echo "error: unknown flag '$arg' (try --help)" >&2
            exit 2 ;;
    esac
done

log()  { printf '\033[1;34m::\033[0m %s\n' "$*"; }
die()  { printf '\033[1;31mxx\033[0m %s\n' "$*" >&2; exit 1; }

# ----- platform & dependency checks -------------------------------------------
[[ "$(uname -s)" == "Linux" ]] || die "this repo's tlapm setup is Linux-only (WSL is fine)."

need() {
    command -v "$1" >/dev/null 2>&1 || die "$1 not found in PATH — $2"
}

need java  "install a JDK >= 17 (e.g. 'sudo apt install default-jdk')"
need javac "install a JDK >= 17 (you have a JRE without javac); needed to build specs/DDGraphs.java"
need curl  "install curl"
need git   "install git"
need tar   "install tar"

JAVA_MAJOR="$(java -version 2>&1 | awk -F[\".] '/version/ {print $2; exit}')"
[[ "${JAVA_MAJOR:-0}" -ge 17 ]] || die "JDK >= 17 required (found ${JAVA_MAJOR:-?}); update java/javac."

# ----- check mode -------------------------------------------------------------
if [[ "$MODE" == "check" ]]; then
    log "checking existing install in ${TOOLS_DIR}"
    [[ -f "${TOOLS_DIR}/tla2tools.jar" ]]             || die "missing tla2tools.jar"
    [[ -f "${TOOLS_DIR}/CommunityModules-deps.jar" ]] || die "missing CommunityModules-deps.jar"
    [[ -d "${TOOLS_DIR}/CommunityModules/modules" ]]  || die "missing CommunityModules sources"
    [[ -x "${TLAPM_DIR}/bin/tlapm" ]]                 || die "missing prebuilt tlapm binary"
    [[ -x "${TLAPM_DIR}/bin/tlapm_lsp" ]]             || die "missing prebuilt tlapm_lsp binary"
    "${TLAPM_DIR}/bin/tlapm" --version >/dev/null     || die "tlapm does not run"
    "${TLAPM_DIR}/bin/tlapm_lsp" --help >/dev/null    || die "tlapm_lsp does not run"
    log "ok — install is healthy"
    exit 0
fi

mkdir -p "${TOOLS_DIR}"

# ----- tla2tools.jar ----------------------------------------------------------
log "downloading tla2tools.jar v${TLA2TOOLS_VERSION}"
curl -fL --retry 3 -o "${TOOLS_DIR}/tla2tools.jar" \
    "https://github.com/tlaplus/tlaplus/releases/download/v${TLA2TOOLS_VERSION}/tla2tools.jar"

# ----- CommunityModules-deps.jar ----------------------------------------------
log "downloading CommunityModules-deps.jar (${COMMUNITY_MODULES_REF})"
curl -fL --retry 3 -o "${TOOLS_DIR}/CommunityModules-deps.jar" \
    "https://github.com/tlaplus/CommunityModules/releases/download/${COMMUNITY_MODULES_REF}/CommunityModules-deps.jar"

# ----- CommunityModules sources (for tlapm -I) --------------------------------
CM_SRC="${TOOLS_DIR}/CommunityModules"
if [[ ! -d "${CM_SRC}/.git" ]]; then
    log "cloning CommunityModules sources"
    rm -rf "${CM_SRC}"
    git clone --quiet --depth 50 \
        https://github.com/tlaplus/CommunityModules.git "${CM_SRC}"
else
    log "updating CommunityModules sources"
    git -C "${CM_SRC}" fetch --quiet --depth 50 origin
fi
git -C "${CM_SRC}" -c advice.detachedHead=false checkout --quiet "${COMMUNITY_MODULES_REF}"

# ----- prebuilt tlapm ---------------------------------------------------------
log "downloading prebuilt tlapm ${TLAPM_RELEASE_TAG}"
TLAPM_TARBALL="${TOOLS_DIR}/.tlapm-${TLAPM_RELEASE_TAG}.tar.gz"
curl -fL --retry 3 -o "${TLAPM_TARBALL}" \
    "https://github.com/tlaplus/tlapm/releases/download/${TLAPM_RELEASE_TAG}/tlapm-${TLAPM_RELEASE_TAG}-x86_64-linux-gnu.tar.gz"
rm -rf "${TLAPM_DIR}"
tar -xzf "${TLAPM_TARBALL}" -C "${TOOLS_DIR}"     # tarball top-level dir is "tlapm/"
rm -f "${TLAPM_TARBALL}"
[[ -x "${TLAPM_DIR}/bin/tlapm" ]]     || die "tlapm tarball didn't produce ${TLAPM_DIR}/bin/tlapm"
[[ -x "${TLAPM_DIR}/bin/tlapm_lsp" ]] || die "tlapm tarball didn't produce ${TLAPM_DIR}/bin/tlapm_lsp"
"${TLAPM_DIR}/bin/tlapm" --version  >/dev/null || die "prebuilt tlapm doesn't run"
"${TLAPM_DIR}/bin/tlapm_lsp" --help >/dev/null || die "prebuilt tlapm_lsp doesn't run"

# ----- VERSIONS lockfile ------------------------------------------------------
{
    echo "TLA2TOOLS_VERSION=${TLA2TOOLS_VERSION}"
    echo "COMMUNITY_MODULES_REF=${COMMUNITY_MODULES_REF} ($(git -C "${CM_SRC}" rev-parse --short HEAD))"
    echo "TLAPM_RELEASE_TAG=${TLAPM_RELEASE_TAG}"
    echo "TLAPM_PREBUILT_VERSION=$("${TLAPM_DIR}/bin/tlapm" --version 2>/dev/null | head -1)"
    echo "INSTALLED_AT=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
} > "${TOOLS_DIR}/VERSIONS"

log "done. summary:"
sed 's/^/    /' "${TOOLS_DIR}/VERSIONS"
