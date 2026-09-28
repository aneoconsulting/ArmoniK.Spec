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
#   .tlatools/tlapm-opt/                 prebuilt tlapm fork with the
#                                          instantiation/preparation optimizations
#                                          (same layout, ~1.6 GB unpacked)
#   .tlatools/VERSIONS                   resolved versions of the above
#
# It also renders .vscode/settings.json from .vscode/settings.json.template,
# substituting this repo's absolute path for the __REPO_ROOT__ token (the TLA+
# extension's moduleSearchPaths require absolute paths). The generated file is
# gitignored; edit the template, not the generated file.
#
# Linux-only. tlapm_lsp (used by the tlaplus.vscode-ide extension) ships in
# the prebuilt tarball, so opam / a local switch are not needed.
#
# The optimized tlapm is a separate build of the same prover, kept alongside the
# upstream one rather than replacing it: the proof modules too large for one
# upstream run are checked whole by it, and by line range with the upstream
# prover (scripts/chunk_proofs.py). It is a 826 MB download, hence the flags to
# install it -- or everything else -- alone.
#
# Flags:
#   --check            verify presence + runnability without re-downloading
#   --no-tlapm-opt     leave out the optimized tlapm (skips the 826 MB download)
#   --only-tlapm-opt   install the optimized tlapm and nothing else
#   --help

set -euo pipefail

# ----- pinned versions (bump to update) ---------------------------------------
TLA2TOOLS_VERSION="1.8.0"
COMMUNITY_MODULES_REF="202604221529"   # CommunityModules release tag
TLAPM_RELEASE_TAG="1.6.0-pre"          # prebuilt tarball tag
TLAPM_OPT_REPO="qdelamea-aneo/tlapm"   # fork carrying the performance patches
TLAPM_OPT_RELEASE_TAG="v1.6.0-instopt.2"
# ------------------------------------------------------------------------------

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TOOLS_DIR="${REPO_ROOT}/.tlatools"
TLAPM_DIR="${TOOLS_DIR}/tlapm"
TLAPM_OPT_DIR="${TOOLS_DIR}/tlapm-opt"
VSCODE_TEMPLATE="${REPO_ROOT}/.vscode/settings.json.template"
VSCODE_SETTINGS="${REPO_ROOT}/.vscode/settings.json"

MODE="install"
WANT_BASE=1       # tla2tools, CommunityModules, upstream tlapm, .vscode/settings.json
WANT_TLAPM_OPT=1  # the optimized tlapm fork
for arg in "$@"; do
    case "$arg" in
        --check) MODE="check" ;;
        --no-tlapm-opt) WANT_TLAPM_OPT=0 ;;
        --only-tlapm-opt) WANT_BASE=0 ;;
        -h|--help)
            sed -n '2,35p' "$0" | sed 's/^# \{0,1\}//'
            exit 0 ;;
        *)
            echo "error: unknown flag '$arg' (try --help)" >&2
            exit 2 ;;
    esac
done

(( WANT_BASE || WANT_TLAPM_OPT )) || { echo "error: --no-tlapm-opt and --only-tlapm-opt leave nothing to do" >&2; exit 2; }

log()  { printf '\033[1;34m::\033[0m %s\n' "$*"; }
die()  { printf '\033[1;31mxx\033[0m %s\n' "$*" >&2; exit 1; }

# Render .vscode/settings.json from the template, substituting the repo's
# absolute path for __REPO_ROOT__ (the TLA+ extension needs absolute paths).
render_vscode_settings() {
    [[ -f "${VSCODE_TEMPLATE}" ]] || die "missing ${VSCODE_TEMPLATE}"
    sed "s|__REPO_ROOT__|${REPO_ROOT}|g" "${VSCODE_TEMPLATE}" > "${VSCODE_SETTINGS}"
}

# ----- platform & dependency checks -------------------------------------------
[[ "$(uname -s)" == "Linux" ]] || die "this repo's tlapm setup is Linux-only (WSL is fine)."

need() {
    command -v "$1" >/dev/null 2>&1 || die "$1 not found in PATH — $2"
}

need curl  "install curl"
need tar   "install tar"

# Java runs SANY, TLC and the specs/*.java overrides; tlapm itself is a native
# binary, so an --only-tlapm-opt install needs no JDK at all.
if (( WANT_BASE )); then
    need java  "install a JDK >= 17 (e.g. 'sudo apt install default-jdk')"
    need javac "install a JDK >= 17 (you have a JRE without javac); needed to build specs/DDGraphs.java"
    need git   "install git"
    JAVA_MAJOR="$(java -version 2>&1 | awk -F[\".] '/version/ {print $2; exit}')"
    [[ "${JAVA_MAJOR:-0}" -ge 17 ]] || die "JDK >= 17 required (found ${JAVA_MAJOR:-?}); update java/javac."
fi

# ----- check mode -------------------------------------------------------------
if [[ "$MODE" == "check" ]]; then
    log "checking existing install in ${TOOLS_DIR}"
    if (( WANT_BASE )); then
        [[ -f "${TOOLS_DIR}/tla2tools.jar" ]]             || die "missing tla2tools.jar"
        [[ -f "${TOOLS_DIR}/CommunityModules-deps.jar" ]] || die "missing CommunityModules-deps.jar"
        [[ -d "${TOOLS_DIR}/CommunityModules/modules" ]]  || die "missing CommunityModules sources"
        [[ -x "${TLAPM_DIR}/bin/tlapm" ]]                 || die "missing prebuilt tlapm binary"
        [[ -x "${TLAPM_DIR}/bin/tlapm_lsp" ]]             || die "missing prebuilt tlapm_lsp binary"
        "${TLAPM_DIR}/bin/tlapm" --version >/dev/null     || die "tlapm does not run"
        "${TLAPM_DIR}/bin/tlapm_lsp" --help >/dev/null    || die "tlapm_lsp does not run"
        [[ -f "${VSCODE_SETTINGS}" ]]                     || die "missing .vscode/settings.json (run 'make install' to render it)"
        grep -q '__REPO_ROOT__' "${VSCODE_SETTINGS}" \
            && die ".vscode/settings.json still has unresolved __REPO_ROOT__ tokens (re-run 'make install')"
    fi
    if (( WANT_TLAPM_OPT )); then
        [[ -x "${TLAPM_OPT_DIR}/bin/tlapm" ]]             || die "missing optimized tlapm binary (run 'make install-tlapm-opt')"
        "${TLAPM_OPT_DIR}/bin/tlapm" --version >/dev/null || die "optimized tlapm does not run"
    fi
    log "ok — install is healthy"
    exit 0
fi

mkdir -p "${TOOLS_DIR}"

if (( WANT_BASE )); then

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

# ----- VSCode settings --------------------------------------------------------
log "rendering .vscode/settings.json from template (REPO_ROOT=${REPO_ROOT})"
render_vscode_settings

fi  # WANT_BASE

# ----- optimized tlapm --------------------------------------------------------
# The same layout as the upstream tarball (top-level "tlapm/"), unpacked next to
# it under tlapm-opt/ so that both provers stay available side by side.
if (( WANT_TLAPM_OPT )); then
    log "downloading optimized tlapm ${TLAPM_OPT_RELEASE_TAG} from ${TLAPM_OPT_REPO} (826 MB)"
    TLAPM_OPT_VERSION="${TLAPM_OPT_RELEASE_TAG#v}"
    TLAPM_OPT_TARBALL="${TOOLS_DIR}/.tlapm-opt-${TLAPM_OPT_RELEASE_TAG}.tar.gz"
    curl -fL --retry 3 -o "${TLAPM_OPT_TARBALL}" \
        "https://github.com/${TLAPM_OPT_REPO}/releases/download/${TLAPM_OPT_RELEASE_TAG}/tlapm-${TLAPM_OPT_VERSION}-x86_64-linux-gnu.tar.gz"
    rm -rf "${TLAPM_OPT_DIR}" "${TOOLS_DIR}/.tlapm-opt-unpack"
    mkdir -p "${TOOLS_DIR}/.tlapm-opt-unpack"
    tar -xzf "${TLAPM_OPT_TARBALL}" -C "${TOOLS_DIR}/.tlapm-opt-unpack"
    mv "${TOOLS_DIR}/.tlapm-opt-unpack/tlapm" "${TLAPM_OPT_DIR}"
    rm -rf "${TLAPM_OPT_TARBALL}" "${TOOLS_DIR}/.tlapm-opt-unpack"
    [[ -x "${TLAPM_OPT_DIR}/bin/tlapm" ]] || die "optimized tlapm tarball didn't produce ${TLAPM_OPT_DIR}/bin/tlapm"
    "${TLAPM_OPT_DIR}/bin/tlapm" --version >/dev/null || die "optimized tlapm doesn't run"
fi

# ----- VERSIONS lockfile ------------------------------------------------------
# Written from what the tree actually holds, so that a partial install
# (--only-tlapm-opt) describes the whole of .tlatools rather than itself.
{
    if [[ -d "${TOOLS_DIR}/CommunityModules" ]]; then
        echo "TLA2TOOLS_VERSION=${TLA2TOOLS_VERSION}"
        echo "COMMUNITY_MODULES_REF=${COMMUNITY_MODULES_REF} ($(git -C "${TOOLS_DIR}/CommunityModules" rev-parse --short HEAD))"
    fi
    if [[ -x "${TLAPM_DIR}/bin/tlapm" ]]; then
        echo "TLAPM_RELEASE_TAG=${TLAPM_RELEASE_TAG}"
        echo "TLAPM_PREBUILT_VERSION=$("${TLAPM_DIR}/bin/tlapm" --version 2>/dev/null | head -1)"
    fi
    if [[ -x "${TLAPM_OPT_DIR}/bin/tlapm" ]]; then
        echo "TLAPM_OPT_RELEASE_TAG=${TLAPM_OPT_RELEASE_TAG} (${TLAPM_OPT_REPO})"
        echo "TLAPM_OPT_VERSION=$("${TLAPM_OPT_DIR}/bin/tlapm" --version 2>/dev/null | head -1)"
    fi
    echo "INSTALLED_AT=$(date -u +%Y-%m-%dT%H:%M:%SZ)"
} > "${TOOLS_DIR}/VERSIONS"

log "done. summary:"
sed 's/^/    /' "${TOOLS_DIR}/VERSIONS"
