#!/bin/sh
# Download SMT-LIB benchmarks from the SMT-LIB releases on Zenodo
# (https://smt-lib.org/benchmarks.shtml, https://zenodo.org/communities/smt-lib).
# The git repositories on clc-gitlab.cs.uiowa.edu that this script used to
# clone are no longer available.
#
# Usage: scripts/SMT-LIB-clone.sh LOGIC...
#   Downloads the non-incremental benchmarks of each LOGIC (e.g. QF_LIA)
#   to non-incremental/LOGIC/ in the current directory.
#   Without arguments, lists the logics of the release.
#
# Environment variables:
#   INCREMENTAL=1   download the incremental benchmarks instead, to
#                   incremental/LOGIC/
#   RELEASE=2024    use another release (2023, 2024 or 2025, default 2025)
#   RECORD=<id>     use another Zenodo record, e.g. a newer release
#
# Requires curl, tar and zstd.

set -e

RELEASE=${RELEASE:-2025}
if [ -z "$RECORD" ]; then
    case "$RELEASE-${INCREMENTAL:-0}" in
        2025-0) RECORD=16740866 ;;
        2025-1) RECORD=15493096 ;;
        2024-0) RECORD=11061097 ;;
        2024-1) RECORD=11186591 ;;
        2023-0) RECORD=10607722 ;;
        2023-1) RECORD=10607775 ;;
        *)
            echo "error: unknown release $RELEASE, set RECORD to the" \
                 "Zenodo record of the release" >&2
            exit 1 ;;
    esac
fi

for tool in curl tar zstd; do
    if ! command -v $tool > /dev/null 2>&1; then
        echo "error: $tool is required" >&2
        exit 1
    fi
done

if [ $# -eq 0 ]; then
    echo "usage: $0 LOGIC..."
    echo "logics in Zenodo record $RECORD:"
    curl -fsSL "https://zenodo.org/api/records/$RECORD" \
        | grep -o '"key": *"[^"]*\.tar\.zst"' \
        | sed 's/.*"\([^"]*\)\.tar\.zst"/\1/' | sort | tr '\n' ' '
    echo
    exit 0
fi

archive=$(mktemp)
trap 'rm -f "$archive"' EXIT
for logic in "$@"; do
    echo "Downloading $logic (Zenodo record $RECORD)"
    if ! curl -fSL -o "$archive" \
            "https://zenodo.org/records/$RECORD/files/$logic.tar.zst?download=1"
    then
        echo "error: cannot download $logic, run $0 without arguments" \
             "for the list of logics" >&2
        exit 1
    fi
    zstd -dc "$archive" | tar -x
done
