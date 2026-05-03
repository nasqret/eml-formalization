#!/usr/bin/env bash
# Build the EML auto-formalization presentation.
#
# Usage:
#   ./build.sh         # static HTML in build/
#   ./build.sh pdf     # PDF in eml_presentation.pdf
#   ./build.sh serve   # live-reload server on http://localhost:1948

set -euo pipefail

cd "$(dirname "$0")"

case "${1:-html}" in
  html)
    rm -rf build
    npx -y reveal-md eml_presentation.md \
      --static build \
      --static-dirs=assets \
      --theme simple \
      --highlight-theme atom-one-light
    # Some reveal-md versions don't honour --static-dirs reliably;
    # mirror the assets directory in any case.
    if [ ! -d build/assets ]; then
      cp -R assets build/assets
    fi
    echo "==> built build/eml_presentation.html"
    ;;
  pdf)
    npx -y reveal-md eml_presentation.md \
      --print eml_presentation.pdf \
      --theme simple
    echo "==> built eml_presentation.pdf"
    ;;
  serve)
    npx -y reveal-md eml_presentation.md \
      --theme simple \
      --highlight-theme atom-one-light
    ;;
  *)
    echo "unknown target: $1" >&2
    exit 2
    ;;
esac
