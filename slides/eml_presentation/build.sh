#!/usr/bin/env bash
# Build the EML auto-formalization presentation.
#
# Usage:
#   ./build.sh         # static HTML in build/
#   ./build.sh pdf     # PDF (one slide per page) in eml_presentation.pdf
#   ./build.sh serve   # live-reload server on http://localhost:1948
#   ./build.sh all     # html + pdf
#
# The PDF target uses headless Chrome with reveal.js's `?print-pdf` mode,
# which is the only reliable way to get exactly one slide per PDF page.
# `reveal-md --print` (the built-in mode) frequently splits tall slides.

set -euo pipefail

cd "$(dirname "$0")"

CHROME_BIN_DEFAULT="/Applications/Google Chrome.app/Contents/MacOS/Google Chrome"
CHROME_BIN="${CHROME_BIN:-$CHROME_BIN_DEFAULT}"

build_html() {
  rm -rf build
  npx -y reveal-md eml_presentation.md \
    --static build \
    --static-dirs=assets \
    --theme simple \
    --css assets/theme.css \
    --highlight-theme atom-one-light
  # mirror assets in case --static-dirs is ignored
  if [ ! -d build/assets ]; then
    cp -R assets build/assets
  fi
  # reveal-md drops the user CSS *file* into build/_assets/<basename>.
  # Make sure build/index.html (or eml_presentation.html) really points
  # at the right css file. The default emit usually does, but be safe.
  echo "==> built build/index.html"
}

build_pdf() {
  build_html

  # Pick a port unlikely to clash.
  local port=18948
  local url="http://localhost:${port}/eml_presentation.html?print-pdf"

  # Serve the static build directory.
  npx -y http-server build -p "${port}" -s >/dev/null 2>&1 &
  local pid=$!
  trap "kill ${pid} 2>/dev/null || true" EXIT
  sleep 2

  if [ ! -x "$CHROME_BIN" ]; then
    echo "Chrome binary not found at ${CHROME_BIN}; set CHROME_BIN env var." >&2
    kill ${pid} || true
    exit 2
  fi

  rm -f eml_presentation.pdf
  "$CHROME_BIN" \
    --headless=new \
    --disable-gpu \
    --no-sandbox \
    --hide-scrollbars \
    --virtual-time-budget=20000 \
    --run-all-compositor-stages-before-draw \
    --no-pdf-header-footer \
    --print-to-pdf-no-header \
    --print-to-pdf=eml_presentation.pdf \
    "${url}" >/dev/null 2>&1

  kill ${pid} 2>/dev/null || true
  trap - EXIT
  echo "==> built eml_presentation.pdf"
}

case "${1:-html}" in
  html)
    build_html
    ;;
  pdf)
    build_pdf
    ;;
  all)
    build_pdf
    ;;
  serve)
    npx -y reveal-md eml_presentation.md \
      --theme simple \
      --css assets/theme.css \
      --highlight-theme atom-one-light
    ;;
  *)
    echo "unknown target: $1" >&2
    exit 2
    ;;
esac
