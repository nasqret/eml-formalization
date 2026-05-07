#!/usr/bin/env bash
# Build the GhostDay 2026 unified presentation.
#
# Usage:
#   ./build.sh         # static HTML in build/
#   ./build.sh pdf     # PDF (one slide per page) in build/ghostday.pdf
#   ./build.sh pptx    # PowerPoint version (transport format)
#   ./build.sh serve   # live-reload server on http://localhost:1948
#   ./build.sh all     # html + pdf + pptx

set -euo pipefail

cd "$(dirname "$0")"

CHROME_BIN_DEFAULT="/Applications/Google Chrome.app/Contents/MacOS/Google Chrome"
CHROME_BIN="${CHROME_BIN:-$CHROME_BIN_DEFAULT}"

build_html() {
  rm -rf build/html
  mkdir -p build
  npx -y reveal-md ghostday.md \
    --static build/html \
    --static-dirs=assets \
    --theme simple \
    --css assets/theme.css \
    --highlight-theme atom-one-light
  if [ ! -d build/html/assets ]; then
    cp -r assets build/html/assets
  fi
  cp -f build/html/ghostday.html build/html/index.html 2>/dev/null || true
  echo "==> built build/html/index.html"
}

build_pdf() {
  build_html
  local PORT=18949
  local URL="http://localhost:${PORT}/ghostday.html?print-pdf"
  npx -y http-server build/html -p $PORT -c-1 -s >/tmp/ghostday-http.log 2>&1 &
  local HTTP_PID=$!
  trap "kill $HTTP_PID 2>/dev/null" EXIT
  sleep 2
  rm -f build/ghostday.pdf
  "$CHROME_BIN" \
    --headless=new \
    --disable-gpu \
    --no-sandbox \
    --hide-scrollbars \
    --virtual-time-budget=20000 \
    --run-all-compositor-stages-before-draw \
    --no-pdf-header-footer \
    --print-to-pdf-no-header \
    --print-to-pdf=build/ghostday.pdf \
    "${URL}" >/dev/null 2>&1
  kill $HTTP_PID 2>/dev/null || true
  trap - EXIT
  echo "==> built build/ghostday.pdf"
}

build_pptx() {
  # PPTX export via pandoc. Reference doc + reveal-md markdown.
  # Note: SVG diagrams won't translate live — pandoc will rasterize image
  # references; we'd need to pre-rasterize SVG → PNG for the cleanest result.
  rm -f build/ghostday.pptx

  # Quick rasterize of all SVG to PNG so they embed in PPTX
  mkdir -p build/png
  for svg in assets/*.svg; do
    base=$(basename "$svg" .svg)
    if command -v rsvg-convert >/dev/null 2>&1; then
      rsvg-convert -w 1600 "$svg" -o "build/png/$base.png"
    elif command -v inkscape >/dev/null 2>&1; then
      inkscape "$svg" --export-type=png --export-dpi=200 --export-filename="build/png/$base.png" 2>/dev/null
    elif command -v "$CHROME_BIN" >/dev/null 2>&1; then
      # Fallback: use chrome headless
      "$CHROME_BIN" --headless --disable-gpu --window-size=1600,1000 --screenshot="build/png/$base.png" "file://$(pwd)/$svg" 2>/dev/null || true
    fi
  done

  # Make a copy of the markdown with SVG paths replaced by PNG paths
  sed 's|assets/\([^"]*\)\.svg|build/png/\1.png|g' ghostday.md > build/ghostday_pptx.md

  pandoc build/ghostday_pptx.md \
    -o build/ghostday.pptx \
    --slide-level=2 \
    --resource-path=. 2>&1 | tail -3
  echo "==> built build/ghostday.pptx"
}

case "${1:-html}" in
  html) build_html ;;
  pdf)  build_pdf ;;
  pptx) build_pptx ;;
  all)  build_html; build_pdf; build_pptx ;;
  serve)
    npx -y reveal-md ghostday.md \
      --watch \
      --theme simple \
      --css assets/theme.css \
      --highlight-theme atom-one-light \
      --port 1948
    ;;
  *) echo "usage: $0 {html|pdf|pptx|serve|all}"; exit 1 ;;
esac
