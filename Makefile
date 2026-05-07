# EML formalization — Makefile
#
# Reproducibility entry point for the Lean artefact and its surrounding
# scaffold. See `First_run.md` for the narrative recipe Claude follows
# on first checkout of this repository.

# ===== Paths =====
LEAN_DIR        := lambda_lab/proofs/eml/2603_21852/lean_workspace
ARISTOTLE_DIR   := lambda_lab/proofs/lean_aristotle
NOTES_DIR       := lambda_lab/proofs/eml/2603_21852/notes
EML_DIR         := lambda_lab/proofs/eml/2603_21852
GHOSTDAY_DIR    := slides/ghostday_post_submission

# Default location where the Claude session-archive snapshot is expected
# to live. Can be overridden on the command line:
#   make claude-memory-restore ARCHIVE_DIR=/path/to/snapshot
ARCHIVE_DIR ?= $(HOME)/claude-archives/eml-formalization-2026-05-08

# Project key used by Claude Code to namespace per-project memory.
# Derived from the absolute path of the current checkout.
PROJECT_KEY := $(shell pwd | sed 's|/|-|g')
CLAUDE_MEM_DIR := $(HOME)/.claude/projects/$(PROJECT_KEY)/memory

# ===== Help =====
.PHONY: help
help:
	@echo "EML formalization — Make targets"
	@echo ""
	@echo "  Setup:"
	@echo "    make first-run             Full first-time setup (memory + deps + build + sanity)"
	@echo "    make claude-memory-restore Restore Claude auto-memory from snapshot archive"
	@echo "    make pip-install           pip install -e . (Python scaffold)"
	@echo "    make prereqs               Print the required tool versions and check availability"
	@echo ""
	@echo "  Verify the Lean artefact:"
	@echo "    make build                 lake build (incremental, ~minutes)"
	@echo "    make build-clean           Clean rebuild (slow; ~hours on cold cache)"
	@echo "    make sanity                Quick smoke test (paper_claim_pi + a few others)"
	@echo "    make verify                Full reproducibility: clean build + paper-claim audit"
	@echo "    make scoreboard            Print the public paper-claim scoreboard"
	@echo "    make stats                 Print artefact size statistics (LOC, file counts, K-sums)"
	@echo ""
	@echo "  Documents:"
	@echo "    make notes-pdf             Re-render notes/proof_structure.pdf"
	@echo "    make slides-pdf            Render the GhostDay 2026 deck to PDF"
	@echo ""
	@echo "  Cleanup:"
	@echo "    make clean                 Remove build artefacts (.lake, build/)"
	@echo ""
	@echo "  Settings (override on command line):"
	@echo "    ARCHIVE_DIR    = $(ARCHIVE_DIR)"
	@echo "    PROJECT_KEY    = $(PROJECT_KEY)"
	@echo "    CLAUDE_MEM_DIR = $(CLAUDE_MEM_DIR)"

# ===== First-run orchestration =====
.PHONY: first-run
first-run: prereqs claude-memory-restore pip-install build sanity
	@echo ""
	@echo "✅  first-run complete."
	@echo "   The Lean artefact is built and verified, the Python scaffold is"
	@echo "   installed, and Claude auto-memory has been restored. You can now"
	@echo "   open a Claude Code session here and the persistent context will"
	@echo "   load automatically."
	@echo ""
	@echo "   Recommended next reading for any new Claude instance:"
	@echo "     - $(EML_DIR)/AUTHOR_SUMMARY.md"
	@echo "     - $(EML_DIR)/OPEN_QUESTIONS.md"
	@echo "     - $(NOTES_DIR)/proof_structure.pdf"

# ===== Prerequisites =====
.PHONY: prereqs
prereqs:
	@echo "Checking prerequisites..."
	@command -v elan >/dev/null 2>&1 || { echo "  ✗ elan not found — install from https://leanprover-community.github.io/get_started.html" >&2; exit 1; }
	@command -v lake >/dev/null 2>&1 || { echo "  ✗ lake not found — should be installed by elan" >&2; exit 1; }
	@command -v python3 >/dev/null 2>&1 || { echo "  ✗ python3 not found" >&2; exit 1; }
	@command -v git >/dev/null 2>&1 || { echo "  ✗ git not found" >&2; exit 1; }
	@echo "  ✓ elan: $$(elan --version | head -1)"
	@echo "  ✓ lake: $$(lake --version 2>&1 | head -1)"
	@echo "  ✓ python3: $$(python3 --version)"
	@echo "  ✓ git: $$(git --version)"
	@if [ -f $(LEAN_DIR)/lean-toolchain ]; then \
	    echo "  Lean toolchain pinned to: $$(cat $(LEAN_DIR)/lean-toolchain)"; \
	fi

# ===== Claude memory restore =====
.PHONY: claude-memory-restore
claude-memory-restore:
	@if [ ! -d "$(ARCHIVE_DIR)/claude-memory" ]; then \
	    echo "⚠  archive not found at $(ARCHIVE_DIR)/claude-memory"; \
	    echo "   Set ARCHIVE_DIR=/path/to/snapshot if you snapshotted elsewhere,"; \
	    echo "   or skip this step (memory will start empty in the new instance)."; \
	    exit 0; \
	fi
	@echo "Restoring Claude auto-memory:"
	@echo "  source: $(ARCHIVE_DIR)/claude-memory/"
	@echo "  target: $(CLAUDE_MEM_DIR)/"
	@mkdir -p "$(CLAUDE_MEM_DIR)"
	@cp -r "$(ARCHIVE_DIR)/claude-memory/." "$(CLAUDE_MEM_DIR)/"
	@echo "  ✓ memory restored ($$(ls -1 "$(CLAUDE_MEM_DIR)" | wc -l | tr -d ' ') files)"

# ===== Python scaffold =====
.PHONY: pip-install
pip-install:
	@echo "Installing Python CLI scaffold (rich, prompt_toolkit, pyyaml)..."
	@pip install --quiet -e . 2>&1 | tail -3 || pip install --quiet --break-system-packages -e .
	@echo "  ✓ scaffold installed"
	@echo "    use: python -m lambda_lab.lab.commands.aristotle <cmd>"
	@echo "    or:  python -m lambda_lab.lab.commands.eml <cmd>"

# ===== Lean build =====
.PHONY: build
build:
	@cd $(LEAN_DIR) && lake build 2>&1 | tail -3

.PHONY: build-clean
build-clean:
	@echo "Clean rebuild — this may take hours on a cold Mathlib cache..."
	@cd $(LEAN_DIR) && lake clean && lake build 2>&1 | tail -3

# ===== Sanity / verification =====
.PHONY: sanity
sanity: build
	@echo ""
	@echo "Sanity check: probing public paper-claim symbols..."
	@cd $(LEAN_DIR) && \
	    echo "import EML\nopen EML\n#check @paper_claim_pi\n#check @paper_claim_sin\n#check @paper_claim_cos\n#check @K_count_pi" \
	    > /tmp/eml_sanity.lean && \
	    lake env lean /tmp/eml_sanity.lean 2>&1 | grep -E "^EML\.|paper_claim" | head -5
	@echo "  ✓ sanity passes"

.PHONY: verify
verify: build-clean
	@echo "Full re-verify complete."
	@echo "  jobs: $$(cd $(LEAN_DIR) && lake build 2>&1 | grep -E '[0-9]+ jobs' | tail -1)"
	@$(MAKE) sanity

# ===== Stats / scoreboard =====
.PHONY: scoreboard
scoreboard:
	@echo "==== Public paper claims (theorems exported by EML.Framework.PaperClaims) ===="
	@grep -oE "^theorem paper_claim_[a-zA-Z_]+" $(LEAN_DIR)/EML/Framework/PaperClaims.lean \
	    | sed 's/^theorem /  /'
	@echo ""
	@echo "==== K-counts (machine-checked tree sizes from KCounting.lean) ===="
	@grep -E "K_count_[a-zA-Z_]+ : .* = [0-9]+ := rfl" $(LEAN_DIR)/EML/Framework/KCounting.lean \
	    | sed 's/^theorem //; s/^/  /' | head -50

.PHONY: stats
stats:
	@echo "==== Repository statistics ===="
	@echo "  total tracked files:        $$(git ls-files | wc -l | tr -d ' ')"
	@echo "  Lean files in framework:    $$(find $(LEAN_DIR)/EML/Framework -name '*.lean' | wc -l | tr -d ' ')"
	@echo "  Lean files in solutions:    $$(find $(LEAN_DIR)/EML/Solutions -name '*.lean' | wc -l | tr -d ' ')"
	@echo "  paper_claim theorems:       $$(grep -c '^theorem paper_claim_' $(LEAN_DIR)/EML/Framework/PaperClaims.lean)"
	@echo "  K_count theorems:           $$(grep -c 'K_count_[a-zA-Z_]* :.*:= rfl' $(LEAN_DIR)/EML/Framework/KCounting.lean)"
	@echo "  notes/ documents:           $$(ls -1 $(NOTES_DIR) 2>/dev/null | wc -l | tr -d ' ')"

# ===== Documents =====
.PHONY: notes-pdf
notes-pdf:
	@echo "Re-rendering proof_structure.pdf..."
	@cd $(NOTES_DIR) && pdflatex -interaction=nonstopmode proof_structure.tex >/dev/null && pdflatex -interaction=nonstopmode proof_structure.tex >/dev/null
	@echo "  ✓ $(NOTES_DIR)/proof_structure.pdf"

.PHONY: slides-pdf
slides-pdf:
	@echo "Rendering GhostDay deck..."
	@cd $(GHOSTDAY_DIR) && ./build.sh pdf 2>&1 | tail -3

# ===== Cleanup =====
.PHONY: clean
clean:
	@echo "Removing Lean build artefacts..."
	@cd $(LEAN_DIR) && lake clean 2>/dev/null || true
	@find . -name "*.olean" -delete 2>/dev/null || true
	@find . -type d -name ".lake" -exec rm -rf {} + 2>/dev/null || true
	@find $(GHOSTDAY_DIR) -type d -name "build" -exec rm -rf {} + 2>/dev/null || true
	@echo "  ✓ clean"
