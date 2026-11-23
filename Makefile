# Build the papers, the review/complexity markups, and the arXiv bundle.
# Everything generated goes to build/; `make clean` removes it.
#
#   make main | cidr            the two papers (build/main.pdf, build/cidr.pdf)
#   make cidr-review cidr-complexity main-review main-complexity \
#        main-complexity-initial main-changes
#                               each markup's .tex (from scripts/) and its PDF
#   make reviews                all of the markups
#   make all                    papers and markups
#   make arxiv                  build/arxiv/ and build/arxiv.tar.gz
#   make lean                   Lean build and checks (see AGENTS.md)
#   make clean
#
# Plain `tectonic main.tex` and `tectonic cidr.tex` also work from the repo
# root; they write their PDFs next to the sources.

TECTONIC ?= $(shell command -v tectonic 2>/dev/null || echo $(HOME)/.local/bin/tectonic)
PYTHON   ?= python3
BUILD    := build
TEXC     := $(TECTONIC) -X compile

PAPER    := $(wildcard paper/*.tex)
CLASS    := cidr-2027.cls acmart-preload-hook.tex
MAIN_IN  := main.tex $(PAPER) references.bib $(CLASS)
CIDR_IN  := cidr.tex references.bib tex/cidr-extra.bib tex/ACM-Reference-Format-cidr.bst $(CLASS)

MARKUPS  := cidr-review cidr-complexity main-review main-complexity \
            main-complexity-initial main-changes
# Base revision for main-changes.
BASE     ?= origin/main

.PHONY: all main cidr reviews arxiv lean clean FORCE $(MARKUPS)

all: main cidr reviews

main: $(BUILD)/main.pdf
cidr: $(BUILD)/cidr.pdf
reviews: $(MARKUPS)
$(MARKUPS): %: $(BUILD)/%.pdf

$(BUILD):
	@mkdir -p $@

$(BUILD)/main.pdf: $(MAIN_IN) | $(BUILD)
	@$(TEXC) --outdir $(BUILD) main.tex

$(BUILD)/cidr.pdf: $(CIDR_IN) | $(BUILD)
	@$(TEXC) --outdir $(BUILD) cidr.tex

# Markup sources, written to build/ by the scripts.
$(BUILD)/cidr-review.tex: cidr.tex $(PAPER) scripts/cidr_review.py scripts/cidr_categories.json | $(BUILD)
	@$(PYTHON) scripts/cidr_review.py

$(BUILD)/cidr-complexity.tex: cidr.tex scripts/cidr_complexity.py scripts/cidr_complexity.json scripts/cidr_rewrite.json | $(BUILD)
	@$(PYTHON) scripts/cidr_complexity.py

$(BUILD)/main-review.tex: main.tex $(PAPER) cidr.tex scripts/main_review.py scripts/cidr_review.py | $(BUILD)
	@$(PYTHON) scripts/main_review.py

$(BUILD)/main-complexity.tex: main.tex $(PAPER) cidr.tex scripts/main_complexity.py $(wildcard scripts/main-ratings/*.json) | $(BUILD)
	@$(PYTHON) scripts/main_complexity.py

$(BUILD)/main-complexity-initial.tex: main.tex $(PAPER) cidr.tex scripts/main_complexity.py $(wildcard scripts/main-ratings/*.json) | $(BUILD)
	@$(PYTHON) scripts/main_complexity.py --initial

# Depends on git state, so it is always regenerated.
$(BUILD)/main-changes.tex: FORCE | $(BUILD)
	@$(PYTHON) scripts/main_changes.py $(BASE)

# Markup PDFs: the class and bibliographies are found from the repo root.
$(BUILD)/%.pdf: $(BUILD)/%.tex references.bib $(CLASS)
	@$(TEXC) -Z search-path=. --outdir $(BUILD) $<

# arXiv: main.tex, the paper/ files it inputs, references.bib, the
# precompiled bibliography (arXiv does not run BibTeX), and the class files.
# The bundle is test-compiled before it is packed.
arxiv: $(MAIN_IN) | $(BUILD)
	@rm -rf $(BUILD)/arxiv $(BUILD)/arxiv-tmp $(BUILD)/arxiv.tar.gz
	@mkdir -p $(BUILD)/arxiv/paper $(BUILD)/arxiv-tmp
	@$(TEXC) --keep-intermediates --outdir $(BUILD)/arxiv-tmp main.tex
	@cp main.tex references.bib $(CLASS) $(BUILD)/arxiv/
	@cp $(BUILD)/arxiv-tmp/main.bbl $(BUILD)/arxiv/
	@for f in $$(sed -n 's/^[[:space:]]*\\input{\(paper\/[^}]*\)}.*/\1/p' main.tex $(PAPER)); do \
	  cp $$f $(BUILD)/arxiv/$$f; done
	@cd $(BUILD)/arxiv && $(TEXC) --outdir ../arxiv-tmp main.tex
	@tar czf $(BUILD)/arxiv.tar.gz -C $(BUILD)/arxiv .
	@rm -rf $(BUILD)/arxiv-tmp
	@echo "arXiv bundle: $(BUILD)/arxiv.tar.gz"; tar tzf $(BUILD)/arxiv.tar.gz | sort

lean:
	@cd lean && lake build && lake env lean scripts/CheckAxioms.lean && \
	  $(PYTHON) scripts/gen_index.py && lake env lean scripts/CheckReadme.lean

clean:
	rm -rf $(BUILD) scripts/__pycache__
	rm -f main.pdf cidr.pdf comment.cut *.aux *.log *.out *.bbl *.blg *.toc *.synctex.gz

FORCE:
