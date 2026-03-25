MAIN = article
OUTDIR = out

LATEX = xelatex
BIBER = biber
LATEXFLAGS = -output-directory=$(OUTDIR) -interaction=nonstopmode -halt-on-error

.PHONY: all
all: $(OUTDIR)/$(MAIN).pdf

$(OUTDIR):
	mkdir -p $(OUTDIR)

$(OUTDIR)/$(MAIN).pdf: $(OUTDIR) $(MAIN).tex system-security-article.cls crypto-commands.tex references.bib
	cp references.bib $(OUTDIR)/
	$(LATEX) $(LATEXFLAGS) $(MAIN).tex
	-cd $(OUTDIR) && $(BIBER) $(MAIN) || echo "Warning: biber failed, bibliography may be incomplete"
	$(LATEX) $(LATEXFLAGS) $(MAIN).tex
	$(LATEX) $(LATEXFLAGS) $(MAIN).tex
	@echo "Build complete: $(OUTDIR)/$(MAIN).pdf"

.PHONY: nobib
nobib: $(OUTDIR)
	$(LATEX) $(LATEXFLAGS) $(MAIN).tex
	$(LATEX) $(LATEXFLAGS) $(MAIN).tex
	@echo "Build complete (no bibliography): $(OUTDIR)/$(MAIN).pdf"

.PHONY: quick
quick: $(OUTDIR)
	$(LATEX) $(LATEXFLAGS) $(MAIN).tex
	@echo "Quick build complete"

.PHONY: bib
bib:
	cp references.bib $(OUTDIR)/
	cd $(OUTDIR) && $(BIBER) $(MAIN)

.PHONY: view
view: $(OUTDIR)/$(MAIN).pdf
	open $(OUTDIR)/$(MAIN).pdf

.PHONY: clean
clean:
	rm -rf $(OUTDIR)
	@echo "Cleaned: $(OUTDIR)/ removed"
