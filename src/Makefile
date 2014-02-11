.PHONY: all doc tex

VERNACS=Untyped.v Subst.v Rels.v Beta.v Eta.v Postpone.v Standardization.v
VERNOCS=$(subst .v,.vo,$(VERNACS))
VERNECS=$(addprefix $(DOCDIR)/,$(subst .v,.tex,$(VERNACS)))

DOCDIR=../doc

all: $(VERNOCS) doc pdf

doc: $(DOCDIR)/index.html

pdf: $(DOCDIR)/report.pdf

tex: $(VERNECS)

$(DOCDIR)/index.html: $(VERNOCS)
	coqdoc \
		--utf8 \
		--interpolate \
		--parse-comments \
		-d $(DOCDIR) \
		$(VERNACS)


$(DOCDIR)/report.pdf: $(DOCDIR)/report.tex $(VERNECS)
	cd $(DOCDIR) && pdflatex $<

$(DOCDIR)/%.tex: %.vo
	@mkdir -p $(DOCDIR)
	coqdoc \
		--utf8 \
		--interpolate \
		--body-only \
		--parse-comments \
		--latex \
		-d $(DOCDIR) \
		$*.v

%.vo: %.v
	coqc $<
