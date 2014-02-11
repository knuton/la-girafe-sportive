.PHONY: all doc tex

VERNACS=Untyped.v Subst.v Rels.v Beta.v Eta.v Postpone.v Standardization.v
VERNOCS=$(subst .v,.vo,$(VERNACS))
VERNECS=$(subst .v,.tex,$(VERNACS))

DOCDIR=../doc

all: $(VERNOCS) doc

doc: $(DOCDIR)/index.html

tex: $(addprefix $(DOCDIR)/, $(VERNECS))

$(DOCDIR)/index.html: $(VERNOCS)
	@mkdir -p $(DOCDIR)
	coqdoc \
		--utf8 \
		--interpolate \
		--parse-comments \
		-d $(DOCDIR) \
		$(VERNACS)

$(DOCDIR)/%.tex: %.vo
	@mkdir -p $(DOCDIR)
	coqdoc \
		--utf8 \
		--interpolate \
		--parse-comments \
		--latex \
		-d $(DOCDIR) \
		$*.v

%.vo: %.v
	coqc $<
