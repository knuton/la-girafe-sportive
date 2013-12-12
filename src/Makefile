.PHONY: all doc

VERNACS=Untyped.v Subst.v Rels.v Beta.v Eta.v
VERNOCS=$(subst .v,.vo,$(VERNACS))

DOCDIR=../doc

all: $(VERNOCS) doc

doc: $(DOCDIR)/index.html

$(DOCDIR)/index.html: $(VERNOCS)
	@mkdir -p $(DOCDIR)
	coqdoc \
		--utf8 \
		--interpolate \
		--parse-comments \
		-d $(DOCDIR) \
		$(VERNACS)

%.vo: %.v
	coqc $<
