.PHONY: all doc

VERNACS=Untyped.v Subst.v Beta.v
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
