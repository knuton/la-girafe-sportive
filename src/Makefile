VERNACS=Untyped.v Subst.v
VERNOCS=$(subst .v,.vo,$(VERNACS))

all: $(VERNOCS)

%.vo: %.v
	coqc $<
