Require Import Relation_Definitions.
Require Import Untyped.

Module Export Rels.

(** Some generic relation things **)

Section CompatClosure.

Variable rel: relation lterm.
(** Variable x y: lterm. **)

(** Compatible closure of a relation on lterms **)

Inductive clos_compat : relation lterm :=
  | clos_base (x y: lterm): rel x y -> clos_compat x y
  | clos_lam  (x y: lterm): clos_compat x y -> clos_compat (Lam x) (Lam y)
  | clos_appl (x f f': lterm): clos_compat f f' -> clos_compat (App f x) (App f' x)
  | clos_appr (x y f: lterm): clos_compat x y -> clos_compat (App f x) (App f y).

End CompatClosure.

End Rels.
