Require Import Untyped.
Require Import Subst.
Require Import Rels.
Require Import Relation_Operators.

Module Export Eta.

(** * η-conversion *)

Inductive eta_prim : lterm -> lterm -> Prop :=
   eta_base (f g: lterm): (f = shift 0 g) -> eta_prim (Lam (App f (Var 0))) g.

Definition eta := clos_compat eta_prim.

Example ex1_eta : eta (\"x" ~> ((\"y" ~> `"y") $ `"x")) (\"x" ~> `"x").
  apply clos_base. apply eta_base. unfold shift. auto.
Qed.

Example ex2_eta: eta (Lam (App (Lam (Lam (Var 1))) (Var 0))) (Lam (Lam (Var 1))).
Proof.
  apply clos_base. apply eta_base. unfold shift. auto.
Qed.

(* TODO *)
Example ex3_eta: ~ eta (Lam (App (Lam (Var 1)) (Var 0))) (Lam (Var 0)).
Proof.
  admit.
Qed.

(** * Reflexive-transitive closure of η-conversion *)

Definition eta_star := clos_refl_trans lterm eta.
Definition eta_star_step := rt_step lterm eta.
Definition eta_star_refl := rt_refl lterm eta.
Definition eta_star_trans := rt_trans lterm eta.

End Eta.
