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

Example ex3_eta: ~ eta (Lam (App (Lam (Var 1)) (Var 0))) (Lam (Var 0)).
Proof.
  unfold not. intros. inversion H.
  inversion H0. discriminate.
  inversion H2. inversion H3.
Qed.

(** * Reflexive-transitive closure of η-conversion *)

Definition eta_star := clos_refl_trans lterm eta.
Definition eta_star_step := rt_step lterm eta.
Definition eta_star_refl := rt_refl lterm eta.
Definition eta_star_trans := rt_trans lterm eta.


Lemma eta_prim_substitutive:
  forall (M N L: lterm) (n: nat),
  eta_prim M N -> eta_prim (subst n L M) (subst n L N).
Proof.
  intros.
  assert (What: n + 1 = S n). omega.
  destruct H.
  assert (Hmm: subst n L (Lam (App f (Var 0))) =
               Lam (App (subst (S n) L f) (Var 0))).
  simpl.
  rewrite What. auto.
  rewrite Hmm.
  apply eta_base.
  unfold shift.
  rewrite lift_lem2. simpl. rewrite H. rewrite What.
  unfold shift.
  reflexivity. omega.
Qed.

Lemma eta_substitutive:
  forall (M N L: lterm) (n: nat),
  eta M N -> eta (subst n L M) (subst n L N).
Proof.
  intros. generalize dependent n. generalize dependent L.
  unfold eta.
  induction H.
  intros. apply clos_base. apply eta_prim_substitutive. assumption.
  (* TODO: find out why subst unfolds into the ugly thing after applying
     one of the clos_{lam,appl,appr}
   *)
  intros. apply clos_lam. apply IHclos_compat.
  intros. apply clos_appl. apply IHclos_compat.
  intros. apply clos_appr. apply IHclos_compat.
Qed.

End Eta.
