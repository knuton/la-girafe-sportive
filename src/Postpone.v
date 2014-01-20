Require Import Untyped.
Require Import Subst.
Require Import Rels.
Require Import Relation_Operators.
Require Import Relation_Definitions.
Require Import Coq.Structures.Equalities.
Require Import Coq.Program.Equality.
Require Import Beta.
Require Import Eta.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Plus.
Require Import Coq.Arith.Lt.
Require Import Omega.

Module Export Postpone.

Lemma lam_k_alt:
  forall k, forall M,
    lam_k (S k) M = lam_k k (Lam (App (shift 0 M) (Var 0))).
Proof.
  induction k.
  intros. simpl. reflexivity.
  intros.
  simpl. do 4 f_equal. rewrite <- IHk. simpl.
  reflexivity.
Qed.

Lemma lam_k_beta_subst:
  forall k, forall M M' N N',
    beta_par M M' -> beta_par N N' ->
      beta_par (App (lam_k k (Lam M)) N) (subst 0 N' M').
Proof.
  induction k.
  (** k := 0 **)
  intros.
  simpl. apply beta_par_base; assumption.
  (** k := (S k) **)
  intros.
  simpl.
  apply beta_par_base. rewrite shift_0_lam_commute.
  unfold shift. simpl.
  replace M' with (subst 0 (Var 0) (shift 1 M')).
  apply IHk.
  apply beta_par_shift. assumption. apply beta_par_refl.
  apply subst_k_shift_S_k. assumption.
Qed.


Lemma lam_k_beta_lam:
  forall k, forall M M',
    beta_par M M' -> beta_par (lam_k k (Lam M)) (Lam M').
Proof.
  induction k.
  (* k := 0 *)
  intros. simpl. apply beta_par_lam. assumption.
  (* k := (S k) *)

  intros.
  remember H as HH. clear HeqHH. apply IHk in H.
  simpl.
  constructor.
  rewrite shift_0_lam_commute.
  unfold shift. simpl.
  replace M' with (subst 0 (Var 0) (shift 1 M')).
  apply lam_k_beta_subst.
  apply beta_par_shift. assumption.
  apply beta_par_refl.
  apply subst_k_shift_S_k.
Qed.

Lemma lam_k_beta_app:
  forall k, forall M M' N N',
    beta_par M M' -> beta_par N N' ->
      beta_par (App (lam_k k M) N) (App M' N').
Proof.
  induction k.
  (** k := 0 **)
  intros. simpl. apply beta_par_app. assumption. assumption.
  (** k := (S k) **)
  intros.
  rewrite lam_k_alt.
  replace (App M' N') with (subst 0 N' (App (shift 0 M') (Var 0))).
  apply lam_k_beta_subst.
  constructor. apply beta_par_shift. assumption. apply beta_par_refl.
      assumption.
  simpl. rewrite lift_0_ident. rewrite subst_shift_ident. reflexivity.
Qed.

Lemma lam_S_k_beta:
  forall k, forall M M',
    beta_par M M' ->
      beta_par (lam_k (S k) M) (lam_k 1 M').
Proof.
  induction k.
  (** k := 0 **)
  intros. simpl.
  constructor. constructor. apply beta_par_shift. assumption.
  apply beta_par_refl.
  (** k := (S k) **)
  intros.
  rewrite lam_k_alt.
  apply lam_k_beta_lam.
  constructor. apply beta_par_shift. assumption. apply beta_par_refl.
Qed.


Lemma postpone_comm:
  forall M P N,
    eta_par M P -> beta_par P N ->
        (exists P', beta_par M P' /\ eta_par P' N).
Proof.
  intros.
  generalize dependent M.
  dependent induction H0.

  intros.
  exists M. split.
  apply beta_par_refl.
  assumption.

  intros.
  (* TODO *)
  admit.
  admit.
  admit.
Qed.

Definition beta_eta_star := union lterm bstar eta_star.

Theorem eta_postponement:
  forall M N,
    beta_eta_star M N -> (exists P, bstar M P /\ eta_star P N).
Proof.
  admit.
Qed.


End Postpone.