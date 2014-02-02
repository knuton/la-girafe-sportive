Require Import Relation_Operators.
Require Import Relation_Definitions.
Require Import Coq.Structures.Equalities.
Require Import Coq.Program.Equality.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Plus.
Require Import Coq.Arith.Lt.
Require Import Omega.

Require Import Untyped.
Require Import Subst.
Require Import Rels.
Require Import Beta.
Require Import Eta.
Module Export Postpone.

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

Lemma beta_par_lam_k_closed:
  forall k, forall M N,
    beta_par M N -> beta_par (lam_k k M) (lam_k k N).
Proof.
  induction k.
  intros.
  simpl. assumption.
  intros.
  simpl. constructor. constructor. apply beta_par_shift. apply IHk. assumption.
  apply beta_par_refl.
Qed.

Lemma lam_k_eta_red:
  forall k, forall M N,
    eta_par M N -> eta_par (lam_k k M) N.
Proof.
  induction k.
  intros.

  simpl. assumption.

  intros.
  simpl. apply eta_par_base with (lam_k k M).
  reflexivity.
  apply IHk. assumption.
Qed.


Lemma postpone_comm:
  forall M P N,
    eta_par M P -> beta_par P N ->
        (exists P', beta_par M P' /\ eta_par P' N).
Proof.
  intros.
  generalize dependent M.
  rename H0 into H.
  dependent induction H.
  (* [P = (Var n) = N] *)
      intros.
      exists M. split.
      apply beta_par_refl.
      assumption.
  (* [P = (Lam P1)] *)
      intro K.
      intros.
      rename M' into N1.
      rename M into P.
      rename K into M.
      apply eta_par_lam_k_lam in H0.
      do 3 destruct H0.
      rewrite H1; clear H1; clear M.
      apply IHbeta_par in H0.
      do 2 destruct H0.
      exists (Lam x1).
      split.
      apply lam_k_beta_lam. assumption.
      constructor. assumption.

   (* App case *)
      intros MM HH.
      apply eta_par_lam_k_app in HH.
      destruct HH. do 3 destruct H1.
      destruct H2.
      rewrite H3; clear H3; clear MM.
      apply IHbeta_par1 in H1.
      apply IHbeta_par2 in H2.
      do 2 destruct H1.
      do 2 destruct H2.
      (* This feels like a weird choice, but seems to work. *)
      exists (lam_k x (App x2 x3)).
      split.
      Focus 2.
      induction x.
      simpl. constructor; assumption.
      simpl. apply eta_par_base with (lam_k x (App x2 x3)).
      reflexivity. assumption.
      induction x.
      simpl. constructor; assumption.
      simpl. constructor. constructor.
      apply beta_par_shift. assumption. apply beta_par_refl.

   (* subst case *)
      intros.
      apply eta_par_lam_k_app in H1.
      do 4 destruct H1. destruct H2.
      rewrite H3. clear H3. clear M0.
      apply eta_par_lam_k_lam in H1.
      do 3 destruct H1. rewrite H3. clear H3. clear x0.
      apply IHbeta_par1 in H1.
      apply IHbeta_par2 in H2.
      do 2 destruct H1.
      do 2 destruct H2.
      exists (lam_k x (subst 0 x4 x0)).
      split.

      apply beta_par_lam_k_closed.
      apply lam_k_beta_subst. assumption. assumption.

      apply lam_k_eta_red.
      apply eta_par_subst_closed.
      assumption.
      assumption.
Qed.

(* is this definition wrong? *)
Definition beta_eta := union lterm bred eta.
Definition beta_eta_star := clos_refl_trans lterm beta_eta.


Lemma star_exists_iff_par_exists:
  forall M N,
  (exists P, bstar M P /\ eta_star P N) <->
  (exists P, beta_par_trans M P /\ eta_par_trans P N).
Proof.
  split; intros;
  do 2 destruct H;
  exists x; split;
  do 2 (try
          apply bstar_eq_closure_of_beta_par ||
          apply eta_star_eq_closure_of_eta_par;
       assumption).
Qed.

Lemma par_impl_par_trans:
  forall M N,
    (exists P, beta_par M P /\ eta_par P N) ->
    (exists P, beta_par_trans M P /\ eta_par_trans P N).
Proof.
  intros. destruct H. destruct H as [H1 H2].
  exists x.
  split; constructor; assumption.
Qed.

Lemma rewrite_existential_eta:
  forall M N,
  (exists P, beta_par M P /\ eta_star P N) <->
  (exists P, beta_par M P /\ eta_par_trans P N).
Proof.
  split; intros;
  do 2 destruct H;
  exists x; split;
  do 2 (try
          apply bstar_eq_closure_of_beta_par ||
          apply eta_star_eq_closure_of_eta_par;
       assumption).
Qed.

Lemma eta_baby_postpone_eta:
  forall M P N,
    eta_star M P -> beta_par P N ->
      (exists P', beta_par M P' /\ eta_star P' N).
Proof.
  intros ? ? ? H1 H2.
  apply rewrite_existential_eta.
  generalize dependent N.
  dependent induction H1.
  intros.
  assert (HH: exists P', beta_par x P' /\ eta_par P' N).
  apply eta_imp_eta_par in H.
  apply postpone_comm with y; assumption.
  destruct HH. destruct H0.
  exists x0. split. assumption. constructor. assumption.

  intros. exists N.
  split. assumption. constructor. apply eta_par_refl.

  intros.

  fold eta_star in H1_, H1_0.
  apply IHclos_refl_trans2 in H2.
  destruct H2. destruct H.
  apply IHclos_refl_trans1 in H.
  destruct H. destruct H.
  exists x1.
  split. assumption.
  apply t_trans with x0; assumption.
Qed.


Lemma rewrite_existential_beta:
  forall M N,
  (exists P, bstar M P /\ eta_par P N) <->
  (exists P, beta_par_trans M P /\ eta_par P N).
Proof.
  split; intros;
  do 2 destruct H;
  exists x; split;
  do 2 (try
          apply bstar_eq_closure_of_beta_par ||
          apply eta_star_eq_closure_of_eta_par;
       assumption).
Qed.

Lemma eta_baby_postpone_beta:
  forall M P N,
    eta_par M P -> bstar P N ->
      (exists P', bstar M P' /\ eta_par P' N).
Proof.
  intros ? ? ? H1 H2.
  apply rewrite_existential_beta.
  generalize dependent M.
  dependent induction H2.
  intros.
  assert (HH: exists P', beta_par M P' /\ eta_par P' y).
  apply bred_imp_beta_par in H.
  apply postpone_comm with x; assumption.
  destruct HH. destruct H0.
  exists x0. split. constructor. assumption. assumption.

  intros. exists M.
  split. constructor. apply beta_par_refl. assumption.

  intros.

  fold bstar in H2_, H2_0.
  apply IHclos_refl_trans1 in H1.
  destruct H1. destruct H.
  apply IHclos_refl_trans2 in H0.
  destruct H0. destruct H0.
  exists x1.
  split. apply t_trans with x0; assumption. assumption.
Qed.

Theorem eta_postponement_basic:
  forall M N P,
    eta_star M P -> bstar P N -> (exists P', bstar M P' /\ eta_star P' N).
Proof.
  intros.
  rewrite eta_star_eq_closure_of_eta_par in *.
  rewrite bstar_eq_closure_of_beta_par in *.
  rewrite star_exists_iff_par_exists.
  generalize dependent M.
  dependent induction H0.
  intros.
  assert (HH:
            (exists P, beta_par M P /\ eta_star P y) ->
            (exists P, beta_par_trans M P /\ eta_par_trans P y)).
  intros.
  destruct H1. destruct H1.
  apply beta_par_imp_bstar in H1.
  apply bstar_eq_closure_of_beta_par in H1.
  apply eta_star_eq_closure_of_eta_par in H2.
  exists x0.
  split; assumption.

  assert (HH2:
            (exists P, beta_par M P /\ eta_star P y)).

  apply eta_baby_postpone_eta with x.
  apply eta_star_eq_closure_of_eta_par. assumption. assumption.
  apply HH. assumption.

  fold beta_par_trans in H0_, H0_0.
  intros.
  apply IHclos_trans1 in H.
  destruct H. destruct H.
  apply IHclos_trans2 in H0.
  destruct H0. destruct H0.

  exists x1.
  split. apply t_trans with x0; assumption. assumption.
Qed.


(** Main theorem **)
Theorem eta_postponement:
  forall M N,
    beta_eta_star M N -> (exists P, bstar M P /\ eta_star P N).
Proof.
  intros.
  dependent induction H.

  destruct H.
    exists y. split. constructor. assumption. apply rt_refl.
    exists x. split. apply rt_refl. constructor. assumption.

  exists x. split. apply rt_refl. apply rt_refl.

  rename H into H1. rename H0 into H2.
  fold beta_eta_star in H1, H2.

  destruct IHclos_refl_trans1 as [xy]. destruct H as [A1 A2].
  destruct IHclos_refl_trans2 as [yz]. destruct H as [B1 B2].


  assert (H: exists xyz, bstar xy xyz /\ eta_star xyz yz).
  apply eta_postponement_basic with y; assumption.

  do 2 destruct H.
  exists x0.

  split. apply rt_trans with xy; assumption.
  apply rt_trans with yz; assumption.
Qed.

End Postpone.
