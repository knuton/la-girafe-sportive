Require Import Untyped.
Require Import Subst.
Require Import Rels.
Require Import Relation_Operators.
Require Import Relation_Definitions.
Require Import Coq.Structures.Equalities.
Require Import Coq.Program.Equality.

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

Lemma eta_very_substitutive:
  forall (M M' N N': lterm) (n: nat),
  eta M M' -> eta N N' -> eta (subst n N M) (subst n N' M').
Proof.
  admit.
Qed.

Inductive eta_par : lterm -> lterm -> Prop :=
  | eta_par_var: forall n, eta_par (Var n) (Var n)
  | eta_par_lam: forall M M',
                    eta_par M M' -> eta_par (Lam M) (Lam M')
  | eta_par_app: forall M M' N N',
                   eta_par M M' -> eta_par N N' -> eta_par (App M N) (App M' N')
  | eta_par_base: forall M N N', (M = shift 0 N) ->
                                         eta_par N N' ->
                                         eta_par (Lam (App M (Var 0))) N'.


Lemma eta_par_substitutive:
  forall (M M' N N': lterm), forall (n: nat),
    eta_par M M' -> eta_par N N' -> eta_par (subst n N M) (subst n N' M').
Proof.
  admit.
Qed.

Fixpoint lam_k (k: nat) (M: lterm) : lterm :=
  match k with
    | 0 => M
    | (S n) => Lam (App (lam_k n (shift 0 M)) (Var 0))
  end.

Example lam_k_zero:
  forall M, lam_k 0 M = M.
Proof.
  auto.
Qed.


Lemma shift_lam_k_commute:
  forall k, forall t,
                 shift 0 (lam_k k t) = lam_k k (shift 0 t).
Proof.
  induction k.
  simpl. reflexivity.
  intros. simpl.
  unfold shift. simpl. f_equal. f_equal.
  assert (HH: lift 1 1 (lam_k k (lift 1 0 t)) = shift 0 (lam_k k (lift 1 0 t))).
  unfold shift.
  unfold shift in IHk.
  rewrite IHk. rewrite <- IHk. rewrite <- IHk. rewrite <- IHk.
  rewrite lift_fuse. simpl. rewrite lift_fuse. simpl.
  reflexivity. simpl. auto. simpl. auto.
  rewrite HH. apply IHk.
Qed.


Lemma eta_par_lam_k_var:
  forall M, forall n,
    eta_par M (Var n) <-> (exists k, M = lam_k k (Var n)).
Proof.
  intros.
  split.
  (** -> **)
  intros.
  dependent induction H.
  exists 0.
  apply lam_k_zero.
  destruct IHeta_par.
  rewrite H.
  exists (S x). simpl. f_equal. f_equal.
  apply shift_lam_k_commute.
  (** <- **)
  intros.
  destruct H.
  rewrite H.
  clear H. clear M.
  generalize dependent n.
  generalize dependent x.
  intro k.
  induction k.
  intros.
  simpl.
  apply eta_par_var.
  intros.
  simpl.
  apply eta_par_base with (lam_k k (Var n)).
  rewrite shift_lam_k_commute. reflexivity.
  apply IHk.
Qed.


Lemma eta_par_lam_k_app:
  forall M N_1 N_2,
    eta_par M (App N_1 N_2) <->
    (exists k, exists M_1 M_2,
         (eta_par M_1 N_1) /\ (eta_par M_2 N_2) /\  M = lam_k k (App M_1 M_2)).
Proof.
  split.
    (* -> *)
    intro.
    dependent induction H.
    exists 0. simpl.
    exists M.
    exists N.
    split.
    assumption.
    split.
    assumption.
    reflexivity.
    destruct IHeta_par.
    exists (S x).
    simpl.
    destruct H as [M_1].
    destruct H as [M_2].
    exists M_1.
    exists M_2.
    split. destruct H.
    assumption.
    destruct H. destruct H1.
    split. assumption.
    apply f_equal.
    f_equal. rewrite H2. apply shift_lam_k_commute.
    (* <- *)
    intros.
    destruct H as [k].
    generalize dependent M.
    generalize dependent N_1.
    generalize dependent N_2.
    induction k.
    intros.
    destruct H as [M_1].
    destruct H as [M_2].
    destruct H as [H1].
    destruct H as [H2].
    rewrite H.
    simpl. apply eta_par_app. assumption. assumption.

    intros.
    simpl in H.
    destruct H as [M_1].
    destruct H as [M_2].
    destruct H as [H1].
    destruct H as [H2].
    rewrite H.
    rewrite <- shift_lam_k_commute.
    apply eta_par_base with (lam_k k (App M_1 M_2)).
    reflexivity.
    apply IHk.
    exists M_1.
    exists M_2.
    split. assumption.
    split. assumption.
    reflexivity.
Qed.

Lemma eta_par_lam_k_lam:
  forall M N,
    eta_par M (Lam N) <-> (exists k, exists M', (eta_par M' N) /\ (M = lam_k k (Lam M'))).
Proof.
  split.
    (* -> *)
    intro.
    dependent induction H.
    exists 0. exists M.
    split. assumption.
    simpl. reflexivity.
    destruct IHeta_par as [k].
    destruct H as [M'].
    destruct H as [H1].
    exists (S k).
    exists M'.
    split. assumption.
    simpl. rewrite H. f_equal. f_equal.
    apply shift_lam_k_commute.

    (* <- *)
    intros.
    destruct H as [k].
    generalize dependent M.
    generalize dependent N.
    induction k.
    intros. destruct H as [M'].
    destruct H as [H1].
    rewrite H.
    simpl. apply eta_par_lam. assumption.

    intros.
    destruct H as [M'].
    destruct H as [H1].
    rewrite H.
    simpl. rewrite <- shift_lam_k_commute.
    apply eta_par_base with (lam_k k (Lam M')).
    reflexivity.
    apply IHk.
    exists M'.
    split. assumption.
    reflexivity.
Qed.

End Eta.

