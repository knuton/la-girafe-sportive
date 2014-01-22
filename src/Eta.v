Require Import Untyped.
Require Import Subst.
Require Import Rels.
Require Import Relation_Operators.
Require Import Relation_Definitions.
Require Import Coq.Structures.Equalities.
Require Import Coq.Program.Equality.

Module Export Eta.

(** * η-conversion *)

(** We define [eta] conversion as the compatible closure of the [eta_base]
    relation. In literature eta-conversion is usually specified as:

        [[λx. (f x) ~> f]], if [[x]] is not free in [[f]]

    Using de Bruijn indices this corresponds to ensuring that
    [[f]] contains no references to the variable with index [0] (or any of it's
    lifted occurances), which can be expressed by the condition
        [f = shift 0 g]
    Ensuring that *all* variables in [[g]] are of higher binding level.

    Moreover, after the eta-conversion we have lost one λ binder,
    hence we "un-shift" [[f]] to [[g]].
**)

Inductive eta_prim : lterm -> lterm -> Prop :=
   eta_base (f g: lterm): (f = shift 0 g) -> eta_prim (Lam (App f (Var 0))) g.

Definition eta := clos_compat eta_prim.

(** A couple of examples to make sure our definition works with at least
    the basic cases **)

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

(** We prove a couple of substitution lemmas, again, just to exercise the
    definition of [eta], they are not needed for the main result. **)

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

(** * Parallel [eta] conversion *)

(** We now define parallel eta conversion [eta_par],
    it is a trivial translation from the one in the paper, except for the case
    [eta_par_base], in which one needs to do the same translation as for
    [eta_prim].
**)

Inductive eta_par : lterm -> lterm -> Prop :=
  | eta_par_var: forall n,
        eta_par (Var n) (Var n)
  | eta_par_lam: forall M M',
        eta_par M M' -> eta_par (Lam M) (Lam M')
  | eta_par_app: forall M M' N N',
        eta_par M M' -> eta_par N N' -> eta_par (App M N) (App M' N')
  | eta_par_base: forall M N N',
        (M = shift 0 N) -> eta_par N N' ->
          eta_par (Lam (App M (Var 0))) N'.


(** Parallel eta is reflexive on all [lterm]s **)

Lemma eta_par_refl:
  forall t, eta_par t t.
Proof.
  induction t.
  constructor.
  apply eta_par_lam.
  assumption.
  apply eta_par_app.
  assumption. assumption.
Qed.


(** We now define a function for expressing a [k]-fold [eta] expansion of
    an [lterm]. **)

Fixpoint lam_k (k: nat) (M: lterm) : lterm :=
  match k with
    | 0 => M
    (*
     Note: This should have probably been defined in a tail-recursive way, as:

      [ (S n) => lam_k (App (shift 0 M) (Var 0)) ]

      since it is much easier to work with. However,
      I realised this way too late, so left it this way in order to avoid
      modifying existing proofs. Instead, an equivalence of these definitions
      is proved in the [lam_k_alt] lemma.
    *)
    | (S n) => Lam (App (shift 0 (lam_k n M)) (Var 0))
  end.

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

(** A trivial fact **)
Example lam_k_zero:
  forall M, lam_k 0 M = M.
Proof.
  auto.
Qed.


(** Morever we prove this commutativity lemma which will be useful later. **)
Lemma shift_0_lam_commute:
    forall n, forall t,
      shift 0 (lam_k n t) = (lam_k n (shift 0 t)).
Proof.
    induction n.
    (* [n := 0] *)
        simpl. reflexivity.
    (* [n := (S n)] *)
        intros. simpl. unfold shift. simpl.
        f_equal. f_equal.
        rewrite lift_fuse. simpl. rewrite <- IHn. unfold shift.
        rewrite lift_fuse. simpl.
        reflexivity. simpl. auto. simpl. auto.
Qed.

(** We now prove some basic properties about the relationship between [[eta]]
    and [[lam_k]]. (This is Lemma 3.2 in the Takahashi paper.) **)

(* Lemma 3.2 (1) *)
Lemma eta_par_lam_k_var:
  forall M, forall n,
    eta_par M (Var n) <-> (exists k, M = lam_k k (Var n)).
Proof.
  intros. split.
  (* -> *)
      (* trivial induction on the definition of [eta_par] *)
      intros.
      dependent induction H.
      exists 0.
      apply lam_k_zero.
      destruct IHeta_par.
      rewrite H.
      exists (S x). simpl. f_equal.
  (* <- *)
      intros.
      (* clean up our hypothesis a bit *)
      destruct H.
      rewrite H.
      clear H. clear M.
      generalize dependent n.
      generalize dependent x.
      (* again, just perform simple induction on [k] *)
      intro k.
      induction k.
          intros.
          simpl.
          apply eta_par_var.

          intros.
          simpl.
          apply eta_par_base with (lam_k k (Var n)).
          reflexivity.
          apply IHk.
Qed.

(* Lemma 3.2 (2), the proof technique is essentially the same as for
   [eta_par_lam_k_var].
*)
Lemma eta_par_lam_k_app:
  forall M N_1 N_2,
    eta_par M (App N_1 N_2)
    <->
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
    f_equal. rewrite H2. reflexivity.
    (* <- *)
    intros.
    destruct H as [k].
    generalize dependent M.
    generalize dependent N_1.
    generalize dependent N_2.
    induction k.
    (* [k := 0] *)
        intros.
        destruct H as [M_1].
        destruct H as [M_2].
        destruct H as [H1].
        destruct H as [H2].
        rewrite H.
        simpl. apply eta_par_app. assumption. assumption.
    (* [k := (S k)] *)
        intros.
        simpl in H.
        destruct H as [M_1].
        destruct H as [M_2].
        destruct H as [H1].
        destruct H as [H2].
        rewrite H.
        apply eta_par_base with (lam_k k (App M_1 M_2)).
        reflexivity.
        apply IHk.
        exists M_1.
        exists M_2.
        split. assumption.
        split. assumption.
        reflexivity.
Qed.


(* Lemma 3.2 (3), the situation is again similar to the previous two
    cases *)
Lemma eta_par_lam_k_lam:
  forall M N,
        eta_par M (Lam N)
        <->
        (exists k, exists M', (eta_par M' N) /\ (M = lam_k k (Lam M'))).
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
    simpl. rewrite H. f_equal.

  (* <- *)
    intros.
    destruct H as [k].
    generalize dependent M.
    generalize dependent N.
    induction k.
    (* [k := 0] *)
        intros. destruct H as [M'].
        destruct H as [H1].
        rewrite H.
        simpl. apply eta_par_lam. assumption.

    (* [k := (S k)] *)
        intros.
        destruct H as [M'].
        destruct H as [H1].
        rewrite H.
        simpl.
        apply eta_par_base with (lam_k k (Lam M')).
        reflexivity.
        apply IHk.
        exists M'.
        split. assumption.
        reflexivity.
Qed.

End Eta.
