Require Import Untyped.
Require Import Subst.
Require Import Beta.

Require Import Omega.
Require Import Relation_Operators.
Require Import Coq.Program.Equality.

(** * Standardization in Untyped Lambda Calculus *)

Module Export Standardization.

(* This module contains a proof of the Standardization Theorem for the untyped
   lambda calculus, made lückenlos with the help of Coq.

   The actual proof is not original, but closely follows that given by Ryo
   Kashima in ``A Proof of the Standardization Theorem in λ-Calculus''
   (Tokyo Institute of Technology, 2000). Due to its inductive definition
   of a standard derivation, Kashima's proof is a friendly basis for a fully
   formal one.

   Minor adaptations were made where prudent to facilitate work with the proof
   assistant. Those differences are pointed out in the comments and it was
   generally attempted to stay close to the paper, allowing the reader to study
   paper and Coq verbatim side by side. *)

(** ** Preliminaries *)

(** Reduction Numbering (Definition 2.1) **)

(* Count the total number of redexes in a term. *)

Fixpoint redcount (M : lterm) : nat :=
  match M with
  | Var i as v => 0
  | App (Lam N) N' => (redcount N) + (redcount N') + 1
  | App N N' => (redcount N) + (redcount N')
  | Lam N => redcount N
  end.

(* For brevity in definitions and proofs, we introduce two functions which
   serve to adjust the reduction count in case of [l]eft or [r]ight
   application. *)

Definition ladjust (M : lterm) (n : nat) :=
  match M with
  | Var _ => n
  | Lam _ => n + redcount M + 1
  | App _ _ => n + redcount M
  end.

Definition radjust (M : lterm) (n : nat) :=
  match M with
  | Var _ => n
  | Lam _ => n + 1
  | App _ _ => n
  end.

(* This is the predicate defined in 2.1.
   [nthred n A B] states that [B] is the result of reducing the [A]-th
   redex in [B].

   In order to simplify working with this definition, we start counting from
   zero, while in the paper counting starts from one.
*)

Inductive nthred : nat -> lterm -> lterm -> Prop :=
  | nthred_base : forall A B,
      nthred 0 (App (Lam A) B) (subst 0 B A)
  | nthred_concr : forall n A B C,
      nthred n A B -> nthred (radjust A n) (App A C) (App B C)
  | nthred_concl : forall n A B C,
      nthred n A B -> nthred (ladjust C n) (App C A) (App C B)
  | nthred_lam : forall n A B,
      nthred n A B -> nthred n (Lam A) (Lam B).

(* Some implications for lambda terms related by [nthred]. *)

Lemma nthred_outer_lam : forall M N n,
  nthred n M N -> (exists M', M = Lam M') -> exists N', N = Lam N'.
Proof.
  intros. inversion H0. inversion H.
    rewrite H1 in H3. inversion H3.
    rewrite H1 in H4. inversion H4.
    rewrite H1 in H4. inversion H4.
    exists B. reflexivity.
Qed.

Lemma nthred_radjust : forall M N n k l,
  nthred n M N -> k >= l -> radjust N k >= radjust M l.
Proof.
  intros. destruct M; destruct N.
    simpl. omega. simpl. omega. simpl. omega.
    simpl. apply nthred_outer_lam in H.
      inversion H. inversion H1. exists M. reflexivity.
    simpl. omega.
    simpl. apply nthred_outer_lam in H.
      inversion H. inversion H1. exists M. reflexivity.
    simpl. assumption.
    simpl. omega.
    simpl. assumption.
Qed.

Lemma nthred_redcount : forall n M N,
  nthred n M N -> redcount N >= n.
Proof.
  intros. induction H.
    omega.
    destruct B; destruct A; simpl; simpl in IHnthred;
      try (omega || inversion H).
    destruct C; simpl.
      assumption.
      omega.
      destruct C1; simpl; omega.
    simpl. assumption.
Qed.

(** Beta-reduction and left-most reduction (Definition 2.2) **)

(* The paper defines beta-reduction in terms of the [nthred] relation.

   It is easy to show equivalence of the two definitions of beta reduction,
   see [bet_bred].
*)

Definition bet (A B : lterm) : Prop := exists n : nat, nthred n A B.

(* [betstar] is the reflexive-transitive closure of [bet]. *)

Definition betstar := clos_refl_trans lterm bet.
Definition betstar_step := rt_step lterm bet.
Definition betstar_refl := rt_refl lterm bet.
Definition betstar_trans := rt_trans lterm bet.

(* We prove equivalence of our definition of beta reduction with the
   regular definition from [Beta]. *)

Lemma bet_bred : forall A B, bet A B <-> bred A B.
Proof.
  intros.
  split.
  (* bet A B -> bred A B *)
  intro Hbet. unfold bet in Hbet. inversion Hbet. induction H.
    apply bred_base.
    apply bred_appl. apply IHnthred. exists n. assumption.
    apply bred_appr. apply IHnthred. exists n. assumption.
    apply bred_lam. apply IHnthred. exists n. assumption.
  (* bred A B -> bet A B *)
  intro Hbred. induction Hbred.
    unfold bet. exists 0. apply nthred_base.
    unfold bet. inversion IHHbred.
      exists x. apply nthred_lam. assumption.
    unfold bet. inversion IHHbred.
      exists (radjust t1 x). apply nthred_concr. assumption.
    unfold bet. inversion IHHbred.
      exists (ladjust t3 x). apply nthred_concl. assumption.
Qed.

(* Left-most reduction is simply reduction of the first redex. *)

Definition lmost (A B : lterm) : Prop := nthred 0 A B.

(* [lstar] is the reflexive-transitive closure of [lmost]. *)

Definition lstar := clos_refl_trans lterm lmost.
Definition lstar_step := rt_step lterm lmost.
Definition lstar_refl := rt_refl lterm lmost.
Definition lstar_trans := rt_trans lterm lmost.

(** *** Definition 2.3, Standard Reduction Sequence *)

(** Preliminaries *)

(* A lambda sequence, [seq], is a lambda term or a lambda sequence together
   with a number and a lambda term. *)

Inductive seq : Type :=
  | seq_unit : lterm -> seq
  | seq_cons : seq -> nat -> lterm -> seq.

(* [seqhead] gives the leftmost (first) lambda term in a lambda sequence. *)

Fixpoint seqhead (s : seq) : lterm :=
  match s with
  | seq_unit A => A
  | seq_cons s _ _ => seqhead s
  end.

(* [seqlast] gives the rightmost (last) lambda term in a lambda sequence. *)

Fixpoint seqlast (s : seq) : lterm :=
  match s with
  | seq_unit B => B
  | seq_cons _ _ B => B
  end.

(* Any lambda sequence [s] can be extended to the left by providing a number
   and a lambda term to be prepended to the first term. *)

Fixpoint leftexpand (M : lterm) (n : nat) (s : seq) : seq :=
  match s with
  | seq_unit B => seq_cons (seq_unit M) n B
  | seq_cons s' m N => seq_cons (leftexpand M n s') m N
  end.

(* Extract the head reduction count from a sequence. *)

Definition seqn (s: seq) : nat :=
  match s with
  | seq_unit A => 0
  | seq_cons _ n _ => n
  end.

(* Extract the last reduction count from a sequence. *)

Fixpoint seqnrev (s: seq) : nat :=
  match s with
  | seq_unit A => 0
  | seq_cons (seq_unit M) n N => n
  | seq_cons s' _ _ => seqnrev s'
  end.

(* [seqcat] is concatenation for lambda sequences, requiring a natural number
   as a ``connective'' in addition to two lambda sequences. *)

Fixpoint seqcat (s1 : seq) (n : nat) (s2 : seq) : seq :=
  match s2 with
  | seq_unit B => seq_cons s1 n B
  | seq_cons s2' m B => seq_cons (seqcat s1 n s2') m B
  end.

(* A simple result about sequence concatenation: Concatenating a simplex
   sequence [s1] with any sequence [s2] is equivalent to doing a left expansion
   with [s1]'s constituent lambda term. *)

Lemma seqcat_leftexpand : forall M n s,
  seqcat (seq_unit M) n s = leftexpand M n s.
Proof. intros. induction s. reflexivity. simpl. rewrite IHs. reflexivity. Qed.

Lemma seqlast_seqcat : forall s1 s2 n,
  seqlast (seqcat s1 n s2) = seqlast s2.
Proof. intros. induction s1; induction s2; reflexivity. Qed.

Lemma seqn_seqcat : forall s1 n s2,
  seqn (seqcat s1 n s2) = n \/ seqn (seqcat s1 n s2) = seqn s2.
Proof.
  intros. destruct s1; destruct s2.
    left. reflexivity.
    right. reflexivity.
    left. reflexivity.
    right. reflexivity.
Qed.

(* Interaction of left expansion with extractors for first and last sequence
   members. *)

Lemma leftexpand_seqhead : forall M n s, seqhead (leftexpand M n s) = M.
Proof. intros. induction s. reflexivity. simpl. apply IHs. Qed.

Lemma leftexpand_seqlast : forall M n s, seqlast (leftexpand M n s) = seqlast s.
Proof. intros. induction s. reflexivity. reflexivity. Qed.

(* Interaction of left expansion with reduction count extraction. *)

Lemma leftexpand_bound : forall M s, seqn (leftexpand M 0 s) = seqn s.
Proof. intros. induction s. simpl. omega. simpl. omega. Qed.

(* A reduction sequence, [redseq], is a lambda sequence [s] in which for every
   cons cell consisting of [s'], [n] and [M], the last term [L] of [s'] yields
   [M] by reducing its [n]-th redex, i.e. [nthred n L M]. *)

Inductive redseq : seq -> Prop :=
  | redseq_unit : forall A, redseq (seq_unit A)
  | redseq_cons : forall s n A,
                    nthred n (seqlast s) A ->
                    redseq s ->
                    redseq (seq_cons s n A).

Lemma redseq_seqcat : forall s1 s2 n,
  nthred n (seqlast s1) (seqhead s2) ->
  redseq s1 -> redseq s2 -> redseq (seqcat s1 n s2).
Proof.
  intros. dependent induction s1; dependent induction s2.
    simpl. apply redseq_cons. simpl. simpl in H. assumption. assumption.
    simpl. apply redseq_cons. inversion H1. rewrite seqlast_seqcat. assumption.
    apply IHs2. simpl. simpl in H. assumption. inversion H1. assumption.
    inversion H1. assumption.
    simpl. apply redseq_cons. simpl. simpl in H. assumption. assumption.
    simpl. apply redseq_cons. rewrite seqlast_seqcat. inversion H1. assumption.
    simpl in IHs2. inversion H1. apply IHs2 in H; assumption.
Qed.

(* A monotone sequence, [monotone], is a lambda sequence [s] in which connective
   numbers increase non-strictly from left to right. *)

Inductive monotone : seq -> Prop :=
  | monotone_unit : forall A, monotone (seq_unit A)
  | monotone_cons : forall n A s,
      monotone s ->
      (n >= seqn s \/ exists M, s = seq_unit M) ->
      monotone (seq_cons s n A).

(* Monotonicity and left-expansion *)

Lemma monotone_seqn : forall s n M,
  monotone s -> seqn (leftexpand M n s) = seqn s \/ exists N, s = seq_unit N.
Proof.
  intros. induction s.
    (* seq_unit *)
    right. exists l. reflexivity.
    (* seq_cons *)
    inversion H. apply IHs in H2. inversion H2.
    left. reflexivity.
    inversion H5. rewrite H6. simpl. left. reflexivity.
Qed.

Lemma leftexpand_monotone : forall M s,
  monotone s -> monotone (leftexpand M 0 s).
Proof.
  intros. induction s.
    (* seq_unit *)
    simpl. apply monotone_cons. apply monotone_unit. simpl. left. omega.
    (* seq_cons *)
    simpl. apply monotone_cons. apply IHs. inversion H. assumption.
    inversion H.
    assert (seqn (leftexpand M 0 s) = seqn s \/ exists N, s = seq_unit N).
      apply monotone_seqn. assumption.
    inversion H5.
    left.
      inversion H4.
        rewrite H6. assumption.
        inversion H7. rewrite H8. simpl. omega.
    rewrite leftexpand_bound. inversion H4.
      left. assumption.
      left. inversion H6. rewrite H8. simpl. omega.
Qed.

(** Standard reduction sequence **)

(* A standard reduction sequence, [stseq], is a lambda sequence [s] which is a
   monotone reduction sequence. *)

Definition stseq (s : seq) : Prop := redseq s /\ monotone s.

(* A reusable proof of the simple fact that subsequences of standard reduction
   sequences are standard reduction sequences. *)

Lemma stseq_backwards : forall M n s, stseq (seq_cons s n M) -> stseq s.
Proof.
  intros. unfold stseq in H. inversion H. inversion H0. inversion H1.
  unfold stseq. split; assumption.
Qed.

Lemma stseq_leftexpand : forall M s,
  stseq s -> lmost M (seqhead s) -> stseq (leftexpand M 0 s).
Proof.
  intros M s Hstseq Hlmost. induction s.
    simpl. unfold stseq.
    split.
      apply redseq_cons. unfold lmost in Hlmost. simpl in Hlmost. simpl. assumption.
      apply redseq_unit.
    inversion Hstseq. apply monotone_cons. apply monotone_unit. simpl. left. omega.
    simpl. unfold stseq.
    split.
      apply redseq_cons. unfold lmost in Hlmost. rewrite leftexpand_seqlast.
        unfold stseq in Hstseq. inversion Hstseq. inversion H. assumption.
      apply IHs.
        apply (stseq_backwards l n s). assumption.
        simpl in Hlmost. assumption. apply monotone_cons.
          apply leftexpand_monotone. inversion Hstseq.
          apply stseq_backwards in Hstseq. unfold stseq in Hstseq. inversion Hstseq.
            assumption. inversion Hstseq. inversion H0. rewrite leftexpand_bound.
              inversion H5.
                left. assumption.
                left. inversion H6. rewrite H7. simpl. omega.
Qed.

Lemma redcount_seqn : forall s,
  stseq s -> redcount (seqlast s) >= seqn s.
Proof.
  destruct s.
    simpl. omega.
    intro Hstseq. simpl. inversion Hstseq. inversion H.
      apply nthred_redcount with (M := seqlast s). assumption.
Qed.

(* This lemma helps concisely eliminating the common goal of a one-term
   reduction sequence being standard. *)

Lemma stseq_unit : forall M, stseq (seq_unit M).
Proof. intros. unfold stseq. split. apply redseq_unit. apply monotone_unit. Qed.

(** A range of respectful operations on reduction sequences. *)

(* Applying each member of a sequence [s] to a lambda term [M]. *)

Fixpoint appl (M : lterm) (s : seq) : seq :=
  match s with
  | seq_unit A => seq_unit (App M A)
  | seq_cons s n B => seq_cons (appl M s) (ladjust M n) (App M B)
  end.

Lemma seqhead_appl : forall s M, seqhead (appl M s) = App M (seqhead s).
Proof.
  intros. induction s.
    induction M; reflexivity.
    induction M; simpl; apply IHs.
Qed.

Lemma seqlast_appl : forall s M, seqlast (appl M s) = App M (seqlast s).
Proof. intros. induction s; induction M; reflexivity. Qed.

Lemma seqn_appl_var : forall s x, seqn (appl (Var x) s) = seqn s.
Proof. intros. induction s; simpl; omega. Qed.

Lemma seqn_appl_lam : forall s M, seqn s + redcount M + 1 >= seqn (appl (Lam M) s).
Proof. intros. induction s; induction M; simpl; omega. Qed.

Lemma seqn_appl_app : forall s M M',
  seqn s + redcount (App M M') >= seqn (appl (App M M') s).
Proof. intros. induction s; induction M; induction M'; simpl; omega. Qed.

Lemma redseq_appl : forall s M, redseq s -> redseq (appl M s).
Proof.
  intros. induction s.
    (* seq_unit *)
    induction M; simpl; apply redseq_unit.
    (* seq_cons *)
    induction M; unfold appl; fold appl; apply redseq_cons.
      (* Var *)
      rewrite seqlast_appl. apply nthred_concl. inversion H. assumption.
      apply IHs. inversion H. assumption.
      (* Lam *)
      rewrite seqlast_appl. apply nthred_concl. inversion H. assumption.
      apply IHs. inversion H. assumption.
      (* App *)
      rewrite seqlast_appl. apply nthred_concl. inversion H. assumption.
      apply IHs. inversion H. assumption.
Qed.

Lemma monotone_appl : forall s M, monotone s -> monotone (appl M s).
Proof.
  intros. induction s; induction M.
    apply monotone_unit. apply monotone_unit. apply monotone_unit.
    simpl. apply monotone_cons.
      apply IHs. inversion H. assumption.
      inversion H. rewrite seqn_appl_var. inversion H4.
        left. assumption.
        left. inversion H5. rewrite H6. simpl. omega.
    simpl. apply monotone_cons.
      apply IHs. inversion H. assumption.
      inversion H. assert (seqn s + redcount M + 1 >= seqn (appl (Lam M) s)).
        apply seqn_appl_lam. inversion H4.
         left. omega.
         left. inversion H6. rewrite H7. simpl. omega.
    simpl. apply monotone_cons.
      apply IHs. inversion H. assumption. simpl. fold redcount. case_eq (M1).
        (* Var *)
        intros.
        assert (E: redcount (Var n0) + redcount M2 =
                   redcount (App (Var n0) M2)).
        reflexivity. rewrite E. inversion H.
        assert (seqn s + redcount (App (Var n0) M2) >=
                seqn (appl (App (Var n0) M2) s)).
        apply seqn_appl_app. inversion H5.
          left. omega.
          left. inversion H7. rewrite H8. simpl. omega.
        (* Lam *)
        intros.
        assert (E: redcount l0 + redcount M2 + 1 = redcount (App (Lam l0) M2)).
        reflexivity. rewrite E. inversion H.
        assert (seqn s + redcount (App (Lam l0) M2) >=
                seqn (appl (App (Lam l0) M2) s)).
        apply seqn_appl_app. inversion H5.
          left. omega.
          left. inversion H7. rewrite H8. simpl. omega.
        (* App *)
        intros.
        assert (E: redcount (App l0 l1) + redcount M2 =
                   redcount (App (App l0 l1) M2)).
        reflexivity. rewrite E. inversion H.
        assert (seqn s + redcount (App (App l0 l1) M2) >=
                seqn (appl (App (App l0 l1) M2) s)).
        apply seqn_appl_app. inversion H5.
          left. omega.
          left. inversion H7. rewrite H8. simpl. omega.
Qed.

Lemma stseq_appl : forall s M, stseq s -> stseq (appl M s).
Proof.
  intros. unfold stseq. split.
    apply redseq_appl. inversion H. assumption.
    apply monotone_appl. inversion H. assumption.
Qed.

(* Applying a lambda term [M] to every member of a sequence [s]. *)

Fixpoint appr (M : lterm) (s : seq) : seq :=
  match s with
  | seq_unit A => seq_unit (App A M)
  | seq_cons s n B => seq_cons (appr M s) (radjust (seqlast s) n) (App B M)
  end.

Lemma seqhead_appr : forall s M, seqhead (appr M s) = App (seqhead s) M.
Proof.
  intros. induction s.
  induction M; reflexivity.
  induction M; simpl; apply IHs.
Qed.

Lemma seqlast_appr : forall s M, seqlast (appr M s) = App (seqlast s) M.
Proof. intros. induction s; induction M; reflexivity. Qed.

Lemma appr_cons : forall s n M N,
  appr N (seq_cons s n M) = seq_cons (appr N s) (radjust (seqlast s) n) (App M N).
Proof. intros. induction s; induction l; reflexivity. Qed.

Lemma redseq_appr : forall s M, redseq s -> redseq (appr M s).
Proof.
  intros. induction s.
  (* seq_unit *)
  induction M; simpl; apply redseq_unit.
  (* seq_cons *)
  induction M; unfold appr; fold appr; apply redseq_cons.
      (* Var *)
      rewrite seqlast_appr. apply nthred_concr. inversion H. assumption.
      apply IHs. inversion H. assumption.
      (* Lam *)
      rewrite seqlast_appr. apply nthred_concr. inversion H. assumption.
      apply IHs. inversion H. assumption.
      (* App *)
      rewrite seqlast_appr. apply nthred_concr. inversion H. assumption.
      apply IHs. inversion H. assumption.
Qed.

Lemma monotone_appr : forall s M, stseq s -> monotone (appr M s).
Proof.
  intros. inversion H. induction s.
    (* seq_unit *)
    induction M; apply monotone_unit.
    (* seq_cons *)
    simpl. apply monotone_cons.
      apply IHs.
        apply stseq_backwards in H. assumption.
        inversion H0. assumption.
        inversion H1. assumption.
      destruct s.
        destruct l0; simpl; left; omega.
        rewrite appr_cons. simpl. inversion H0.
          inversion H6.
          left. apply nthred_radjust with (n := n0).
            assumption.
            inversion H1. simpl in H16. inversion H16.
              assumption.
              inversion H17. inversion H18.
Qed.

Lemma stseq_appr : forall s M, stseq s -> stseq (appr M s).
Proof.
  intros. unfold stseq. split.
    apply redseq_appr. inversion H. assumption.
    apply monotone_appr. assumption.
Qed.

(* Wrap all members of a reduction sequence in lambdas. *)

Fixpoint lambdize (s : seq) : seq :=
  match s with
  | seq_unit A => seq_unit (Lam A)
  | seq_cons s n B => seq_cons (lambdize s) n (Lam B)
  end.

(* We prove results for some simple interactions of [lambdize] with sequence
   operations. *)

Lemma seqhead_lambdize : forall s, seqhead (lambdize s) = Lam (seqhead s).
Proof. intros. induction s. reflexivity. simpl. apply IHs. Qed.

Lemma seqlast_lambdize : forall s, seqlast (lambdize s) = Lam (seqlast s).
Proof. intros. induction s; reflexivity. Qed.

Lemma seqn_lambdize : forall s, seqn (lambdize s) = seqn s.
Proof. intros. induction s; reflexivity. Qed.

(* We establish that standard sequences are stable wrt [lambdize]. *)

Lemma stseq_lambdize : forall s, stseq s -> stseq (lambdize s).
Proof.
  intros. inversion H. induction s.
    (* seq_unit *)
    simpl. apply stseq_unit.
    (* seq_cons *)
    simpl. unfold stseq.
    split.
      apply redseq_cons. inversion H0. rewrite seqlast_lambdize.
        apply nthred_lam. assumption.
        inversion H0. apply stseq_backwards in H. apply IHs in H.
        inversion H. assumption. assumption. inversion H. assumption.
      apply monotone_cons. inversion H. inversion H3. apply stseq_backwards in H.
        apply IHs in H. inversion H. assumption. inversion H.
          assumption.
          assumption.
      rewrite seqn_lambdize. inversion H1. inversion H6.
        left. assumption.
        left. inversion H7. rewrite H8. simpl. omega.
Qed.

Lemma stseq_lambda : forall A B,
  (exists s : seq, seqhead s = A /\ seqlast s = B /\ stseq s) ->
   exists s : seq, seqhead s = (Lam A) /\ seqlast s = (Lam B) /\ stseq s.
Proof.
  intros. inversion H. induction x.
    (* seq_unit *)
    inversion H0. inversion H2.
    simpl in H1. simpl in H3.
    rewrite <- H1. rewrite <- H3.
    exists (seq_unit (Lam l)).
    split.
      reflexivity.
      split.
        reflexivity.
        apply stseq_unit.
    (* seq_cons *)
    inversion H.
    exists (lambdize x0). inversion H1. inversion H3.
    split.
      rewrite seqhead_lambdize. f_equal. assumption.
      split.
        rewrite seqlast_lambdize. f_equal. assumption.
        apply stseq_lambdize. assumption.
Qed.

(* ``Zip'' two lambda sequences.

   Beta reduction sequences s1 = A ->> B, s2 = C ->> D will be zipped to a
   sequence A C ->> ... ->> B C ->> ... ->> B D, with reduction counts adapted
   to maintain reduction and monotonocity properties. *)

Definition zip (s1 : seq) (s2 : seq) : seq :=
  match s1, s2 with
  | seq_unit M, _ => appl M s2
  | seq_cons s1' m M, _ =>
      seqcat (appr (seqhead s2) s1') (radjust (seqlast s1') m) (appl M s2)
  end.

(* We establish that zipping preserves reduction sequences. *)

Lemma monotone_seqcat : forall s1 s2 n,
  nthred n (seqlast s1) (seqhead s2) ->
  seqn s1 <= n /\ (n <= seqnrev s2 \/ exists M, s2 = seq_unit M) ->
  stseq s1 -> stseq s2 -> monotone (seqcat s1 n s2).
Proof.
  intros s1 s2 n Hnth Hbetw Hs1 Hs2. inversion Hs1. inversion Hs2.
  dependent induction s1; dependent induction s2.
    simpl. apply monotone_cons. apply monotone_unit. simpl. left. omega.
    (* seq_unit x seq_cons *)
    simpl. apply monotone_cons.
      apply IHs2.
        simpl in Hnth. simpl. assumption.
        split.
          simpl. omega.
          destruct s2.
            right. exists l1. reflexivity.
            left.
              inversion Hbetw.
                inversion H4. unfold seqnrev in H5. fold seqnrev in H5. assumption.
                inversion H5. inversion H6.
        assumption.
        apply stseq_backwards in Hs2. assumption.
        assumption.
        inversion H2. assumption.
        inversion H1. assumption.
        inversion H2. assumption.
    inversion Hbetw.
    inversion H4.
      left. destruct s2.
        simpl in H5. simpl. assumption.
        simpl. inversion H2. simpl in H10. inversion H10.
          assumption.
          inversion H11. inversion H12.
      inversion H5. inversion H6.
    (* seq_cons x seq_unit *)
    simpl. apply monotone_cons. assumption. inversion Hbetw. left. omega.
    (* seq_cons x seq_cons *)
    simpl. apply monotone_cons. apply IHs2.
      unfold seqhead in Hnth. fold seqhead in Hnth. assumption.
      inversion Hbetw. split.
        assumption.
        inversion H4. destruct s2.
          right. exists l1. reflexivity.
          left. unfold seqnrev in H5. fold seqnrev in H5.
            unfold seqnrev. fold seqnrev. assumption.
            inversion H5. inversion H6.
      assumption.
      apply stseq_backwards in Hs2. assumption.
      assumption.
      assumption.
      inversion H1. assumption.
      inversion H2. assumption.
    left. inversion Hbetw. inversion H4.
      destruct s2.
        simpl. simpl in H5. omega.
        simpl. simpl in H5. inversion H2. simpl in H10. inversion H10.
          assumption.
          inversion H11. inversion H12.
          inversion H5. inversion H6.
Qed.

Lemma redseq_zip : forall s1 s2,
  redseq s1 -> redseq s2 -> redseq (zip s1 s2).
Proof.
  intros. induction s1; induction s2.
    (* seq_unit x seq_unit *)
    induction l; induction l0; simpl; apply redseq_unit.
    (* seq_unit x seq_cons *)
    induction l; induction l0;
      unfold zip; fold zip; fold appl; apply redseq_cons;
      first [rewrite seqlast_appl; apply nthred_concl; inversion H0; assumption |
             apply redseq_appl; inversion H0; assumption].
    (* seq_cons x seq_unit *)
    induction l; induction l0; simpl; apply redseq_cons;
      first [rewrite seqlast_appr; apply nthred_concr; inversion H; assumption |
             apply redseq_appr; inversion H; assumption].
    (* seq_cons x seq_cons *)
    simpl. apply redseq_cons.
      rewrite seqlast_seqcat. rewrite seqlast_appl.
        apply nthred_concl. inversion H0. assumption.
        apply redseq_seqcat.
          rewrite seqlast_appr. rewrite seqhead_appl.
          apply nthred_concr.
            inversion H. assumption.
            apply redseq_appr. inversion H. assumption.
          apply redseq_appl. inversion H0. assumption.
Qed.

Lemma monotone_connectives : forall s1 s2 m n M N,
  monotone (zip (seq_cons s1 m M) (seq_cons s2 n N)) ->
  radjust (seqlast s1) m <= seqnrev (appl M (seq_cons s2 n N)).
Proof.
  intros. dependent induction s2.
    simpl. simpl in H. inversion H. inversion H2.
      simpl in H4. inversion H4.
        omega.
        inversion H10. inversion H11.
    simpl in H. inversion H. simpl in IHs2. apply IHs2 in H2.
    simpl. assumption.
Qed.

Lemma monotone_zip : forall s1 s2,
  stseq s1 -> stseq s2 -> monotone (zip s1 s2).
Proof.
  intros s1 s2 Hs1 Hs2. inversion Hs1. inversion Hs2.
  dependent induction s1; dependent induction s2.
    (* seq_unit x seq_unit *)
    induction l; induction l0; apply monotone_unit.
    (* seq_unit x seq_cons *)
    simpl. apply monotone_cons.
      apply monotone_appl. inversion H2. assumption.
      destruct l; try (rewrite seqn_appl_var ||
                       rewrite seqn_appl_lam ||
                       rewrite seqn_appl_app
        ); inversion H2.
        simpl. inversion H7.
          left. assumption.
          left. inversion H8. rewrite H9. simpl. omega.
        simpl.
          assert (seqn s2 + redcount l + 1 >= seqn (appl (Lam l) s2)) by
            apply seqn_appl_lam.
          left. inversion H7.
            omega.
            inversion H9. rewrite H10. simpl. omega.
        unfold ladjust.
          assert (seqn s2 + redcount (App l1 l2) >= seqn (appl (App l1 l2) s2)) by
            apply seqn_appl_app.
          left. inversion H7.
            omega.
            inversion H9. rewrite H10. simpl. omega.
    (* seq_cons x seq_unit *)
    simpl. apply monotone_cons.
      apply monotone_appr. apply stseq_backwards in Hs1. assumption.
    destruct s1.
      simpl. left. omega.
      rewrite appr_cons. simpl.
        inversion H. inversion H7.
        inversion H0. simpl in H17.
        left. simpl. apply nthred_radjust with (n := n0). assumption.
        inversion H17.
          assumption.
          inversion H18. inversion H19.
    (* seq_cons x seq_cons *)
    simpl. apply monotone_cons.
      (* predecessor sequence *)
      apply monotone_seqcat.
        rewrite seqlast_appr. rewrite seqhead_appl.
          apply nthred_concr. inversion Hs1. inversion H3. assumption.
        split.
          destruct s1.
            simpl. omega.
            simpl. inversion Hs1. inversion H3. inversion H9.
              apply nthred_radjust with (n := n1).
                assumption.
                inversion H4. simpl in H19. inversion H19.
                  assumption.
                  inversion H20. inversion H21.
          apply stseq_appl with (M := l) in Hs1. inversion Hs1. inversion H4.
            destruct s2. simpl.
              right. exists (App l l1). reflexivity.
              left. apply monotone_connectives.
                apply IHs2.
                  unfold stseq. split; assumption.
                  apply stseq_backwards in Hs2. assumption.
                  assumption.
                  assumption.
                  inversion H1. assumption.
                  inversion H2. assumption.
        apply stseq_appr. apply stseq_backwards in Hs1. assumption.
        apply stseq_appl. apply stseq_backwards in Hs2. assumption.
      (* inbetween-ness *)
      left.
      assert (redcount (seqlast (seq_cons s1 n l)) >= seqn (seq_cons s1 n l)).
      apply redcount_seqn. assumption. simpl in H3.
      inversion H0.
      assert (Hor:
        seqn (seqcat (appr (seqhead s2) s1) (radjust (seqlast s1) n) (appl l s2)) =
        radjust (seqlast s1) n \/
        seqn (seqcat (appr (seqhead s2) s1) (radjust (seqlast s1) n) (appl l s2)) =
        seqn (appl l s2)).
      apply seqn_seqcat.
      inversion Hor.
        (* left Hor branch *)
        rewrite H9. case_eq (l); case_eq (seqlast s1).
        (* l is Var *)
        intros. simpl. rewrite H11 in H3. simpl in H3. omega.
        intros. inversion H. rewrite H10 in H14. rewrite H11 in H14. inversion H14.
        intros. simpl. rewrite H11 in H3. simpl in H3. omega.
        (* l is Lam *)
        intros. simpl.
          assert (HLam: redcount l1 = redcount l) by (rewrite H11; reflexivity).
          rewrite HLam. omega.
        intros. simpl.
          assert (HLam: redcount l2 = redcount l) by (rewrite H11; reflexivity).
          rewrite HLam. omega.
        intros. simpl.
          assert (HLam: redcount l3 = redcount l) by (rewrite H11; reflexivity).
          rewrite HLam. omega.
        (* l is App *)
        intros. unfold ladjust. rewrite <- H11. unfold radjust. omega.
        intros. inversion H. rewrite H10 in H14. rewrite H11 in H14. inversion H14.
        intros. unfold ladjust. rewrite <- H11. unfold radjust. omega.
        (* right Hor branch *)
        rewrite H9. destruct l.
          (* l is Var *)
          simpl. rewrite seqn_appl_var. inversion H2.
          inversion H14.
            assumption.
            inversion H15. rewrite H16. simpl. omega.
          (* l is Lam *)
          simpl.
          assert (seqn s2 + redcount l + 1 >= seqn (appl (Lam l) s2))
            by (simpl; apply seqn_appl_lam).
          inversion H2.
          inversion H15.
            omega.
            inversion H16. rewrite H17. simpl. omega.
          (* l is App *)
          unfold ladjust.
          assert (seqn s2 + redcount (App l1 l2) >= seqn (appl (App l1 l2) s2))
            by apply seqn_appl_app.
          inversion H2.
          inversion H15.
            omega.
            inversion H16. rewrite H17. simpl. omega.
Qed.

Lemma zip_appr : forall s M,
  zip s (seq_unit M) = appr M s.
Proof. intros. induction s; induction M; induction l; reflexivity. Qed.

Lemma zip_appl : forall s M,
  zip (seq_unit M) s = appl M s.
Proof. intros. induction s; induction M; induction l; reflexivity. Qed.

Lemma zip_seqhead_right : forall s s' n M,
  seqhead (zip s (seq_cons s' n M)) = seqhead (zip s s').
Proof.
  intros. induction s; induction s'; induction M; induction l; reflexivity.
Qed.

Lemma zip_seqhead : forall s1 s2,
  seqhead (zip s1 s2) = App (seqhead s1) (seqhead s2).
Proof.
  intros. induction s1; induction s2.
    (* seq_unit x seq_unit *)
    induction l; induction l0; reflexivity.
    (* seq_unit x seq_cons *)
    induction l; induction l0;
      unfold seqhead; fold seqhead;
      unfold seqhead in IHs2; fold seqhead in IHs2;
      rewrite <- IHs2; reflexivity.
    (* seq_cons x seq_unit *)
    induction l; induction l0;
      unfold seqhead; fold seqhead;
      unfold seqhead in IHs1; fold seqhead in IHs1;
      rewrite <- IHs1; simpl; rewrite zip_appr; reflexivity.
    (* seq_cons x seq_cons *)
    unfold seqhead. fold seqhead.
    unfold seqhead in IHs1. fold seqhead in IHs1.
    unfold seqhead in IHs2. fold seqhead in IHs2.
    rewrite zip_seqhead_right in IHs1. apply IHs2 in IHs1.
    rewrite <- zip_seqhead_right with (n := n0) (M := l0) in IHs1.
    assumption.
Qed.

Lemma zip_seqlast : forall s1 s2,
  seqlast (zip s1 s2) = App (seqlast s1) (seqlast s2).
Proof.
  intros. induction s1; induction s2;
    induction l; induction l0;
    unfold seqlast; fold seqlast;
    reflexivity.
Qed.

(* This is the useful lemma about zipping standard reduction sequences. *)

Lemma zip_stseq : forall s1 s2,
  stseq s1 -> stseq s2 -> stseq (zip s1 s2).
Proof.
  intros. inversion H. inversion H0. unfold stseq. split.
    apply redseq_zip; assumption.
    apply monotone_zip; assumption.
Qed.

(** ** Proof of the standardization theorem *)

(** *** Definition 3.1, Head-reduction in application *)

Inductive hap' : lterm -> lterm -> Prop :=
  | hap'_hred : forall A B, hap' (App (Lam A) B) (subst 0 B A)
  | hap'_hreds : forall A B C, hap' A B -> hap' (App A C) (App B C).

Inductive hap : lterm -> lterm -> Prop :=
  | hap_refl : forall A, hap A A
  | hap_hred : forall A B, hap' A B -> hap A B
  | hap_trans : forall A B C, hap A B -> hap B C -> hap A C.

(** *** Definition 3.2, Standard reduction *)

Inductive st : lterm -> lterm -> Prop :=
  | st_hap : forall L x, hap L (Var x) -> st L (Var x)
  | st_hap_st_st : forall L A B C D,
      hap L (App A B) -> st A C -> st B D -> st L (App C D)
  | st_haplam_st : forall L A B,
      hap L (Lam A) -> st A B -> st L (Lam B).

(** *** Lemma 3.3 *)

(** (1) **)
Lemma hap_lstar : forall M N, hap M N -> lstar M N.
Proof.
  intros. induction H as [ M | M N | M N P].
    (* hap_refl *)
    apply lstar_refl.
    (* hap_hred *)
    apply lstar_step. unfold lmost. induction H.
      apply nthred_base.
      assert (Hadj: 0 = radjust A 0). inversion H; reflexivity. rewrite Hadj.
      apply nthred_concr. assumption.
    (* hap_trans *)
    apply lstar_trans with (y := N). apply IHhap1. apply IHhap2.
Qed.

(** (2) **)

Lemma st_stseq : forall M N, st M N ->
  exists s, seqhead s = M /\ seqlast s = N /\ stseq s.
Proof.
  intros M N Hst. induction Hst.
  (* st_hap *)
  apply hap_lstar in H. unfold lstar in H.
  apply Operators_Properties.clos_refl_trans_ind_right
    with (A := lterm) (R := lmost) (x := L) (z := (Var x)).
  exists (seq_unit (Var x)).
  split.
    reflexivity.
    split.
      reflexivity.
      apply stseq_unit.
  intros.
  inversion H1. inversion H3. inversion H5. inversion H7.
  exists (leftexpand x0 0 x1).
  split.
    apply leftexpand_seqhead.
    split.
      rewrite <- H6. apply leftexpand_seqlast.
      apply stseq_leftexpand. assumption. rewrite H4. assumption.
  assumption.
  (* st_hap_st_st *)
  apply hap_lstar in H. unfold lstar in H.
  apply Operators_Properties.clos_refl_trans_ind_right
    with (A := lterm) (R := lmost) (x := L) (z := (App A B)).
    (* step *)
    inversion IHHst1. inversion H0. inversion H2.
    inversion IHHst2. inversion H5. inversion H7.
    exists (zip x x0).
    split.
      rewrite <- H1. rewrite <- H6. apply zip_seqhead.
      split.
        rewrite <- H3. rewrite <- H8. apply zip_seqlast.
        apply zip_stseq; assumption.
    (* refl *)
    intros.
    inversion H1. inversion H3. inversion H5. inversion H7.
    exists (leftexpand x 0 x0).
    split.
      apply leftexpand_seqhead.
      split.
        rewrite <- H6. apply leftexpand_seqlast.
        apply stseq_leftexpand. assumption. rewrite H4. assumption.
    (* trans *)
    assumption.
  (* st_haplam_st *)
  apply hap_lstar in H. unfold lstar in H.
  apply Operators_Properties.clos_refl_trans_ind_right
    with (A := lterm) (R := lmost) (x := L) (z := (Lam A)).
    (* step *)
    apply stseq_lambda; assumption.
    (* refl *)
    intros.
    inversion H1. inversion H3. inversion H5. inversion H7.
    exists (leftexpand x 0 x0).
    split.
      apply leftexpand_seqhead.
      split.
        rewrite <- H6. apply leftexpand_seqlast.
        apply stseq_leftexpand. assumption. rewrite H4. assumption.
    (* trans *)
    assumption.
Qed.

(** *** Lemma 3.4 *)

(** (1) **)
Lemma st_refl : forall M, st M M.
Proof.
  intros M.
  induction M.
    apply st_hap. apply hap_refl.
    apply st_haplam_st with (A := M).
      apply hap_refl.
      assumption.
    apply st_hap_st_st with (A := M1) (B := M2).
      apply hap_refl.
      assumption.
      assumption.
Qed.

(** (2) **)
Lemma hap__app_hap : forall M N P,
  hap M N -> hap (App M P) (App N P).
Proof.
  intros. induction H.
    apply hap_refl.
    apply hap_hred. apply hap'_hreds. assumption.
    apply hap_trans with (B := App B P); assumption.
Qed.

(** (3) **)
Lemma hap_st__st : forall L M N,
  hap L M -> st M N -> st L N.
Proof.
  intros. induction H0.
    apply st_hap. apply hap_trans with (B := L0); assumption.
    apply st_hap_st_st with (A := A) (B := B).
      apply hap_trans with (B := L0); assumption.
      assumption.
      assumption.
    apply st_haplam_st with (A := A).
      apply hap_trans with (B := L0); assumption.
      assumption.
Qed.

(** (4) **)

(* We first prove [subst_hap'], after which the actual lemma is easy to show. *)

Lemma subst_hap' : forall M N P, forall n,
  hap' M N -> hap' (subst n P M) (subst n P N).
Proof.
  intros. induction H.
    (* hap'_hred *)
    simpl.
    assert (EXP: subst n P (subst 0 B A) = subst 0 (subst n P B) (subst (n+1) P A)).
      simpl. assert (T1: subst n P B = subst (n - 0) P B).
        assert (T2: n = n - 0). omega. rewrite <- T2. reflexivity.
      rewrite T1. apply subst_lemma. omega.
    rewrite EXP. apply hap'_hred.
    (* hap'_hreds *)
    apply hap'_hreds. apply IHhap'.
Qed.

Lemma hap__hap_subst : forall M N P,
  hap M N -> forall n : nat, hap (subst n P M) (subst n P N).
Proof.
  intros M N P H n. induction H.
    apply hap_refl.
    apply hap_hred. apply subst_hap'. assumption.
    apply hap_trans with (B := subst n P B); assumption.
Qed.

(* We need to do quite a bit of busywork for (5). *)

(* First, lift-independence of [hap], which is easy. *)

Lemma lift_hap' : forall M N,
  hap' M N -> forall n k, hap' (lift n k M) (lift n k N).
Proof.
  intros M N H. induction H.
    (* hap'_hred *)
    intros n k. simpl.
    rewrite lift_distr_subst.
    replace (k - 0) with k by omega.
    apply hap'_hred. omega.
    (* hap'_hreds *)
    intros n k.
    rewrite lift_app. rewrite lift_app.
    apply hap'_hreds. apply (IHhap' n).
Qed.

Lemma lift_hap : forall M N,
  hap M N -> forall n k, hap (lift n k M) (lift n k N).
Proof.
  intros. induction H.
    (* hap_refl *)
    apply hap_refl.
    (* hap_hreds *)
    apply hap_hred. apply lift_hap'. assumption.
    (* hap_trans *)
    apply hap_trans with (B := lift n k B); assumption.
Qed.

(* Second, lift-independence for [st], which is more intricate. *)

Lemma subst_to_var : forall M N i,
  subst 0 N M = Var i -> M = Var 0 /\ N = Var i \/ M = Var (i + 1).
Proof.
  intros. induction M.
    (* Var *)
    inversion H. case_eq (Compare_dec.nat_compare n 0).
      (* Eq *)
      intros nEQ0.
      rewrite nEQ0 in H1. rewrite Compare_dec.nat_compare_eq_iff in nEQ0.
      left. split.
        f_equal. assumption.
        rewrite (lift_0_ident N 0). reflexivity.
      (* Lt *)
      intro nLT0.
      rewrite <- Compare_dec.nat_compare_lt in nLT0. contradict nLT0.
      omega.
      (* Gt *)
      intro nGT0.
      rewrite nGT0 in H1. rewrite <- Compare_dec.nat_compare_gt in nGT0.
      right. f_equal. rewrite Plus.plus_comm.
      inversion H1. apply Minus.le_plus_minus. omega.
    (* Lam *)
    simpl in H. inversion H.
    (* App *)
    simpl in H. inversion H.
Qed.

Lemma subst_indist : forall i M N,
  i > 0 -> subst 0 M (Var i) = subst 0 N (Var i).
Proof.
  intros. simpl. rewrite Compare_dec.nat_compare_gt in H. rewrite H. reflexivity.
Qed.

Lemma lift_first_hap : forall M n i k,
  hap M (Var i) -> i < k -> hap (lift n k M) (Var i).
Proof.
  intros M n i k H iLTk.
  assert (Var i = lift n k (Var i)). simpl. case_eq (Compare_dec.lt_dec i k).
    (* i < k *)
    intros. reflexivity.
    (* ~ i < k *)
    intros. contradict iLTk. assumption.
  rewrite H0. apply lift_hap. assumption.
Qed.

Lemma lift_st : forall M N,
  st M N -> forall n k, st (lift n k M) (lift n k N).
Proof.
  intros M N H. dependent induction H.
    (* st_hap *)
    intros n k. simpl. case_eq (Compare_dec.lt_dec x k).
      (* i < k *)
      intros. apply st_hap. apply lift_first_hap; assumption.
      (* ~ i < k *)
      intros. apply st_hap.
      assert (FLD: Var (x + n) = lift n k (Var x)). simpl.
        case_eq (Compare_dec.lt_dec x k).
          (* x < k *)
          intros. contradiction.
          (* ~ x < k *)
          intros. reflexivity.
      rewrite FLD. apply lift_hap. assumption.
    (* st_hap_st_st *)
    intros n k. apply st_hap_st_st with (A := lift n k A) (B := lift n k B).
    rewrite <- lift_app. apply lift_hap. assumption.
    fold lift. apply IHst1.
    fold lift. apply IHst2.
    (* st_haplam_st *)
    intros n k. apply st_haplam_st with (A := lift n (k+1) A).
    rewrite <- lift_lam. apply lift_hap. assumption.
    fold lift. apply IHst.
Qed.

(** (5) **)
Lemma st_st__st_subst : forall M N P Q,
  st M N -> st P Q -> forall n, st (subst n P M) (subst n Q N).
Proof.
  intros M N P Q HMN HPQ. induction HMN.
    (* hap with Var *)
    intro n.
    assert (hap (subst n P L) (subst n P L)). apply hap_refl.
    assert (hap (subst n P L) (subst n P (Var x))).
      apply hap__hap_subst. assumption.
    apply hap_st__st with (M := subst n P (Var x)). assumption.
    simpl. case_eq (Compare_dec.nat_compare x n).
      (* Eq *)
      intro. apply lift_st. assumption.
      (* Lt *)
      intro. apply st_hap. apply hap_refl.
      (* Gt *)
      intro. apply st_hap. apply hap_refl.
    (* hap with App *)
    intro n. rewrite subst_app.
    apply st_hap_st_st with (A := subst n P A) (B := subst n P B).
    rewrite <- subst_app.
    apply hap__hap_subst.
    assumption. apply (IHHMN1 n). apply (IHHMN2 n).
    (* hap with Lam *)
    intro n.
    apply st_haplam_st with (A := subst (n+1) P A).
    rewrite <- subst_lam.
    apply hap__hap_subst.
    assumption.
    apply (IHHMN (n+1)).
Qed.

(** *** Lemma 3.5 *)

Lemma st_app__st_subst : forall L M N,
  st L (App (Lam M) N) -> st L (subst 0 N M).
Proof.
  intros. inversion H as [ | X P N' |]. inversion H4 as [ | | X' M' ].
  apply hap_st__st with (M := subst 0 N' M').
  apply hap_trans with (B := App (Lam M') N').
  apply hap_trans with (B := App P N').
    assumption.
    apply hap__app_hap. apply H7.
    apply hap_hred. apply hap'_hred.
  apply st_st__st_subst; assumption.
Qed.

(** *** Lemma 3.6 *)

Lemma st_nthred__st : forall M N i,
  nthred i M N -> forall L, st L M -> st L N.
Proof.
  intros M N i Hbet.
  induction Hbet as [A B | n A B C | n A B C | n A B].
    (* 2.1 (1) *)
    intros L Hst.
    apply st_app__st_subst. assumption.
    (* 2.1 (2) *)
    intros L Hst.
    inversion Hst as [| X A' C' |].
    apply st_hap_st_st with (A := A') (B := C').
      assumption.
      apply IHHbet. assumption.
      assumption.
    (* 2.1 (3), (4), (5) *)
    intros L Hst.
    inversion Hst as [| X A' C' |].
    apply st_hap_st_st with (A := A') (B := C').
      assumption.
      assumption.
      apply (IHHbet C'); assumption.
    (* 2.1 (6) *)
    intros L Hst.
    inversion Hst as [| | X A'].
    apply st_haplam_st with (A := A').
      assumption.
      apply (IHHbet A'). assumption.
Qed.

Lemma st_bred__st : forall L M N,
  bet M N -> st L M -> st L N.
Proof.
  intros. unfold bet in H. inversion H.
  apply st_nthred__st with (M := M) (i := x); assumption.
Qed.

(** *** Lemma 3.7 *)

Lemma betstar_st : forall M N,
  betstar M N -> st M N.
Proof.
  intros M N Hstar. induction Hstar.
    (* step *)
    intros.
    apply (st_bred__st x x y). assumption. apply st_refl.
    (* refl *)
    apply st_refl.
    (* trans *)
    apply (Operators_Properties.clos_refl_trans_ind_left lterm bet y).
      assumption.
      intros. apply (st_bred__st x y0 z0); assumption.
      assumption.
Qed.

(** *** Theorem 2.4, Standardization Theorem *)

Theorem betstar_stseq : forall M N,
  betstar M N -> exists s, seqhead s = M /\ seqlast s = N /\ stseq s.
Proof. intros. apply st_stseq. apply betstar_st. assumption. Qed.

End Standardization.
