Require Import Untyped.
Require Import Subst.
Require Import Beta.
Require Import Relation_Operators.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Lists.List.

(** Reduction Numbering (Definition 2.1) **)

(* Predicate characterising abstractions. *)

Inductive abstr : lterm -> Prop :=
  | islam : forall M, abstr (Lam M).

Example notabstr : ~ abstr (`"x").
Proof. unfold not. intro. inversion H. Qed.

(* Count the total number of redexes in a term. *)

Fixpoint redcount (M : lterm) : nat :=
  match M with
  | Var i as v => 0
  | App (Lam N) N' => (redcount N) + (redcount N') + 1
  | App N N' => (redcount N) + (redcount N')
  | Lam N => redcount N
  end.

Example countright :
  redcount (`"x") = 0 /\ redcount (`"x" $ `"z") = 0 /\ redcount ((\"x" ~> (\"y" ~> `"y" $ `"y") $ `"x") $ `"z") = 2. 
Proof.
  split.
    compute. reflexivity.
    split; compute; reflexivity.
Qed.

(* This is the predicate defined in 2.1.
   [nthred n t t'] states that [t'] is the result of reducing the [n]-th redex in [t].

   In order to simplify working with this definition, we start counting from zero.
*)

Inductive nthred : nat -> lterm -> lterm -> Prop :=
  | nthred_prim : forall A B,
      nthred 0 (App (Lam A) B) (subst 0 B A)
  | nthred_concr : forall n A B C,
      ~ abstr A -> nthred n A B -> nthred n (App A C) (App B C)
  | nthred_concrplus : forall n A B C,
      abstr A -> nthred n A B -> nthred (n+1) (App A C) (App B C)
  | nthred_concl : forall n A B C,
      ~ abstr C -> nthred n A B -> nthred (n + redcount C) (App C A) (App C B)
  | nthred_conclplus : forall n A B C,
      abstr C -> nthred n A B -> nthred (n + (redcount C) + 1) (App C A) (App C B)
  | nthred_abst : forall n A B,
      nthred n A B -> nthred n (Lam A) (Lam B).

Example prim : nthred 0 ((\"x" ~> `"x") $ `"y") (`"y").
Proof. apply nthred_prim. Qed.

Example concr : nthred 0 ((\"x" ~> `"x") $ `"y" $ `"z") (`"y" $ `"z").
Proof.
  apply nthred_concr.
  unfold not. intro. inversion H.
  apply nthred_prim.
Qed.

Example concrplus :
  nthred 1 ((\"y" ~> (\"x" ~> `"x") $ `"y") $ `"z") ((\"y" ~> `"y") $ `"z").
Proof.
  assert (M: 1 = 0 + 1) by reflexivity. rewrite M.
  apply nthred_concrplus.
    apply islam.
    apply nthred_abst. apply nthred_prim.
Qed.

Example concl :
  nthred 1 (((\"x" ~> `"x") $ `"z") $ ((\"x" ~> `"x") $ `"z")) (((\"x" ~> `"x") $ `"z") $ `"z").
Proof.
  assert (M: 1 = 0 + redcount ((\"x" ~> `"x") $ `"z")) by reflexivity. rewrite M.
  apply nthred_concl.
  unfold not. intro. inversion H.
  apply nthred_prim.
Qed.

Example conclplus :
  nthred 2 ((\"y" ~> ((\"x" ~> `"x") $ `"z")) $ ((\"x" ~> `"x") $ `"z")) ((\"y" ~> ((\"x" ~> `"x") $ `"z")) $ `"z").
Proof.
  assert (M: 2 = 0 + redcount (\"y" ~> (\"x" ~> `"x") $ `"z") + 1) by reflexivity. rewrite M.
  apply nthred_conclplus.
  apply islam.
  apply nthred_prim.
Qed.

(** Beta-reduction and left-most reduction (Definition 2.2) **)

(* The paper defines beta-reduction in terms of the [nthred] relation.
   Equivalence with the definition found in [Beta] has yet to be proven (if necessary).
*)

Definition bet (A B : lterm) : Prop := exists n : nat, nthred n A B.

Definition betstar := clos_refl_trans lterm bet.
Definition betstar_step := rt_step lterm bet.
Definition betstar_refl := rt_refl lterm bet.
Definition betstar_trans := rt_trans lterm bet.

(* Left-most reduction is simply reduction of the first redex. *)

Definition lmost (A B : lterm) : Prop := nthred 0 A B.

Definition lstar := clos_refl_trans lterm lmost.
Definition lstar_step := rt_step lterm lmost.
Definition lstar_refl := rt_refl lterm lmost.
Definition lstar_trans := rt_trans lterm lmost.

(** Standard reduction sequence (Definition 2.3) **)

Inductive seq : Type :=
  | seq_unit : lterm -> seq
  | seq_cons : seq -> nat -> lterm -> seq.

Fixpoint seqhead (s : seq) : lterm :=
  match s with
  | seq_unit A => A
  | seq_cons s _ _ => seqhead s
  end.

Fixpoint seqlast (s : seq) : lterm :=
  match s with
  | seq_unit B => B
  | seq_cons _ _ B => B
  end.

Fixpoint leftexpand (M : lterm) (n : nat) (s : seq) : seq :=
  match s with
  | seq_unit B => seq_cons (seq_unit M) n B
  | seq_cons s' m N => seq_cons (leftexpand M n s') m N
  end.

(* Extracting the head and last reduction count from a sequence. *)

Definition seqn (s: seq) : nat :=
  match s with
  | seq_unit A => 0
  | seq_cons _ n _ => n
  end.

Fixpoint seqnrev (s: seq) : nat :=
  match s with
  | seq_unit A => 0
  | seq_cons (seq_unit M) n N => n
  | seq_cons s' _ _ => seqnrev s'
  end.
(*
Lemma seqn_one
*)

Fixpoint seqcat (s1 : seq) (n : nat) (s2 : seq) : seq :=
  match s2 with
  | seq_unit B => seq_cons s1 n B
  | seq_cons s2' m B => seq_cons (seqcat s1 n s2') m B
  end.

Lemma seqcat_leftexpand : forall M n s,
  seqcat (seq_unit M) n s = leftexpand M n s.
Proof. intros. induction s. reflexivity. simpl. rewrite IHs. reflexivity. Qed.

Inductive redseq : seq -> Prop :=
  | redseq_unit : forall A, redseq (seq_unit A)
  | redseq_cons : forall s n A,
                    nthred n (seqlast s) A ->
                    redseq s ->
                    redseq (seq_cons s n A).

Example lmost_redseq : forall A B,
  redseq (seq_cons (seq_unit (App (Lam A) B)) 0 (subst 0 B A)).
Proof. intros. apply redseq_cons. simpl. apply nthred_prim. apply redseq_unit. Qed.

Inductive monotone : seq -> Prop :=
  | monotone_unit : forall A, monotone (seq_unit A)
  | monotone_cons : forall n A s, monotone s -> n >= seqn s -> monotone (seq_cons s n A).

Definition stseq (s : seq) : Prop := redseq s /\ monotone s.

Lemma stseq_backwards : forall M n s, stseq (seq_cons s n M) -> stseq s.
Proof.
  intros. unfold stseq in H. inversion H. inversion H0. inversion H1.
  unfold stseq. split; assumption.
Qed.

Lemma leftexpand_seqhead : forall M n s, seqhead (leftexpand M n s) = M.
Proof. intros. induction s. reflexivity. simpl. apply IHs. Qed.

Lemma leftexpand_seqlast : forall M n s, seqlast (leftexpand M n s) = seqlast s.
Proof. intros. induction s. reflexivity. reflexivity. Qed.

Lemma leftexpand_bound : forall M s, seqn (leftexpand M 0 s) = seqn s.
Proof. intros. induction s. simpl. omega. simpl. omega. Qed.

Lemma leftexpand_redseq : forall M n s,
  redseq s -> nthred n M (seqhead s) -> redseq (leftexpand M n s).
Proof.
  intros. induction s.
    simpl. apply redseq_cons. simpl. simpl in H0. assumption. apply redseq_unit.
    simpl. apply redseq_cons.
      inversion H. rewrite leftexpand_seqlast. assumption.
      apply IHs. inversion H. assumption. simpl in H0. assumption.
Qed.

(* TODO Do I still need this one? *)

Lemma seqnrev_redseq : forall s, redseq s -> seqnrev s >= 0.
Proof.
  intros. induction s.
    simpl. omega.
    inversion H. apply IHs in H4. destruct s.
      simpl. omega.
      unfold seqnrev. fold seqnrev. apply H4.
Qed.

Example seqnrev_sanity1 : forall A B C D i j k,
  seqnrev (seq_cons (seq_cons (seq_cons (seq_unit A) i B) j C) k D) = i.
Proof. reflexivity. Qed.

Example seqnrev_sanity2 : forall A, seqnrev (seq_unit A) = 0.
Proof. reflexivity. Qed.

Example seqnrev_sanity3 : forall A B i, seqnrev (seq_cons (seq_unit A) i B) = i.
Proof. reflexivity. Qed.

Example seqnrev_sanity4 : forall A B C i j,
  seqnrev (seq_cons (seq_cons (seq_unit A) i B) j C) = i.
Proof. reflexivity. Qed.

Lemma seqnrev_seq_cons : forall s n M,
  seqnrev (seq_cons s n M) >= seqnrev s.
Proof.
  intros. induction s.
    simpl. omega.
    destruct s. simpl. omega. simpl. omega.
Qed.

Lemma monotone_seqnrev : forall s n M,
  monotone s -> (exists N, s = seq_unit N) \/ seqnrev (seq_cons s n M) = seqnrev s.
Proof.
  intros. induction s.
    left. exists l. reflexivity.
    inversion H. apply IHs in H2. inversion H2.
      inversion H5. right. rewrite H6. reflexivity.
      right. simpl. reflexivity.
Qed.

Lemma monotone_seqn : forall s n M,
  monotone s -> seqn (leftexpand M n s) = seqn s \/ exists N, s = seq_unit N.
Proof. Admitted.

Lemma leftexpand_monotone_gen : forall M n s,
  monotone s -> (n <= (seqnrev s) \/ exists N, s = seq_unit N) -> monotone (leftexpand M n s).
Proof.
  intros. induction s.
  (* seq_unit *)
  simpl. apply monotone_cons. apply monotone_unit. simpl. omega.
  (* seq_cons *)
  simpl. apply monotone_cons. apply IHs.
    inversion H. assumption.
    inversion H0. destruct s.
      right. exists l0. reflexivity.
      left. unfold seqnrev in H1. unfold seqnrev. assumption.
      inversion H1. inversion H2. inversion H.
      assert (HE: seqn (leftexpand M n s) = seqn s \/ exists N, s = seq_unit N).
        apply monotone_seqn. assumption.
      inversion HE.
        rewrite H6. assumption.
        inversion H6. rewrite H7. simpl. rewrite H7 in H0. simpl in H0. inversion H0.
          omega.
          inversion H8. inversion H9.
Qed.

Lemma leftexpand_monotone : forall M s, monotone s -> monotone (leftexpand M 0 s).
Proof. intros. apply leftexpand_monotone_gen. assumption. left. omega. Qed.

Lemma stseq_leftexpand : forall M s,
  stseq s -> lmost M (seqhead s) -> stseq (leftexpand M 0 s).
Proof.
  intros M s Hstseq Hlmost. induction s.
    simpl. unfold stseq.
    split.
      apply redseq_cons. unfold lmost in Hlmost. simpl in Hlmost. simpl. assumption.
      apply redseq_unit.
    inversion Hstseq. apply monotone_cons. apply monotone_unit. simpl. omega.
    simpl. unfold stseq.
    split.
      apply redseq_cons. unfold lmost in Hlmost. rewrite leftexpand_seqlast.
        unfold stseq in Hstseq. inversion Hstseq. inversion H. assumption.
      apply IHs.
        apply (stseq_backwards l n s). assumption.
        simpl in Hlmost. assumption. apply monotone_cons.
          apply leftexpand_monotone. inversion Hstseq.
          apply stseq_backwards in Hstseq. unfold stseq in Hstseq. inversion Hstseq. assumption. inversion Hstseq. inversion H0. rewrite leftexpand_bound. omega.
Qed.

Lemma seqlast_seqcat : forall s1 s2 n,
  seqlast (seqcat s1 n s2) = seqlast s2.
Proof. intros. induction s1; induction s2; reflexivity. Qed.

Lemma stseq_seqcat : forall s1 s2 n,
  nthred n (seqlast s1) (seqhead s2) ->
  n >= seqn s1 ->
  n <= seqnrev s2 ->
  stseq s1 ->
  stseq s2 ->
  stseq (seqcat s1 n s2).
Proof.
  intros. induction s1; induction s2.
    (* seq_unit, seq_unit *)
    simpl. unfold stseq.
    split.
      apply redseq_cons. simpl in H. simpl. assumption.
      inversion H2. assumption.
      apply monotone_cons. inversion H2. assumption. assumption.
    (* seq_unit, seq_cons *)
    simpl. unfold stseq.
      split.
        apply redseq_cons. rewrite seqlast_seqcat.
          inversion H3. inversion H4. assumption.
        rewrite seqcat_leftexpand. simpl in H. apply leftexpand_redseq.
          inversion H3. inversion H4. assumption.
          assumption.
        apply monotone_cons. rewrite seqcat_leftexpand.
          (* --- *)
          destruct s2.
            simpl. apply monotone_cons. apply monotone_unit. assumption.
            simpl. apply monotone_cons. inversion H3.
              inversion H5. inversion H8. simpl in H. simpl in H0.
              apply leftexpand_monotone_gen. assumption. (* TODO Not quite yet *)
Admitted.

(*
Lemma stseq_parallel : forall A B C D,
  (exists s : seq, seqhead s = A /\ seqlast s = C /\ stseq s)
  -> (exists s : seq, seqhead s = B /\ seqlast s = D /\ stseq s)
  -> exists s : seq, seqhead s = App A B /\ seqlast s = App C D /\ stseq s.
Proof.
  intros. inversion H. inversion H0.
  induction x; induction x0.
    inversion H1. inversion H4.
    inversion H2. inversion H8.
    assert (HAC: A = C). rewrite <- H5. rewrite <- H3. reflexivity.
    assert (HBD: B = D). rewrite <- H7. rewrite <- H9. reflexivity.
    rewrite HAC. rewrite HBD.
    exists (seq_unit (App C D)).
    split.
      reflexivity.
      split.
        reflexivity.
        unfold stseq. split. apply redseq_unit. apply monotone_unit.
    (* first step for x0 *)
    apply IHx0.
    simpl in H2. inversion H2. inversion H4.
    split.
      assumption.
      split.
        (* TODO ???*) admit.
      apply stseq_backwards in H6. assumption.
    (* second step for IHx *)
    apply IHx. inversion H1. inversion H4. simpl in H3.
    split.
      assumption.
      split.
        simpl in H5.
        admit.
      apply (stseq_backwards l n x). assumption.
    (* last thingy *)
    apply IHx. inversion H1. inversion H4. simpl in H3. simpl in H5.
      split.
        assumption.
        split.
          admit.
        apply (stseq_backwards l n x). assumption.
Admitted.
*)

(* This lemma helps concisely eliminating the common goal of a one-term
   reduction sequence being standard. *)

Lemma stseq_unit : forall M, stseq (seq_unit M).
Proof. intros. unfold stseq. split. apply redseq_unit. apply monotone_unit. Qed.

(* Wrap all members of a reduction sequence in lambdas. *)

Fixpoint lambdize (s : seq) : seq :=
  match s with
  | seq_unit A => seq_unit (Lam A)
  | seq_cons s n B => seq_cons (lambdize s) n (Lam B)
  end.

Fixpoint appl (M : lterm) (s : seq) : seq :=
  match M, s with
  | _, seq_unit A => seq_unit (App M A)
  | Lam M', seq_cons s n B => seq_cons (appl M s) (n + redcount M + 1) (App M B)
  | _, seq_cons s n B => seq_cons (appl M s) (n + redcount M) (App M B)
  end.

Fixpoint appr (M : lterm) (s : seq) : seq :=
  match s with
  | seq_unit A => seq_unit (App A M)
  | seq_cons s n B => seq_cons (appr M s) n (App B M)
  end.

Lemma seqhead_appl : forall s M, seqhead (appl M s) = App M (seqhead s).
Proof.
  intros. induction s; induction M.
    reflexivity. reflexivity. reflexivity.
    simpl. apply IHs. simpl. apply IHs. simpl. apply IHs.
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

Lemma seqn_appr : forall s M, seqn s = seqn (appr M s).
Proof. intros. induction s; induction M; simpl; omega. Qed.


Lemma appl_cons_var : forall s n M x,
  appl (Var x) (seq_cons s n M) = seq_cons (appl (Var x) s) n (App (Var x) M).
Proof. intros. simpl. assert (P0: n = n + 0) by omega. rewrite <- P0. reflexivity. Qed.

Lemma seqnrev_appl_var : forall s x, seqnrev s = seqnrev (appl (Var x) s).
Proof.
  intros. induction s.
    (* seq_unit *)
    simpl. reflexivity.
    (* seq_cons *)
    rewrite appl_cons_var. unfold seqnrev. fold seqnrev. rewrite IHs.
    case (s). simpl. reflexivity. simpl. reflexivity.
Qed.

Lemma seqnrev_ge_zero : forall s, seqnrev s >= 0.
Proof. intros. induction s; induction l; omega. Qed.

Lemma seqn_ge_zero : forall s, seqn s >= 0.
Proof. intros. induction s; induction l; omega. Qed.

Lemma monotone_seqcat : forall s1 s2 n,
  monotone s1 -> monotone s2 -> seqn s1 <= n <= seqnrev s2 -> monotone (seqcat s1 n s2).
Proof.
  intros. induction s1; induction s2.
    simpl. apply monotone_cons. assumption. simpl. omega.
    simpl. apply monotone_cons. apply IHs2.
      inversion H0. assumption.
      simpl.
      split.
        omega. inversion H1.
          assert (HE: (exists N, s2 = seq_unit N) \/ seqnrev (seq_cons s2 n0 l0) = seqnrev s2).
            apply monotone_seqnrev. inversion H0. assumption.
          inversion HE.
            inversion H4. rewrite H5. simpl. rewrite H5 in H3. simpl in H3.
Admitted.


Lemma monotone_appl : forall s M, monotone s -> monotone (appl M s).
Proof.
  intros. induction s; induction M.
    apply monotone_unit. apply monotone_unit. apply monotone_unit.
    simpl. apply monotone_cons.
      apply IHs. inversion H. assumption.
      inversion H. rewrite seqn_appl_var. omega.
    simpl. apply monotone_cons.
      apply IHs. inversion H. assumption.
      inversion H. assert (seqn s + redcount M + 1 >= seqn (appl (Lam M) s)).
        apply seqn_appl_lam. omega.
    simpl. apply monotone_cons.
      apply IHs. inversion H. assumption. simpl. fold redcount. case_eq (M1).
        (* Var *)
        intros.
        assert (E: redcount (Var n0) + redcount M2 = redcount (App (Var n0) M2)).
        reflexivity. rewrite E. inversion H.
        assert (seqn s + redcount (App (Var n0) M2) >= seqn (appl (App (Var n0) M2) s)).
        apply seqn_appl_app. omega.
        (* Lam *)
        intros.
        assert (E: redcount l0 + redcount M2 + 1 = redcount (App (Lam l0) M2)).
        reflexivity. rewrite E. inversion H.
        assert (seqn s + redcount (App (Lam l0) M2) >= seqn (appl (App (Lam l0) M2) s)).
        apply seqn_appl_app. omega.
        (* App *)
        intros.
        assert (E: redcount (App l0 l1) + redcount M2 = redcount (App (App l0 l1) M2)).            reflexivity. rewrite E. inversion H.
        assert (seqn s + redcount (App (App l0 l1) M2) >= seqn (appl (App (App l0 l1) M2) s)).
        apply seqn_appl_app. omega.
Qed.

Lemma monotone_appr : forall s M, monotone s -> monotone (appr M s).
Proof.
  intros. induction s; induction M.
    apply monotone_unit. apply monotone_unit. apply monotone_unit.
    simpl. apply monotone_cons.
      apply IHs. inversion H. assumption.
      inversion H. rewrite <- (seqn_appr s (Var n0)). assumption.
    simpl. apply monotone_cons.
      apply IHs. inversion H. assumption.
      inversion H. rewrite <- (seqn_appr s (Lam M)). assumption.
    simpl. apply monotone_cons.
      apply IHs. inversion H. assumption.
      inversion H. rewrite <- (seqn_appr s (App M1 M2)). assumption.
Qed.

Lemma stseq_appl : forall s M, stseq s -> stseq (appl M s).
Proof.
  intros. inversion H. induction s; induction M.
    (* seq_unit *)
    simpl. apply stseq_unit.
    simpl. apply stseq_unit.
    simpl. apply stseq_unit.
    (* seq_cons, Var *)
    unfold stseq.
    split.
      simpl. apply redseq_cons.
        rewrite seqlast_appl.
        assert (R0: 0 = redcount (Var n0)) by reflexivity. rewrite R0.
        inversion H0.
        apply nthred_concl.
          unfold not. intro. inversion H7.
          assumption.
        apply IHs. apply (stseq_backwards l n s). assumption.
        inversion H0. assumption.
        inversion H1. assumption.
      apply monotone_appl. assumption.
    (* seq_cons, Lam *)
    unfold stseq.
    split. simpl.
      apply redseq_cons.
        rewrite seqlast_appl.
        inversion H0.
        assert (HC: redcount M = redcount (Lam M)) by reflexivity.
        rewrite HC. apply nthred_conclplus. apply islam. assumption.
        apply IHs. apply (stseq_backwards l n s). assumption.
        inversion H0. assumption.
        inversion H1. assumption.
      apply monotone_appl. assumption.
    (* seq_cons, App *)
    unfold stseq.
    split.
      unfold appl. apply redseq_cons.
        rewrite seqlast_appl.
        inversion H0.
        apply nthred_concl. unfold not. intro. inversion H7.
        assumption.
        apply IHs. apply (stseq_backwards l n s). assumption.
        inversion H0. assumption.
        inversion H1. assumption.
      apply monotone_appl. assumption.
Qed.

Lemma stseq_appr : forall s M, stseq s -> stseq (appr M s).
Proof. Admitted.

Definition zipadj (M : lterm) (n : nat) :=
  match M with
  | Var _ => n
  | Lam _ => n + 1
  | App _ _ => n
  end.

Definition zip (s1 : seq) (s2 : seq) : seq :=
  match s1, s2 with
  | seq_unit M, _ => appl M s2
  | seq_cons s1' m M, _ =>
      seqcat (appr (seqhead s2) s1') (zipadj (seqlast s1') m) (appl M s2)
  end.

Section Zipping.

Variables A B C D : lterm.

Compute (zip (seq_unit A) (seq_unit B)).

Compute (zip (seq_cons (seq_unit A) 1 B) (seq_unit C)).

Compute (zip (seq_cons (seq_unit A) 11 B) (seq_cons (seq_unit C) 12 D)).

Example foobar' : stseq (seq_cons (seq_unit (App (Lam (Var 0)) (Lam (Var 0)))) 0 (Lam (Var 0))).
Proof.
  simpl. unfold stseq.
  split.
    apply redseq_cons. simpl. apply nthred_prim.
    apply redseq_unit.
  apply monotone_cons. apply monotone_unit. simpl. omega.
Qed.

Example foobar : stseq (zip (seq_cons (seq_unit (App (Lam (Var 0)) (Lam (Var 0)))) 0 (Lam (Var 0))) (seq_unit (Lam (Var 0)))).
Proof.
  simpl. unfold stseq.
  split.
    apply redseq_cons. simpl.
      apply nthred_concr.
        unfold not. intro. inversion H.
        simpl. apply nthred_prim.
      apply redseq_unit.
    apply monotone_cons.
      apply monotone_unit.
      simpl. omega.
Qed.

Example barfoo : stseq (zip (seq_unit (Lam (Var 0))) (seq_cons (seq_unit (App (Lam (Var 0)) (Lam (Var 0)))) 0 (Lam (Var 0)))).
Proof.
  simpl. unfold stseq.
  split.
    apply redseq_cons. simpl.
      assert (0 + redcount (Lam (Var 0)) + 1 = 1). reflexivity.
      rewrite <- H. apply nthred_conclplus. apply islam.
      apply nthred_prim.
      apply redseq_unit.
    apply monotone_cons.
      apply monotone_unit.
      simpl. omega.
Qed.

End Zipping.

Lemma monotone_zip : forall s1 s2,
  monotone s1 -> monotone s2 -> monotone (zip s1 s2).
Proof.
(* --- *)
  intros. induction s1; induction s2.
    induction l; induction l0.
      apply monotone_unit. apply monotone_unit. apply monotone_unit.
      apply monotone_unit. apply monotone_unit. apply monotone_unit.
      apply monotone_unit. apply monotone_unit. apply monotone_unit.
    unfold zip. apply monotone_appl. assumption.
    induction l; induction l0.
      simpl. apply monotone_cons.
        apply monotone_appr. inversion H. assumption.
        inversion H. rewrite <- seqn_appr. unfold zipadj.
        case_eq (seqlast s1).
          intros. assumption. intros. omega. intros. assumption.
      simpl. apply monotone_cons.
        apply monotone_appr. inversion H. assumption.
        inversion H. rewrite <- seqn_appr. unfold zipadj.
        case_eq (seqlast s1).
          intros. assumption. intros. omega. intros. assumption.
      simpl. apply monotone_cons.
        apply monotone_appr. inversion H. assumption.
        inversion H. rewrite <- seqn_appr. unfold zipadj.
        case_eq (seqlast s1).
          intros. assumption. intros. omega. intros. assumption.
      simpl. apply monotone_cons.
        apply monotone_appr. inversion H. assumption.
        inversion H. rewrite <- seqn_appr. unfold zipadj.
        case_eq (seqlast s1).
          intros. assumption. intros. omega. intros. assumption.
      simpl. apply monotone_cons.
        apply monotone_appr. inversion H. assumption.
        inversion H. rewrite <- seqn_appr. unfold zipadj.
        case_eq (seqlast s1).
          intros. assumption. intros. omega. intros. assumption.
      simpl. apply monotone_cons.
        apply monotone_appr. inversion H. assumption.
        inversion H. rewrite <- seqn_appr. unfold zipadj.
        case_eq (seqlast s1).
          intros. assumption. intros. omega. intros. assumption.
      simpl. apply monotone_cons.
        apply monotone_appr. inversion H. assumption.
        inversion H. rewrite <- seqn_appr. unfold zipadj.
        case_eq (seqlast s1).
          intros. assumption. intros. omega. intros. assumption.
      simpl. apply monotone_cons.
        apply monotone_appr. inversion H. assumption.
        inversion H. rewrite <- seqn_appr. unfold zipadj.
        case_eq (seqlast s1).
          intros. assumption. intros. omega. intros. assumption.
      simpl. apply monotone_cons.
        apply monotone_appr. inversion H. assumption.
        inversion H. rewrite <- seqn_appr. unfold zipadj.
        case_eq (seqlast s1).
          intros. assumption. intros. omega. intros. assumption.
      unfold zip.
      apply monotone_seqcat.
      apply monotone_appr.
        inversion H. assumption.
      apply monotone_appl. assumption.
      inversion H. inversion H0.
      (* Can we somehow get n0 into the mix? *)
      unfold seqhead. fold seqhead. unfold zipadj.
      case_eq (seqlast s1).
        intros.
          rewrite <- seqn_appr. split. omega. destruct l.
          rewrite <- seqnrev_appl_var.

Lemma zip_stseq : forall s1 s2,
  stseq s1 -> stseq s2 -> stseq (zip s1 s2).
Proof.
  intros. induction s1; induction s2.
    (* seq_unit, seq_unit *)
    unfold stseq. induction l; induction l0.
      split. apply redseq_unit. apply monotone_unit.
      split. apply redseq_unit. apply monotone_unit.
      split. apply redseq_unit. apply monotone_unit.
      split. apply redseq_unit. apply monotone_unit.
      split. apply redseq_unit. apply monotone_unit.
      split. apply redseq_unit. apply monotone_unit.
      split. apply redseq_unit. apply monotone_unit.
      split. apply redseq_unit. apply monotone_unit.
      split. apply redseq_unit. apply monotone_unit.
   (* seq_unit, seq_cons *)
   unfold stseq. induction l; induction l0.
     split.
       simpl. apply redseq_cons.
         assert (R0: 0 = redcount (Var n0)) by reflexivity. rewrite R0.
         rewrite seqlast_appl.
         apply nthred_concl.
           unfold not. intro A. inversion A.
           inversion H0. inversion H1. assumption.
         apply stseq_appl. unfold stseq.
         split.
           inversion H0. inversion H1. assumption.
           inversion H0. inversion H2. assumption.
       simpl. apply monotone_cons. apply monotone_appl.
         
         

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
        apply nthred_abst. assumption.
        inversion H0. apply stseq_backwards in H. apply IHs in H.
        inversion H. assumption. assumption. inversion H. assumption.
      apply monotone_cons. inversion H. inversion H3. apply stseq_backwards in H.
        apply IHs in H. inversion H. assumption. inversion H. assumption. assumption.
      rewrite seqn_lambdize. inversion H1. assumption.
Qed.

Lemma stseq_lambda : forall A B,
  (exists s : seq, seqhead s = A /\ seqlast s = B /\ stseq s) ->
   exists s : seq, seqhead s = (Lam A) /\ seqlast s = (Lam B) /\ stseq s.
Proof.
  intros. inversion H. induction x.
    (* seq_unit *)
    inversion H0. inversion H2. simpl in H1. simpl in H3. rewrite <- H1. rewrite <- H3.
    exists (seq_unit (Lam l)).
    split.
      reflexivity.
      split.
        reflexivity.
        unfold stseq.
        split. apply redseq_unit. apply monotone_unit.
    (* seq_cons *)
    inversion H.
    exists (lambdize x0). inversion H1. inversion H3.
    split.
      rewrite seqhead_lambdize. f_equal. assumption.
      split.
        rewrite seqlast_lambdize. f_equal. assumption.
        apply stseq_lambdize. assumption.
Qed.

(** Head-reduction in application (Definition 3.1) **)

Inductive hap' : lterm -> lterm -> Prop :=
  | hap'_hred : forall A B, hap' (App (Lam A) B) (subst 0 B A)
  | hap'_hreds : forall A B C, hap' A B -> hap' (App A C) (App B C).

Inductive hap : lterm -> lterm -> Prop :=
  | hap_refl : forall A, hap A A
  | hap_hred : forall A B, hap' A B -> hap A B
  | hap_trans : forall A B C, hap A B -> hap B C -> hap A C.

(** Standard reduction (Definition 3.2) **)

Inductive st : lterm -> lterm -> Prop :=
  | st_hap : forall L x, hap L (Var x) -> st L (Var x)
  | st_hap_st_st : forall L A B C D,
      hap L (App A B) -> st A C -> st B D -> st L (App C D)
  | st_haplam_st : forall L A B,
      hap L (Lam A) -> st A B -> st L (Lam B).

(** Lemma 3.3 **)

(* (1) *)
Lemma hap_lstar : forall M N, hap M N -> lstar M N.
Proof.
  intros. induction H as [ t | t0 t1 | t1 t2 t3].
    (* hap_refl *)
    apply lstar_refl.
    (* hap_hred *)
    apply lstar_step. unfold lmost. induction H.
      apply nthred_prim.
      apply nthred_concr. unfold not. intro. induction H. inversion H0. inversion H0. assumption.
    (* hap_trans *)
    apply lstar_trans with (y := t2). apply IHhap1. apply IHhap2.
Qed.

(* (2) *)

Lemma st_stseq : forall M N, st M N ->
  exists s, seqhead s = M /\ seqlast s = N /\ stseq s.
Proof.
  intros M N Hst. induction Hst.
  (* st_hap *)
  apply hap_lstar in H. unfold lstar in H.
  apply Operators_Properties.clos_refl_trans_ind_right with (A := lterm) (R := lmost) (x := L) (z := (Var x)).
  exists (seq_unit (Var x)).
  split.
    reflexivity.
    split. reflexivity. unfold stseq. split. apply redseq_unit. apply monotone_unit.
  intros.
  inversion H1. inversion H3. inversion H5. inversion H7.
  exists (leftexpand x0 1 x1).
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
    apply stseq_parallel; assumption.
    (* refl *)
    intros.
    inversion H1. inversion H3. inversion H5. inversion H7.
    exists (leftexpand x 1 x0).
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
    exists (leftexpand x 1 x0).
    split.
      apply leftexpand_seqhead.
      split.
        rewrite <- H6. apply leftexpand_seqlast.
        apply stseq_leftexpand. assumption. rewrite H4. assumption.
    (* trans *)
    assumption.
Qed.
    
  
(***)
  exists (seq_cons x1 1 (Var x)).
  split.
    simpl. assumption.
    simpl. split.
      reflexivity.
      unfold stseq. split.
        apply redseq_cons. rewrite H6. apply H2. assumption.
        apply monotone_cons.
(***********)
  intros M N Hst. dependent induction Hst.
  (* st_hap *)
  apply hap_lstar in H. unfold lstar in H.
  induction H. unfold lmost in H.
    (* rt_step *)
    exists (seq_cons (seq_unit x0) 1 y). split.
      reflexivity.
      split. reflexivity. unfold stseq. split. apply redseq_cons. simpl. assumption.
      apply redseq_unit. apply monotone_cons. simpl. omega.
    (* rt_refl *)
    exists (seq_unit x0).
    split.
      reflexivity.
      split. reflexivity. unfold stseq. split. apply redseq_unit. apply monotone_unit.
    (* rt_trans *) (* Was x:= y *)
    apply Operators_Properties.clos_refl_trans_ind_left with (A := lterm) (R := lmost) (x := x0) (z := z).
    (* refl *)
    exists (seq_unit x0).
    split.
      reflexivity.
      split. reflexivity. unfold stseq. split. apply redseq_unit. apply monotone_unit.
    (* step or sthg *)
    intros.
    (* trans *)
    assert (clos_refl_trans lterm lmost x0 z). apply rt_trans with (y := y); assumption.
(* --- *)
    assumption.
    intros. unfold lmost in H3. inversion H2. inversion H4. inversion H6.
    exists (seq_cons x1 1 z0).
    split.
      simpl. assumption.
      split.
        reflexivity.
        unfold stseq. split.
          apply redseq_cons. rewrite H7. assumption.
        unfold stseq in H8. inversion H8. assumption.
        unfold stseq in H8. inversion H8. apply monotone_cons. (* TODO ??? *)
    assumption.
  (* st_hap_st_st *)
  apply hap_lstar in H. unfold lstar in H.
  inversion H.
Admitted.

(* apply (Operators_Properties.clos_refl_trans_ind_left lterm bet y) *)
      
    
    

(** Lemma 3.4 **)

(* (1) *)
Lemma st_refl : forall M, st M M.
Proof.
  intros M.
  induction M.
    apply st_hap. apply hap_refl.
    apply st_haplam_st with (A := M). apply hap_refl. assumption.
    apply st_hap_st_st with (A := M1) (B := M2). apply hap_refl. assumption. assumption.
Qed.

(* (2) *)
Lemma hap__app_hap : forall M N P,
  hap M N -> hap (App M P) (App N P).
Proof.
  intros. induction H.
    apply hap_refl.
    apply hap_hred. apply hap'_hreds. assumption.
    apply hap_trans with (B := App B P); assumption.
Qed.

(* (3) *)
Lemma hap_st__st : forall L M N,
  hap L M -> st M N -> st L N.
Proof.
  intros. induction H0.
    apply st_hap. apply hap_trans with (B := L0). assumption. assumption.
    apply st_hap_st_st with (A := A) (B := B).
      apply hap_trans with (B := L0); assumption.
      assumption. assumption.
    apply st_haplam_st with (A := A).
      apply hap_trans with (B := L0); assumption.
      assumption.
Qed.

(* (4) *)

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
    intros n k. rewrite lift_app. rewrite lift_app. apply hap'_hreds. apply (IHhap' n).
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

Lemma hap'_no_lhs_var : forall i M,
  ~ hap' (Var i) M.
Proof. intros. unfold not. intro H. inversion H. Qed.

Lemma hap_lefthandside_var : forall i M,
  hap (Var i) M -> M = Var i.
Proof.
  intros. dependent induction H.
    reflexivity.
    contradict H. apply hap'_no_lhs_var.
    apply IHhap2. assumption.
Qed.

Example lift_first_hap_ex1 : hap (lift 4 6 (App (Lam (Var 0)) (Var 3))) (Var 3).
Proof. simpl. apply hap_hred. apply hap'_hred. Qed.

Example lift_first_hap_ex2 :
  hap
    (lift 4 4 ((App (App (Lam (Var 0)) (Lam (Var 4))) (Var 7))))
    (Var 3).
Proof.
  simpl.
  apply hap_trans with (B := App (Lam (Var 4)) (Var 11)).
  apply hap_hred.
    apply hap'_hreds. apply hap'_hred.
    assert (Var 3 = subst 0 (Var 11) (Var 4)). reflexivity. rewrite H.
    apply hap_hred. apply hap'_hred.
Qed.

Lemma subst_to_var : forall M N i,
  subst 0 N M = Var i -> M = Var 0 /\ N = Var i \/ M = Var (i + 1).
Proof.
  intros. induction M.
    (* Var *)
    inversion H. case_eq (Compare_dec.nat_compare n 0).
      (* Eq *)
      intros nEQ0. rewrite nEQ0 in H1. rewrite Compare_dec.nat_compare_eq_iff in nEQ0.
      left. split.
        f_equal. assumption.
        rewrite (lift_0_ident N 0). reflexivity.
      (* Lt *)
      intro nLT0. rewrite <- Compare_dec.nat_compare_lt in nLT0. contradict nLT0. omega.
      (* Gt *)
      intro nGT0. rewrite nGT0 in H1. rewrite <- Compare_dec.nat_compare_gt in nGT0.
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

(* We need to establish that abstractions can appear on the left side of hap
   only due to the reflexive rule.
*)

Lemma not_hap'_lam_var : forall M i, ~ hap' (Lam M) i.
Proof. unfold not. intros. dependent induction H. Qed.

Lemma not_hap_lam : forall M N, N <> Lam M -> ~ hap (Lam M) N.
Proof.
  unfold not. intros.
  dependent induction H0.
    assert (ID: Lam M = Lam M) by reflexivity. apply H in ID. assumption.
    contradict H0. apply not_hap'_lam_var.
    apply IHhap2 in H. assumption. apply NNPP in IHhap1. assumption.
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
        case_eq (Compare_dec.lt_dec x k). intros. contradiction. intros. reflexivity.
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

(* (5) *)
Lemma st_st__st_subst : forall M N P Q,
  st M N -> st P Q -> forall n, st (subst n P M) (subst n Q N).
Proof.
  intros M N P Q HMN HPQ. induction HMN.
    (* hap with Var *)
    intro n.
    assert (hap (subst n P L) (subst n P L)). apply hap_refl.
    assert (hap (subst n P L) (subst n P (Var x))). apply hap__hap_subst. assumption.
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

(* Lemma 3.5 *)

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

(* Lemma 3.6 *)

Lemma st_nthred__st : forall M N i,
  nthred i M N -> forall L, st L M -> st L N.
Proof.
  intros M N i Hbet.
  induction Hbet as [A B | n A B C | n A B C | n A B C | n A B C | n A B].
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
    (* 2.1 (3) *)
    intros L Hst.
    inversion Hst as [| X A' C' |].
    apply st_hap_st_st with (A := A') (B := C').
      assumption.
      apply (IHHbet A'); assumption.
      assumption.
    (* 2.1 (4) *)
    intros L Hst.
    inversion Hst as [| X A' C' |].
    apply st_hap_st_st with (A := A') (B := C').
      assumption.
      assumption.
      apply (IHHbet C'); assumption.
    (* 2.1 (5) *)
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

(* Lemma 3.7 *)

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