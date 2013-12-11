Require Export Untyped.
Require Import Omega.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Plus.
Require Import Coq.Arith.Lt.
Require Import Omega.

(** (l)ift (t)erms below the (b)ound by some (l)evel **)
Fixpoint lift (l: nat) (b: nat) (t: lterm) : lterm :=
  match t with
      | Var i as v =>  if (lt_dec i b) then v else Var (i+l)
      | App m n => App (lift l b m) (lift l b n)
      | Lam t => Lam (lift l (b+1) t)
  end.

(** Substitute the variable with index `v` by `r` in the term `t` **)
Fixpoint subst (v: nat) (r: lterm) (t: lterm) : lterm :=
  match t with
      | Var i =>  match (nat_compare i v) with
                           | Lt => Var i
                           | Eq => lift v 0 r
                           | Gt => Var (i - 1)
                  end
      | App m n => App (subst v r m) (subst v r n)
      | Lam m => Lam (subst (v+1) r m)
  end.


(** The following lemmas are described in Berghofer and Urban, who
    seem to trace down these due to Huet
*)

Lemma lift_fuse:
  forall (N: lterm) (i j n m: nat),
    i <= j <= i + m -> lift n j (lift m i N) = lift (n+m) i N.
Proof.
  induction N as [k | N1 N2 | N1].
    (* N := Var k *)
    intros. simpl. case_eq (lt_dec k i).
      (* k < i *)
      intros. simpl. assert (k < j).
          apply lt_le_trans with i. assumption. apply H.
          destruct (lt_dec k j). reflexivity. contradict H1. auto.
      (* k >= i *)
      intros. simpl.
          destruct (lt_dec (k+m) j). contradict l. omega. apply f_equal.
          omega.
    (* N := Lam .. *)
    intros. simpl. apply f_equal. rewrite N2. reflexivity. omega.
    (* N := App .. .. *)
    intros. simpl. rewrite IHN1. rewrite IHN2. auto. auto. auto.
Qed.

Lemma lift_lem2:
  forall (N L: lterm) (i j k: nat),
  k <= j -> lift i k (subst j L N) = subst (j+i) L (lift i k N).
Proof.
  induction N as [v | N' | N1 ].
    (* N := Var v *)
    intros. simpl. case_eq (nat_compare v j).
      (* v Eq j *)
      intros. apply nat_compare_eq in H0. rewrite lift_fuse.
      destruct (lt_dec v k).
        (* v < k *)
        simpl. case_eq (nat_compare v (j + i)).
          (* Eq *)
          rewrite plus_comm. reflexivity.
          (* Lt *)
          contradict l. omega.
          (* Gt *)
          intros. apply nat_compare_gt in H1. contradict H1. omega.
        (* ~ v < k *)
        simpl. case_eq (nat_compare (v+i) (j+i)).
          (* Eq *)
          intros. rewrite plus_comm. reflexivity.
          (* Lt *)
          intros. apply nat_compare_lt in H1. contradict H1. omega.
          (* Gt *)
          intros. apply nat_compare_gt in H1. contradict H1. omega.
        split. omega. omega.
      (* v Lt j *)
      intros. apply nat_compare_lt in H0. destruct (lt_dec v k).
        (* v < k *)
        simpl. destruct (lt_dec v k).
          (* v < k *)
          case_eq (nat_compare v (j + i)).
            (* Eq *)
            intros. apply nat_compare_eq in H1. contradict H0. omega.
            (* Lt *)
            intros. reflexivity.
            (* Gt *)
            intros. apply nat_compare_gt in H1. contradict H1. omega.
          (* ~ v < k *)
          contradiction.
        (* ~ v < k *)
        simpl. destruct (lt_dec v k).
          (* v < k *)
          contradiction.
          (* ~ v < k *)
          case_eq (nat_compare (v+i) (j+i)).
            (* Eq *)
            intros. apply nat_compare_eq in H1. contradict H0. omega.
            (* Lt *)
            intros. reflexivity.
            (* Gt *)
            intros. apply nat_compare_gt in H1. contradict H0. omega.
      (* v Gt j *)
      intros. apply nat_compare_gt in H0. simpl. destruct (lt_dec (v - 1) k).
        (* v - 1 < k *)
        contradict l. omega.
        (* ~ v - 1 < k *)
        destruct (lt_dec v k).
          (* v < k *)
          contradict l. omega.
          (* ~ v < k *)
          simpl. case_eq (nat_compare (v + i) (j + i)).
            (* Eq *)
            intros. apply nat_compare_eq in H1. contradict H0. omega.
            (* Lt *)
            intros. apply nat_compare_lt in H1. contradict H0. omega.
            (* Gt *)
            intros. apply nat_compare_gt in H1. f_equal. omega.
    (* N := Lam N' *)
    intros. simpl. f_equal.
    assert (U: j + 1 + i = j + i + 1). omega. rewrite <- U.
    apply (IHN' L i (j+1) (k+1)). omega.
    (* N := App N1 N2 *)
    intros. simpl. f_equal.
    apply IHN1. assumption.
    apply IHN2. assumption.
Qed.

Lemma lift_lem3:
  forall (L P: lterm) (i j k: nat),
  k <= i < k + (j + 1) -> subst i P (lift (j+1) k L) = lift j k L.
Proof.
  intro L. induction L.
  intros. simpl. destruct (lt_dec n k).
    intros. simpl. assert (n < i). apply lt_le_trans with k. assumption. apply H.
    apply nat_compare_lt in H0. rewrite H0. reflexivity.

    simpl. apply not_lt in n0. assert (i < n + (j + 1)). omega.
     apply nat_compare_gt in H0. rewrite H0. apply f_equal. omega.

  intros. simpl. apply f_equal. apply IHL. omega.
  intros. simpl. rewrite IHL1. rewrite IHL2. reflexivity.
  auto. auto.
Qed.

Lemma var_subst_lemma: forall (i j n: nat), forall (N L: lterm),
   (i <= j) ->
       subst j L (subst i N (Var n)) =
                 subst i (subst (j-i) L N) (subst (j+1) L (Var n)).
Proof.
  intros. simpl. case_eq (nat_compare n i).
  (* n = i *)
    intros. simpl. apply nat_compare_eq in H0. rewrite H0. simpl.
    assert (i < j + 1). omega. apply nat_compare_lt in H1. rewrite H1.
    simpl. assert (i = i). reflexivity. apply nat_compare_eq_iff in H2.
    rewrite H2. clear H1 H2. rewrite lift_lem2.
    assert (Jeq: j - i + i = j). omega. rewrite Jeq. reflexivity. omega.
  (* n < i *)
    simpl. intros. apply nat_compare_lt in H0.
    assert (n < j). omega. assert (n < j + 1). omega.
    apply nat_compare_lt in H0.
    apply nat_compare_lt in H1.
    apply nat_compare_lt in H2.
    rewrite  H1, H2. simpl. rewrite H0. reflexivity.
  (* n > i *)
    intros.
    apply nat_compare_gt in H0.
    case_eq (nat_compare n (j + 1)).
      (* n = j + 1 *)
      intros. apply nat_compare_eq in H1. rewrite H1.
      assert (Jeq: j + 1 - 1 = j). omega. rewrite Jeq. simpl.
      assert (HH: nat_compare j j = Eq). assert (JJ: j = j). reflexivity.
          apply nat_compare_eq_iff in JJ. assumption.
      rewrite HH. rewrite lift_lem3. reflexivity. omega.
      (* n < j + 1 *)
      intros. apply nat_compare_lt in H1. simpl.
      assert (HLt: nat_compare (n-1) j = Lt).
        assert (n - 1 < j). omega. apply nat_compare_lt in H2. assumption.
        rewrite HLt.
      assert (Hgt: nat_compare n i = Gt).
        apply nat_compare_gt in H0. assumption.
        rewrite Hgt.
      reflexivity.
      (* n > j + 1 *)
      intros. apply nat_compare_gt in H1. simpl.
      assert (Ineq1: nat_compare (n - 1) j = Gt).
        assert (F: n - 1 > j). omega.
        apply nat_compare_gt in F. assumption. rewrite Ineq1.
      assert (Ineq2: nat_compare (n - 1) i = Gt).
        assert (n - 1 > i). omega. apply nat_compare_gt in H2. assumption.
        rewrite Ineq2.
      reflexivity.
Qed.


(** The named version looks like this:
   x =/= y and x not free in L implies:
       M[x/N][y/L] = M[y/L][x/(N[y/L])]
**)
Lemma subst_lemma: forall (M N L: lterm), forall (i j: nat),
   (i <= j) ->
       subst j L (subst i N M) = subst i (subst (j-i) L N) (subst (j+1) L M).
Proof.
  induction M.
  intros. intros. apply var_subst_lemma. assumption.
  intros. simpl. apply f_equal. rewrite IHM.
  assert (AllGood: j + 1 - (i + 1) = j - i). omega.
  rewrite AllGood. reflexivity. omega.
  intros. simpl. rewrite IHM1. rewrite IHM2. reflexivity.
  auto. auto.
Qed.
