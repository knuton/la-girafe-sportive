Require Export Untyped.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Plus.

(** (l)ift (t)erms below the (b)ound by some (l)evel **)
Fixpoint lift (l: nat) (b: nat) (t: lterm) : lterm :=
  match t with
      | Var i as v =>  if (lt_dec i b) then Var (i+l) else v
      | App m n => App (lift l b m) (lift l b n)
      | Lam t => Lam (lift l (b+1) t)
  end.

(** Substitute the variable with index `v` by `r` in the term `t` **)
Fixpoint subst (v: nat) (r: lterm) (t: lterm) : lterm :=
  match t with
      | Var i =>  match (nat_compare i v) with
                           | Lt => Var i
                           | Eq => lift 0 v r
                           | Gt => Var (i - 1)
                  end
      | App m n => App (subst v r m) (subst v r n)
      | Lam m => Lam (subst (v+1) r m)
  end.


(** The following lemmas are described in Berghofer and Urban, who
    seem to trace down these due to Huet **)

(* Lemma lt_dec_lt: forall m n, m <= n -> le_lt_dec m n. *)

Example fishy: 2 <= 4 <= 2 + 100 /\ lift 3 4 (lift 100 2 (Var 1)) <> lift 103 2 (Var 1).
Proof.
  split. split. auto. simpl. assert (0 <= 98). apply Le.le_0_n. apply (plus_le_compat_r 0 98 4) in H. simpl in H. assumption.
  simpl. unfold not. intros. inversion H.
Qed.

Example lift_lem_1_bs:
  ~ forall (i j n m: nat) (N: lterm),
    i <= j <= i + m -> lift n j (lift m i N) = lift (n+m) i N.
Proof.
  unfold not. intros L.
  assert (I: 2 <= 4 <= 2 + 100 -> lift 3 4 (lift 100 2 (Var 1)) = lift (3 + 100) 2 (Var 1)).
  apply (L 2 4 3 100).
  assert (INQ: 2 <= 4 <= 2 + 100). split. auto. simpl. assert (TRIV: 0 <= 98). apply Le.le_0_n.  apply (plus_le_compat_r 0 98 4) in TRIV. simpl in TRIV. assumption.
  apply I in INQ. simpl in INQ. inversion INQ.
Qed.

Lemma lift_lem1:
  forall (i j n m: nat) (N: lterm),
    i <= j <= i + m -> lift n j (lift m i N) = lift (n+m) i N.
Proof.
  intros i j n m N.
  generalize i j n m. clear i j n m.
  induction N as [k | N1 N2 | N1].
    (** N := Var k *)
    intros i j n m (ij, jim).
    simpl. case (lt_dec k i).
      (** k < i *)
      intro ki.
      intro ki. simpl. elim (lt_dec (k + m) j)
        intro kpmj. rewrite plus_assoc_reverse. assert (m + n = n + m). apply plus_comm. rewrite H. reflexivity.
      (** CHEATED *)
      intro negkpmj. unfold not in negkpmj. assert (k + m < j). admit. apply negkpmj in H. inversion H.
      intro negki. unfold not in negki. admit.
    (** N := Lam N1 *)
    intros i j n m (ij, jim). simpl. f_equal. apply N2. split.
      (** i + 1 <= j + 1 *)
      apply plus_le_compat_r. assumption.
      (** j + 1 <= i + 1 + m *)
      rewrite <- plus_assoc. rewrite plus_permute. rewrite plus_comm.
      apply plus_le_compat_l. assumption.
    (** N := App N1 N2 *)
    intros i j n m (ij, jim). simpl. f_equal.
    apply IHN1. split. assumption. assumption.
    apply IHN2. split. assumption. assumption.
Qed.

Lemma lift_lem2:
  forall (i j k: nat) (N L: lterm),
  k <= j -> lift i k (subst j L N) = subst (j+i) L (lift i k N).
Proof.
  admit.
Qed.

Lemma lift_lem3:
  forall (i j k: nat) (N L P: lterm),
  k <= i /\ i < k + (j + 1) -> subst i P (lift (j+1) k L) = lift j k L.
Proof.
  admit.
Qed.


Lemma subst_var_idemp:
  forall (n: nat) (N: lterm), subst n N (Var n) = N.
Proof.
  intros. destruct n; trivial.
  intros. simpl.
Abort.

Lemma var_subst_lemma: forall (i j n: nat), forall (N L: lterm),
   (i <= j) ->
       subst j L (subst i N (Var n)) =
                 subst i (subst (j-i) L N) (subst (j+1) L (Var n)).
Proof.
  admit.
(**
  intros i j n. generalize dependent j.
  case_eq (nat_compare i n).
**)
Qed.


(** The named version looks like this:
   x =/= y and x not free in L implies:
       M[x/N][y/L] = M[y/L][x/(N[y/L])]
**)
Lemma subst_lemma: forall (i j: nat), forall (m n l: lterm),
   (i <= j) ->
       subst j l (subst i n m) = subst i (subst (j-i) l n) (subst (j+1) l m).
Proof.
  admit.
Qed.
