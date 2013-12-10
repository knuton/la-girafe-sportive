Require Export Untyped.
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
    seem to trace down these due to Huet **)

Lemma lift_fuse:
  forall (N: lterm) (i j n m: nat),
    i <= j <= i + m -> lift n j (lift m i N) = lift (n+m) i N.
Proof.
  induction N as [k | N1 N2 | N1].
    (** N := Var k **)
    intros. simpl. case_eq (lt_dec k i).
      (** k < i **)
      intros. simpl. assert (k < j).
          apply lt_le_trans with i. assumption. apply H.
          destruct (lt_dec k j). reflexivity. contradict H1. auto.
      (** k >= i **)
      intros. simpl.
          destruct (lt_dec (k+m) j). contradict l. omega. apply f_equal.
          omega.
    (** N := Lam .. **)
    intros. simpl. apply f_equal. rewrite N2. reflexivity. omega.
    (** N := App .. .. **)
    intros. simpl. rewrite IHN1. rewrite IHN2. auto. auto. auto.
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
