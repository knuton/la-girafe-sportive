Require Export Untyped.
Require Import Coq.Arith.Compare_dec.

(** (l)ift (t)erms below the (b)ound by some (l)evel **)
Fixpoint lift (l: nat) (b: nat) (t: lterm) : lterm :=
  match t with
      | Var i as v =>  if (le_lt_dec i b) then Var (i+l) else v
      | App m n => App (lift l b m) (lift l b n)
      | Lam t => Lam (lift (l+1) b t)
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


Lemma subst_lemma: forall (i j: nat), forall (m n l: lterm),
   (i <= j) ->
       subst j l (subst i n m) = subst i (subst (j-i) l n) (subst (j+1) l m).
Proof.
  admit.
Qed.
