Require Import Arith_base.

Inductive ty : Set := 
  | tvar : nat -> ty 
  | tcon : nat -> ty
  | tapp : ty -> ty -> ty.

Fixpoint ty_size (t : ty) : nat :=
  match t with
    | tvar _ => 0
    | tcon _ => 1
    | tapp l r => 1 + (ty_size l) + (ty_size r)
  end.

Definition ty_pair_size (t t' : ty) : nat :=
  (ty_size t) + (ty_size t').

(** equality on types is decidable **)

Definition eq_ty_dec : forall (t t' : ty), {t = t'} + {t <> t'}.
   pose eq_nat_dec.
   decide equality.
Defined.
