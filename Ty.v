Require Import Arith_base.

Inductive ty : Set := 
  | tvar : nat -> ty 
  | tcon : nat -> ty
  | tapp : ty -> ty -> ty.

(** equality on types is decidable **)

Definition eq_type_dec : forall (t t' : ty), {t = t'} + {t <> t'}.
   pose eq_nat_dec.
   decide equality.
Defined.
