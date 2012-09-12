(** Simple state monad for use in the 
    least generalization function **)

Set Implicit Arguments.

Require Import List Ty.

(** Representation of the state **)

Record state := mkState {
  st_next_tvar : nat ;               (** fresh variable generalization **)
  st_list_gen  : list (ty * ty * ty) (** list of generalizations done by the algorithm **)
}.

(** Concrete monad type definition **)

Definition M (A : Type) := state -> (state * A).

Definition ret (A : Type)(x : A) : M A := fun s => (s,x).

Definition bind(A B : Type)(c1 : M A)(c2: A -> M B) : M B :=
  fun s1 =>
    match c1 s1 with
      |(s2,v) => c2 v s2
    end.

Notation "x <- c1 ; c2" := (bind c1 (fun x => c2))
  (right associativity, at level 84, c1 at next level).

Definition freshVar : M nat :=
  fun s =>
    match s with
      | mkState n m => (mkState (S n) m, n)
    end.

Fixpoint lookup_gen_aux (t t' : ty) (m : list (ty * ty * ty)) : option ty :=
  match m with
    | nil => None
    | (t1,t2,t3) :: m' =>
      match eq_ty_dec t t1, eq_ty_dec t' t2 with
        | left _, left _ => Some t3
        | left _, right _ => None
        | right _, left _ => None
        | right _, right _ => None
      end
  end.

Definition lookup_gen (t t' : ty) : M ty :=
  fun s =>
    match s with
      | mkState n m =>
        match lookup_gen_aux t t' m with
          | None => 
            (mkState (S n) ((t,t',(tvar n)) :: m), tvar n)
          | Some t => (s,t)
        end
    end.