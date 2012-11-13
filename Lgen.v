Set Implicit Arguments.

Require Import List Program.
Require Import LibTactics Omega Arith_base.

Inductive ty : Type :=
  | var : nat -> ty
  | con : nat -> ty
  | app : ty -> ty -> ty.

Definition eq_ty_dec : forall (t t' : ty) , {t = t'} + {t <> t'}.
   pose eq_nat_dec.
   decide equality.
Defined.

Inductive leq_ty : ty -> ty -> Prop :=
  | leq_var : forall n t, leq_ty (var n) t
  | leq_con : forall n, leq_ty (con n) (con n)
  | leq_app : forall l l' r r', leq_ty l l' -> leq_ty r r' -> leq_ty (app l r) (app l' r').

Hint Constructors leq_ty.

Fixpoint fv (t : ty) : list nat :=
  match t with
    | var n => n :: nil
    | con n    => nil
    | app l r  => fv l ++ fv r 
  end.

Notation "'[' x ']'" := (exist _ x _).
Notation "'[[' x ']]'" := (inleft _ [x]).
Notation "!!" := (inright _ _).

Obligation Tactic := program_simpl ; intuition ; 
              (repeat (match goal with
                       | [H : _ \/ _ |- _] => destruct H ; subst
                       | [H : context[In _ _ -> _], 
                          H1 : In _ _ |- _] => apply H in H1 ; try omega
                       end)).

Program Fixpoint max_list (l : list nat) : {n | forall n', In n' l -> n > n'} :=
  match l with
    | nil => 0
    | x :: l' =>
        match max_list l' with
          | x' => match le_gt_dec x x' with
                    | left _  => S x'
                    | right _ => S x
                  end
        end
  end.

Definition gen_list := list (ty * ty * nat)%type.

Obligation Tactic := program_simpl ; intuition ;
     repeat 
       (match goal with
          | [H : ex _ |- _] => let v := fresh "v" in destruct H as [v H]
          | [H : False |- _] => elim H
          | [H : _ \/ _ |- _] => destruct H
          | [H : _ = _ |- _] => inverts* H
        end).

Program Fixpoint lookup_gen_list (t t' : ty) (l : gen_list) : 
  {n | In (t,t',n) l} + {~ exists n, In (t,t',n) l} :=
  match l with
    | nil => inright _ _
    | x :: l' => 
        match x with
          | (a,b,c) => 
              match eq_ty_dec t a, eq_ty_dec b t' with
                | left _, left _ => inleft _ (exist _ c _)
                | right _, left _ => 
                    match lookup_gen_list t t' l' with
                      | inleft x  => inleft _ x
                      | inright _ => inright _ _
                    end
                | left _, right _ => 
                    match lookup_gen_list t t' l' with
                      | inleft x => inleft _ x
                      | inright _ => inright _ _
                    end
                | right _, right _ => 
                    match lookup_gen_list t t' l' with
                      | inleft x => inleft _ x
                      | inright _ => inright _ _
                    end
              end
        end
  end.

Definition least_gen (t t' t1 : ty) :=
  leq_ty t1 t /\ leq_ty t1 t' /\ forall u, leq_ty u t /\ leq_ty u t' -> leq_ty u t1.

Obligation Tactic := 
           unfold least_gen in * ; program_simpl ; intuition ; 
               repeat (match goal with 
                        | [H : leq_ty _ _ |- _] => inverts* H
                        | [H : ?n = ?n -> False |- _] => elim H ; auto
                       end).

Program Fixpoint lgen_aux (t t' : ty) (l : gen_list) (m : nat) : {p | least_gen t t' (@fst ty (gen_list * nat) p)} :=
  match t,t' with
    | var n, var n' =>
        match eq_nat_dec n n' with
          | left _  => exist _ (var n, (l, m)) _
          | right _ => 
              match lookup_gen_list (var n) (var n') l with 
                | inleft (exist x _) => exist _ (var x, (l,m)) _
                | inright _ => exist _ (var m, ((var n, var n',m) :: l, S m)) _
              end
        end
    | var n, con n' =>
        match lookup_gen_list (var n) (con n') l with
          | inleft (exist x _) => exist _ (var x, (l,m)) _
          | inright _ => exist _ (var m, ((var n, con n',m) :: l, S m)) _
        end
    | var n, app f r =>
        match lookup_gen_list (var n) (app f r) l with
          | inleft (exist x _) => exist _ (var x, (l,m)) _
          | inright _ => exist _ (var m, ((var n,app f r,m) :: l, S m)) _            
        end
    | con n, con n' => 
        match eq_nat_dec n n' with
          | left _ => exist _ (con n, (l,m)) _
          | right _ => 
              match lookup_gen_list (con n) (con n') l with
                | inleft (exist x _) => exist _ (var x, (l,m)) _
                | inright _ => exist _ (var m, ((con n,con n',m) :: l, S m)) _
              end
        end
    | con n, var n' =>
        match lookup_gen_list (con n) (var n') l with
          | inleft (exist x _) => exist _ (var x, (l,m)) _
          | inright _ => exist _ (var m, ((con n, var n',m) :: l, S m)) _
        end  
    | con n, app f r =>
        match lookup_gen_list (con n) (app f r) l with
          | inleft (exist x _) => exist _ (var x, (l,m)) _
          | inright _ => exist _ (var m, ((con n, app f r,m) :: l, S m)) _
        end    
    | app f r, con n =>
        match lookup_gen_list (app f r) (con n) l with
          | inleft (exist x _) => exist _ (var x, (l,m)) _
          | inright _ => exist _ (var m, ((app f r, con n,m) :: l, S m)) _
        end  
    | app f r, var n =>
        match lookup_gen_list (app f r) (var n) l with
          | inleft (exist x _) => exist _ (var x, (l,m)) _
          | inright _ => exist _ (var m, ((app f r, var n,m) :: l, S m)) _
        end    
    | app f r, app f' r' =>
        match lgen_aux f f' l m with
          | (t,(l',m')) => 
              match lgen_aux r r' l' m' with
                | (t', (l'', m'')) => 
                    exist _ (app t t', (l'', m'')) _
              end
        end 
  end.

Definition lgen (t t' : ty) : {t1 | least_gen t t' t1}.
   destruct (max_list (fv t ++ fv t')) as [v H].
   destruct (lgen_aux t t' nil v).
   destruct x. simpl in *. exists* t0.
Defined.
   
Eval compute in lgen (app (app (con 0) (var 1)) (con 1)) (app (app (con 0) (con 2)) (var 1)).

Definition tint := con 1.
Definition tfloat := con 2.

Eval compute in lgen (app (app (con 0) tint) tint) (app (app (con 0) tfloat) tfloat).