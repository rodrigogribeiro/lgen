Set Implicit Arguments.

Require Import List Program.

Require Import LibTactics Omega.
Require Import TyOrder Subst Ty Arith_base.

Include SUBST.
Include TYORDER.

Inductive ground_ty : Type :=
  | skolem : nat -> ground_ty
  | con : nat -> ground_ty
  | app : ground_ty -> ground_ty -> ground_ty.

Definition eq_ground_ty_dec : forall (t t' : ground_ty) , {t = t'} + {t <> t'}.
   pose eq_nat_dec.
   decide equality.
Defined.

Inductive leq_ground : ground_ty -> ground_ty -> Prop :=
  | leq_skolem : forall n t, leq_ground (skolem n) t
  | leq_con : forall n, leq_ground (con n) (con n)
  | leq_app : forall l l' r r', leq_ground l l' -> leq_ground r r' -> leq_ground (app l r) (app l' r').

Hint Constructors leq_ground.

Fixpoint skolemize (t : ty) : ground_ty :=
  match t with
    | tvar n => skolem n
    | tcon n => con n
    | tapp l r => app (skolemize l) (skolemize r)
  end.

Fixpoint unskolemize (t : ground_ty) : ty :=
  match t with
    | skolem n => tvar n
    | con n => tcon n
    | app l r => tapp (unskolemize l) (unskolemize r)
  end.

Fixpoint skolem_vars (t : ground_ty) : list nat :=
  match t with
    | skolem n => n :: nil
    | con n    => nil
    | app l r  => skolem_vars l ++ skolem_vars r 
  end.

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

Definition gen_list := list (ground_ty * ground_ty * nat)%type.

Obligation Tactic := program_simpl ; intuition ;
     repeat 
       (match goal with
          | [H : ex _ |- _] => let v := fresh "v" in destruct H as [v H]
          | [H : False |- _] => elim H
          | [H : _ \/ _ |- _] => destruct H
          | [H : _ = _ |- _] => inverts* H
        end).

Program Fixpoint lookup_gen_list (t t' : ground_ty) (l : gen_list) : 
  {n | In (t,t',n) l} + {~ exists n, In (t,t',n) l} :=
  match l with
    | nil => inright _ _
    | x :: l' => 
        match x with
          | (a,b,c) => 
              match eq_ground_ty_dec t a, eq_ground_ty_dec b t' with
                | left _, left _ => inleft _ (exist _ c _)
                | right _, left _ => 
                    match lookup_gen_list t t' l' with
                      | inleft x => inleft _ x
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

Definition lgen_ground (t t' t1 : ground_ty) :=
  leq_ground t1 t /\ leq_ground t1 t' /\ forall u, leq_ground u t /\ leq_ground u t' -> leq_ground u t1.

Obligation Tactic := 
           unfold lgen_ground in * ; program_simpl ; intuition ; 
               repeat (match goal with 
                        | [H : leq_ground _ _ |- _] => inverts* H
                        | [H : ?n = ?n -> False |- _] => elim H ; auto
                       end).

Program Fixpoint lgen_ground_aux (t t' : ground_ty) (l : gen_list) (m : nat) : {p | lgen_ground t t' (@fst ground_ty (gen_list * nat) p)} :=
  match t,t' with
    | skolem n, skolem n' =>
        match eq_nat_dec n n' with
          | left _  => exist _ (skolem n, (l, m)) _
          | right _ => 
              match lookup_gen_list (skolem n) (skolem n') l with 
                | inleft (exist x _) => exist _ (skolem x, (l,m)) _
                | inright _ => exist _ (skolem m, ((skolem n, skolem n',m) :: l, S m)) _
              end
        end
    | skolem n, con n' =>
        match lookup_gen_list (skolem n) (con n') l with
          | inleft (exist x _) => exist _ (skolem x, (l,m)) _
          | inright _ => exist _ (skolem m, ((skolem n, con n',m) :: l, S m)) _
        end
    | skolem n, app f r =>
        match lookup_gen_list (skolem n) (app f r) l with
          | inleft (exist x _) => exist _ (skolem x, (l,m)) _
          | inright _ => exist _ (skolem m, ((skolem n,app f r,m) :: l, S m)) _            
        end
    | con n, con n' => 
        match eq_nat_dec n n' with
          | left _ => exist _ (con n, (l,m)) _
          | right _ => 
              match lookup_gen_list (con n) (con n') l with
                | inleft (exist x _) => exist _ (skolem x, (l,m)) _
                | inright _ => exist _ (skolem m, ((con n,con n',m) :: l, S m)) _
              end
        end
    | con n, skolem n' =>
        match lookup_gen_list (con n) (skolem n') l with
          | inleft (exist x _) => exist _ (skolem x, (l,m)) _
          | inright _ => exist _ (skolem m, ((con n, skolem n',m) :: l, S m)) _
        end  
    | con n, app f r =>
        match lookup_gen_list (con n) (app f r) l with
          | inleft (exist x _) => exist _ (skolem x, (l,m)) _
          | inright _ => exist _ (skolem m, ((con n, app f r,m) :: l, S m)) _
        end    
    | app f r, con n =>
        match lookup_gen_list (app f r) (con n) l with
          | inleft (exist x _) => exist _ (skolem x, (l,m)) _
          | inright _ => exist _ (skolem m, ((app f r, con n,m) :: l, S m)) _
        end  
    | app f r, skolem n =>
        match lookup_gen_list (app f r) (skolem n) l with
          | inleft (exist x _) => exist _ (skolem x, (l,m)) _
          | inright _ => exist _ (skolem m, ((app f r, skolem n,m) :: l, S m)) _
        end    
    | app f r, app f' r' =>
        match lgen_ground_aux f f' l m with
          | (t,(l',m')) => 
              match lgen_ground_aux r r' l' m' with
                | (t', (l'', m'')) => 
                    exist _ (app t t', (l'', m'')) _
              end
        end 
  end.

Program Definition lgen (t t' : ground_ty) := 
  match max_list (skolem_vars t ++ skolem_vars t') with
    v => fst (lgen_ground_aux t t' nil v)
  end.
  