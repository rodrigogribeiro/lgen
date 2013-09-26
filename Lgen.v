Set Implicit Arguments.

Require Import List Omega Arith_base.
Require Import LibTactics.

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

Remark leq_ty_refl : forall t, leq_ty t t.
Proof.
  induction t ; auto.
Qed.

Remark leq_ty_trans : forall t t', leq_ty t t' -> forall t'', leq_ty t' t'' -> leq_ty t t''.
Proof.
  induction 1 ; intros ; auto ;
     match goal with
       | [H : leq_ty (app _ _) _ |- _] => inverts* H
       | [|- _] => idtac
     end.
Qed.

Hint Resolve leq_ty_refl leq_ty_trans.

Fixpoint fv (t : ty) : list nat :=
  match t with
    | var n => n :: nil
    | con n => nil
    | app l r => fv l ++ fv r
  end.

Definition max_list : forall (l : list nat), {n | forall n', In n' l -> n > n'}.
  refine (fix max_list (l : list nat) : {n | forall n', In n' l -> n > n'} :=
            match l with
              | nil => exist _ 0 _
              | x :: l' => 
                match max_list l' with
                  exist x' _ =>
                    match le_gt_dec x x' with
                      | left _ => exist _ (S x') _
                      | right _ => exist _ (S x) _
                    end
                end
            end) ; clear max_list  ; simpl in * ; intuition ; 
                   try (match goal with
                          | [H : context[In _ _ -> _],
                             H1 : In _ _ |- _] => apply H in H1 ; try omega
                        end).
Defined.

Definition gen_list := list (ty * ty * nat)%type.

Definition lookup_phi : forall (t  t' : ty) (l : gen_list), {n | In (t,t',n) l} + {~ exists n, In (t,t',n) l}.
  refine (fix lookup_phi (t t' : ty)(l : gen_list) : {n | In (t,t',n) l} + {~ exists n, In (t,t',n) l} :=
            match l with
              | nil => inright _ _
              | (a,b,c) :: l' => 
                match eq_ty_dec t a, eq_ty_dec t' b with
                   | left _ , left _ => inleft _ (exist _ c _)
                   | _ , _           => 
                     match lookup_phi t t' l' with
                       | inleft (exist x _) => inleft _ (exist _ x _)
                       | inright _ => inright _ _                         
                     end
                end
            end) ; clear lookup_phi ; simpl in * ; intuition ; substs* ;
                   repeat 
                       (match goal with
                         | [H : ex _ |- _] => 
                            let v := fresh "v" in destruct H as [v H]
                         | [H : _ = _ |- _] => inverts* H
                        end ; intuition) ; jauto. 
Defined.
  
Definition least_gen (t t' t1 : ty) :=
  leq_ty t1 t /\ leq_ty t1 t' /\ forall u, leq_ty u t /\ leq_ty u t' -> leq_ty u t1.

Remark least_gen_refl : forall t, least_gen t t t.
Proof.
  induction t ; unfold least_gen in * ; intuition ; auto.
Qed.

Hint Resolve least_gen_refl.

Definition lgen_aux : forall (t t' : ty) (l : gen_list) (m : nat), {p | least_gen t t' (@fst ty (gen_list * nat) p)}.
  refine (fix lgen_aux (t t' : ty) (l : gen_list) (m : nat) : {p | least_gen t t' (@fst ty (gen_list * nat) p)} :=
      match t,t' with
        | con n, con n' =>
          match eq_nat_dec n n' with
            | left _ => exist _ (con n, (l, m)) _
            | right _ =>
                match lookup_phi t t' l with
                  | inleft (exist x _) => exist _ (var x, (l,m)) _
                  | inright _ => exist _ (var m, ((con n, con n',m) :: l, S m)) _
                end
          end
        | app f r, app f' r' =>
          match lgen_aux f f' l m with
            | exist v _ => 
              match lgen_aux r r' (fst (snd v)) (snd (snd v)) with
                | exist v' _ => exist _ (app (fst v) (fst v'), (fst (snd v') , snd (snd v'))) _
              end
          end
        | a, b => 
            match lookup_phi a b l with
               | inleft (exist x _) => exist _ (var x, (l,m)) _
               | inright _ => exist _ (var m, ((a, b, m) :: l, S m)) _
            end
      end)
   ; clear lgen_aux ; unfold least_gen in * ; simpl in * ; intuition ; substs ; eauto ;
     try repeat 
         (match goal with
             | [H : leq_ty ?u (con ?n), H0 : leq_ty ?u (con ?n') |- _] => inverts* H ; inverts* H0 ; try contradiction
             | [H : leq_ty ?u (con _), H0 : leq_ty ?u (app _ _) |- _] => inverts* H ; inverts* H0
             | [H : (?n = ?n) -> False |- _] => elim H ; auto
             | [v : (ty * (gen_list * nat))%type |- _] => let va := fresh "va" in 
                                                          let vb := fresh "vb" in
                                                          destruct v as [v [va vb]] ; simpl in *
             | [H : leq_ty ?u (app _ _), H' : leq_ty ?u (app _ _) |- _ ] =>
                   inverts* H6 ; inverts* H7 ; eauto
          end). 
Defined.

Definition lgen (t t' : ty) : {t1 | least_gen t t' t1}.
   destruct (max_list (fv t ++ fv t')) as [v H].
   destruct (lgen_aux t t' nil v) as [[t1 [phi m]] Ht1].
   simpl in *. exists* t1.
Defined.

Fixpoint least_gen_list (t : ty) (l : list ty) : Prop :=
  match l with
    | nil => True
    | x :: l' => exists t', least_gen_list t' l' /\ least_gen x t' t
  end.

Definition lcg : forall (l : list ty), {t | least_gen_list t l} + {l = nil}.   
   refine (fix lcg (l : list ty) : {t | least_gen_list t l} + {l = nil} :=
              match l return {t | least_gen_list t l} + {l = nil} with
                | nil => inright _ _
                | x :: l' =>
                    match lcg l' with
                      | inright _ => inleft _ (exist _ x _)
                      | inleft (exist y _)  =>
                          match lgen x y with
                            exist z _ => inleft _ (exist _ z _)  
                          end
                    end
              end
          ) ; clear lcg ; repeat (unfold least_gen in * ; substs ; simpl in * ; intuition) ; 
              try eexists ; splits ; eauto ; tauto.
Defined.         
   

