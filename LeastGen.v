Set Implicit Arguments.

Require Import List.

Require Import LibTactics Omega.
Require Import TyOrder Subst Ty Arith_base.

Include SUBST.
Include TYORDER.

Definition gen_list := list (ty * ty * ty)%type.

Fixpoint fv_gen_list (l : gen_list) : list nat :=
  match l with
    | nil => nil
    | t :: l' => match t with
                   | (t1,t2,t3) => fv t1 ++ fv t2 ++ fv t3 ++ fv_gen_list l'
                 end
  end.

Inductive wf_gen_list : gen_list -> Prop :=
  | wf_nil : wf_gen_list nil
  | wf_con : forall t1 t2 n l, wf_gen_list l -> tvar n <=: t1 -> tvar n <=: t2 -> wf_gen_list ((t1,t2,tvar n) :: l).

Hint Constructors wf_gen_list.

Fixpoint split_gen_list (g : gen_list) : option (subst * subst) :=
  match g with
    | nil => Some (M.empty ty, M.empty ty)
    | x :: l =>
      match x with
        | (x1,x2,x3) =>
          match split_gen_list l with
            | Some (s1,s2) => 
              match x3 with
                | tvar n => Some (M.add n x1 s1, M.add n x2 s2)
                | tcon n => 
                  match x1, x2 with
                    | tcon n1, tcon n2 => 
                      match eq_nat_dec n n1, eq_nat_dec n1 n2 with
                        | left _, left _ => Some (s1,s2)
                        | _ , _ => None
                      end
                    | _ , _ => None
                  end
                | _      => None
              end
            | None => None
          end
      end
  end.

Lemma wf_gen_list_in : forall (t t' t1 : ty) (l : gen_list),
  wf_gen_list l -> In (t,t',t1) l -> t1 <=: t /\ t1 <=: t'.
Proof.
  intros t t' t1 l Hwf Hin.
  induction Hwf. inverts* Hin.
  split ; simpl in Hin ; destruct Hin. inverts* H1.
  apply IHHwf in H1. destruct* H1. inverts* H1.
  apply IHHwf in H1. destruct* H1.
Qed.

Definition lookup_gen_list : forall (l : gen_list), 
  wf_gen_list l -> forall (t t' : ty), {t1 | In (t,t',t1) l} + {~ exists t1, In (t,t',t1) l}.
  intros l Hwf.
  refine ((fix F (l : gen_list) (t t' : ty) {struct l} : {t1 | In (t,t',t1) l} + {~ exists t1, In (t,t',t1) l} := 
             match l return {t1 | In (t,t',t1) l} + {~ exists t1, In (t,t',t1) l} with
               | nil => inright _ _
               | x :: l' =>
                 match x with
                   | (x1,x2,x3) => 
                     match eq_ty_dec x1 t, eq_ty_dec x2 t' with
                       | left _, left _ => inleft _ (exist _ x3 _)
                       | right _, left _ =>
                         match F l' t t' with
                           | inleft (exist y _)  => inleft _ (exist _ y _)
                           | inright _ => inright _ _
                         end
                       | left _, right _ =>
                         match F l' t t' with
                           | inleft (exist y _)  => inleft _ (exist _ y _)
                           | inright _ => inright _ _
                         end
                       | right _, right _ =>
                         match F l' t t' with
                           | inleft (exist y _) => inleft _ (exist _ y _)
                           | inright _ => inright _ _
                         end 
                     end
                 end
             end
          ) l) ;
    try intro H ; simpl ; try subst ;
      repeat 
        (match goal with
          | [H : In _ _ |- _] => simpl in H; destruct* H
          | [H : ex _ |- _] => destruct H
          | [H : _ = _ |- _] => try congruence
          | [|- ?X = ?X \/ _] => branch* 1
          | [H : ?X |- _ \/ ?X] => branch* 2
         end).
Defined.
 
Definition max_list_nat_dec : forall (l : list nat), 
                                {n | forall n', In n' l -> n >= n'} + {l = nil}.
   refine (fix F (l : list nat) {struct l} : {n | forall n', In n' l -> n >= n'} + {l = nil} :=
                match l return {n | forall n', In n' l -> n >= n'} + {l = nil} with
                  | nil => inright _ _
                  | n1 :: l' =>
                        match F l' with
                          | inleft (exist x _) =>
                                        match le_gt_dec x n1 with
                                          | left _ => inleft _ (exist _ n1 _)
                                          | right _ => inleft _ (exist _ x _)
                                        end
                          | inright _ => inleft _ (exist _ n1 _)  
                        end
                end) ; auto.
   introv H. apply in_inv in H. destruct* H. subst.
   auto. apply (g n') in H. omega.
   introv H. apply in_inv in H. destruct* H. subst. omega.
   subst. introv H. apply in_inv in H. destruct* H ; try omega.
   inverts H.
Defined.

Definition fresh_nat (n : nat) (l : list nat) :=
  forall n', In n' l -> n > n'.

Definition fresh_nat_from_list : forall (l : list nat),
  {n | fresh_nat n l}.
  intro l. 
  cases* (max_list_nat_dec l).
  destruct H.
  destruct* s as [n' Hs].
  exists (S n'). unfolds.
  introv H. apply (Hs n'0) in H.
  inverts* H. omega.
  subst. exists 0. unfolds.
  intros. inverts H0.
Defined.

Definition fresh_nat_from_ty : forall (t : ty),
  {n | fresh_nat n (fv t)}.
  intro t.
  cases* (max_list_nat_dec (fv t)).
  destruct H.
  destruct* s as [n' Hs].
  exists (S n'). unfolds.
  introv H. apply (Hs n'0) in H.
  inverts* H. omega. 
  rewrite e. exists 0. unfolds.
  intros. inverts H0.
Defined.

Definition fresh_nat_from_ty_triple : forall (t t' t1 : ty),
  {n | fresh_nat n (fv t ++ fv t' ++ fv t1)}.
  intros t t' t1.
  cases* (fresh_nat_from_ty t) as Ht ; destruct Ht.
  cases* (fresh_nat_from_ty t') as Ht' ; destruct Ht'.
  cases* (fresh_nat_from_ty t1) as Ht1 ; destruct Ht1.
  unfold fresh_nat in *.
  cases* (le_gt_dec x x0) as H ;
  cases* (le_gt_dec x0 x1) as H1.
  exists x1.
  intros. apply in_app_or in H0. destruct H0.
  apply (f n') in H0 ; auto. omega.
  apply in_app_or in H0. destruct H0.
  apply (f0 n') in H0. omega.
  apply (f1 n') in H0. omega.
  exists x0. intros. apply in_app_or in H0. destruct H0.
  apply (f n') in H0. omega.
  apply in_app_or in H0. destruct H0.
  apply (f0 n') in H0. omega.
  apply (f1 n') in H0. omega.
  cases*(le_gt_dec x x1) as H2.
  exists x1. intros. apply in_app_or in H0. destruct H0.
  apply (f n') in H0. omega. apply in_app_or in H0. destruct H0.
  apply (f0 n') in H0 ; omega.
  apply (f1 n') in H0 ; omega.
  exists x. intros. apply in_app_or in H0. destruct H0.
  apply (f n') in H0 ; omega.
  apply in_app_or in H0. destruct H0.
  apply (f0 n') in H0 ; omega.
  apply (f1 n') in H0 ; omega.
  exists x. intros. apply in_app_or in H0 ; destruct H0.
  apply (f n') in H0 ; omega.
  apply in_app_or in H0 ; destruct H0.
  apply (f0 n') in H0 ; omega.
  apply (f1 n') in H0 ; omega.
Defined.

Definition fresh_nat_from_gen_list : forall (l : gen_list),
  {n | fresh_nat n (fv_gen_list l)}.
  refine (fix F (l : gen_list) : {n | fresh_nat n (fv_gen_list l)} :=
            match l return {n | fresh_nat n (fv_gen_list l)} with
              | nil => exist _ 0 _
              | p :: l' => 
                match p with
                  (t1,t2,t3) => match F l' with
                                  exist m _ => 
                                  match fresh_nat_from_ty_triple t1 t2 t3 with
                                    | exist m' _ => match le_gt_dec m m' with
                                                      | left _ => exist _ m' _
                                                      | right _ => exist _ m _
                                                    end
                                  end
                                end
                end
            end) ; unfolds ; introv H ; simpl in H.
            elim H.
            unfolds in f. unfolds in f0.
            rewrite app_assoc in H. rewrite app_assoc in H.
            apply in_app_or in H. destruct H.
            rewrite <- app_assoc in H.
            apply (f0 n') in H ; omega.
            apply (f n') in H ; omega.
            rewrite app_assoc in H. rewrite app_assoc in H.
            apply in_app_or in H ; destruct H.
            rewrite <- app_assoc in H.
            unfolds in f. unfolds in f0.
            apply (f0 n') in H ; omega.
            apply (f n') in H ; omega.
Defined.

Definition fresh : forall (t t' : ty) (l : gen_list), {n | fresh_nat n (fv t ++ fv t' ++ fv_gen_list l)}.
  intros t t' l.
  cases* (fresh_nat_from_ty t) as H ; destruct H ;
  cases* (fresh_nat_from_ty t') as H1 ; destruct H1 ;
  cases* (fresh_nat_from_gen_list l) as H2 ; destruct H2.
  cases* (le_gt_dec x x0) as H3 ; destruct H3 ;
  cases* (le_gt_dec x0 x1) as H4 ; destruct H4.
  exists x1. unfolds. introv Hi. rewrite app_assoc in Hi.
  apply in_app_or in Hi. destruct Hi.
  apply in_app_or in H. destruct H.
  unfolds in f. apply (f n') in H. omega.
  unfolds in f0. apply (f0 n') in H. omega.
  unfolds in f1. apply (f1 n') in H. omega.
  exists x0. unfolds. introv Hi. rewrite app_assoc in Hi.
  apply in_app_or in Hi. destruct Hi.
  apply in_app_or in H. destruct H. 
  unfolds in f. apply (f n') in H. omega.
  unfolds in f0. apply (f0 n') in H. omega.
  unfolds in f1. apply (f1 n') in H. omega.
  cases* (le_gt_dec x x1) as H ; destruct H.
  exists x1. unfolds. introv Hi. rewrite app_assoc in Hi.
  apply in_app_or in Hi. destruct Hi.
  apply in_app_or in H. destruct H.
  unfolds in f. apply (f n') in H. omega.
  unfolds in f0. apply (f0 n') in H. omega.
  unfolds in f1. apply (f1 n') in H. omega.
  exists x. unfolds. introv Hi. rewrite app_assoc in Hi.
  apply in_app_or in Hi. destruct Hi.
  apply in_app_or in H. destruct H.
  unfolds in f. apply (f n') in H. omega.
  unfolds in f0. apply (f0 n') in H. omega.
  unfolds in f1. apply (f1 n') in H. omega.
  exists x. unfolds. introv Hi. rewrite app_assoc in Hi.
  apply in_app_or in Hi. destruct Hi.
  apply in_app_or in H. destruct H.
  unfolds in f. apply (f n') in H. omega.
  unfolds in f0. apply (f0 n') in H. omega.
  unfolds in f1. apply (f1 n') in H. omega.
Defined.

Definition least_gen (t1 t2 t : ty) : Prop :=
   t <=: t1 /\ t <=: t2 /\ (forall u, u <=: t1 /\ u <=: t2 -> u <=: t).
   
Ltac s := try intros ; substs ;
          try (exists* (@nil (ty * ty * ty)%type)) ; try congruence ;
    match goal with
      | [H : _ /\ _ |- _] => destruct H
      | [H : ex _ |- _] => destruct H
      | [|- _ /\ _] => split
      | [|- (tvar ?x) <=: ?t] => 
           unfolds ; exists (M.add x t (@M.empty ty)) ;
             simpl ; rewrite add_o ; case_if* 
      | [|- ?t <=: ?t] => apply leq_ty_refl 
      | [H :_ <=: (tvar _) |- _] => 
           apply leq_var_inv_r in H ; destruct H ; subst
      | [H : _ <=: (tcon _) |- _] =>
           apply leq_con_inv_r in H ; destruct H
      | [H : (tcon _) <=: (tapp _ _) |- _] => 
          unfolds in H ; let s := fresh "s" in destruct H as [s H] ; inverts* H
      | [H : In (?t, _, ?t1) ?l, H1 : wf_gen_list ?l  |- ?t1 <=: ?t] =>
          destruct* (wf_gen_list_in _ _ _ H1 H)
      | [H : In (_, ?t, ?t1) ?l, H1 : wf_gen_list ?l |- ?t1 <=: ?t] =>
          destruct* (wf_gen_list_in _ _ _ H1 H)
      | [H : least_gen _ _ ?p |- _] => unfolds in H ;
              let H1 := fresh "H1" in
                let H2 := fresh "H2" in
                  let H3 := fresh "H3" in
                    destruct H as [H1 [H2 H3]]
      | [p : (ty * gen_list)%type |- _] => let t := fresh "t" in destruct p as [p t] ; simpl in *  
      end.

Ltac my_simpl :=  
  try (repeat (unfold least_gen ; simpl ; s)) ; eauto.

Definition lgen_aux : forall (l : gen_list) (t1 t2 : ty), 
  wf_gen_list l -> {p | least_gen t1 t2 (@fst ty gen_list p)}.
   intros l t1 t2 Hwf ; 
   refine ((fix F (t1 t2 : ty) (l : gen_list) :  {p | least_gen t1 t2 (@fst ty gen_list p)} :=
     match t1,t2 
       return {p | least_gen t1 t2 (@fst ty gen_list p)} with
       | tvar n, tvar n' => 
           match lookup_gen_list _ (tvar n) (tvar n') with
             | inleft (exist t _) => exist _ (t,l) _
             | inright _  =>
                  match fresh (tvar n) (tvar n') l with
                    | exist x _ => exist _ ((tvar x), ((tvar n, tvar n', tvar x) :: l)) _
                  end
           end
       | tvar n, tcon n' => 
            match lookup_gen_list _ (tvar n) (tcon n') with
              | inleft (exist t _) => exist _ (t,l) _
              | inright _ => 
                   match fresh (tvar n) (tvar n') l with
                     | exist x _ => exist _ ((tvar x), ((tvar n, tcon n', tvar x) :: l)) _
                   end
            end
       | tvar n, tapp f r => 
            match lookup_gen_list _ (tvar n) (tapp f r) with
              | inleft (exist t _) => exist _ (t,l) _
              | inright _ =>
                match fresh (tvar n) (tapp f r) l with
                  | exist x _ => exist _ ((tvar x), ((tvar n, tapp f r, tvar x) :: l)) _
                end
            end
       | tcon n, tvar n' => 
            match lookup_gen_list _ (tcon n) (tvar n') with
              | inleft (exist t _) => exist _ (t,l) _
              | inright _ =>
                  match fresh (tcon n) (tvar n') l with
                    | exist x _ => exist _ ((tvar x), ((tcon n, tvar n', tvar x) :: l)) _
                  end
            end
       | tcon n, tcon n' => 
            match eq_nat_dec n n' with
              | left _ => exist _ ((tcon n), l) _
              | right _ => 
                match lookup_gen_list _ (tcon n) (tcon n') with
                  | inleft (exist t _) => exist _ (t,l) _
                  | inright _ =>
                        match fresh (tcon n) (tcon n') l with
                          | exist x _ => exist _ ((tvar x), ((tcon n, tcon n', tvar x) :: l)) _
                        end
                end
            end
       | tcon n, tapp f r => 
            match lookup_gen_list _ (tcon n) (tapp f r) with
              | inleft (exist t _) => exist _ (t,l) _
              | inright _ =>
                 match fresh (tcon n) (tapp f r) l with
                   | exist x _ => exist _ ((tvar x), ((tcon n, tapp f r, tvar x) :: l)) _
                 end
            end
       | tapp f r, tvar n' => 
            match lookup_gen_list _ (tapp f r) (tvar n') with
              | inleft (exist t _) => exist _ (t,l) _
              | inright _ =>
                match fresh (tapp f r) (tvar n') l with
                  | exist x _ => exist _ ((tvar x), (tapp f r, tvar n', tvar x) :: l) _
                end
            end
       | tapp f r, tcon n' => 
            match lookup_gen_list _ (tapp f r) (tcon n') with
              | inleft (exist t _) => exist _ (t,l) _
              | inright _ =>
                 match fresh (tapp f r) (tvar n') l with
                   | exist x _ => exist _ ((tvar x), (tapp f r, tcon n', tvar x) :: l) _
                 end
            end
       | tapp f r, tapp f' r' => 
            match F f f' l with
              | exist p _ => 
                match F r r' (snd p) with
                  | exist p' _ => exist _ (tapp (fst p) (fst p'), snd p') _
                end
            end
     end) t1 t2 l) ; my_simpl.
Defined. 

Definition lgen (t t' : ty) := lgen_aux t t' nil.