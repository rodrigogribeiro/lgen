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

Inductive in_gen_list (t t' t1 : ty) : gen_list -> Prop :=
  | igl_here : forall l, in_gen_list t t' t1 ((t,t',t1) :: l)
  | igl_nextl : forall l a b c, a <> t -> b = t' -> in_gen_list t t' t1 l ->
                                                 in_gen_list t t' t1 ((a,b,c) :: l)
  | igl_nextr : forall l a b c, a = t ->  b <> t' -> in_gen_list t t' t1 l ->
                                                     in_gen_list t t' t1 ((a,b,c) :: l)
  | igl_nextb : forall l a b c, a <> t -> b <> t' -> in_gen_list t t' t1 l ->
                                                     in_gen_list t t' t1 ((a,b,c)::l).


Hint Constructors in_gen_list.

Definition lookup_gen_list : forall (t t' : ty) (l : gen_list), 
  {t1 | in_gen_list t t' t1 l} +
  {~ exists t1, in_gen_list t t' t1 l}.
  refine (fix F (t t' : ty) (l : gen_list) {struct l} : 
    {t1 | in_gen_list t t' t1 l} + {~ exists t1, in_gen_list t t' t1 l} :=
    match l return {t1 | in_gen_list t t' t1 l} + {~ exists t1, in_gen_list t t' t1 l} with
      | nil => inright _ _
      | (a,b,c) :: l'   => match eq_ty_dec a t, eq_ty_dec b t' with 
                             | left _, left _ => inleft _ _
                             | left _, right _ => match F t t' l' with
                                                    | inleft _  => inleft _ _
                                                    | inright _ => inright _ _
                                                  end
                             | right _, left _ => match F t t' l' with
                                                    | inleft _ => inleft _ _
                                                    | inright _ => inright _ _
                                                  end
                             | right _, right _ =>  match F t t' l' with
                                                    | inleft _ => inleft _ _
                                                    | inright _ => inright _ _
                                                  end
                           end    
    end) ; try (intro H ; destruct H as [t1 H]) ; subst ; try congruence.  
    inverts* H. 
    exists* c. destruct s as [t1 Hs].
    exists* t1.
    inverts* H.
    destruct s as [t1 Hs]. exists* t1.
    inverts * H.
    destruct s as [t1 Hs]. exists* t1.
    inverts* H. 
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
     t <=: t1 /\ t <=: t2 /\ forall u, u <=: t1 /\ u <=: t2 -> u <=: t.

Ltac s :=
    match goal with
      | [H : _ /\ _ |- _] => destruct H
      | [H : ex _ |- _] => destruct H
    end.

Ltac my_simpl := try (repeat s).

Definition lgen_aux : forall (t1 t2 : ty) (l : gen_list), {p | least_gen t1 t2 (@fst ty gen_list p) /\ exists l', (@snd ty gen_list p) = l' ++ l}.
   refine (fix F (t1 t2 : ty) (l : gen_list) : {p | least_gen t1 t2 (@fst ty gen_list p) /\ exists l', (@snd ty gen_list p) = l' ++ l} :=
     match t1,t2 return {p | least_gen t1 t2 (@fst ty gen_list p) /\ exists l', (@snd ty gen_list p) = l' ++ l} with
       | tvar n, tvar n' => 
           match lookup_gen_list (tvar n) (tvar n') l with
             | inleft (exist t _) => exist _ (t,l) _
             | inright _  =>
                  match fresh (tvar n) (tvar n') l with
                    | exist x _ => exist _ ((tvar x), ((tvar n, tvar n', tvar x) :: l)) _
                  end
           end
       | tvar n, tcon n' => 
            match lookup_gen_list (tvar n) (tcon n') l with
              | inleft (exist t _) => exist _ (t,l) _
              | inright _ => 
                   match fresh (tvar n) (tvar n') l with
                     | exist x _ => exist _ ((tvar x), ((tvar n, tcon n', tvar x) :: l)) _
                   end

            end
       | tvar n, tapp f r => 
            match lookup_gen_list (tvar n) (tapp f r) l with
              | inleft (exist t _) => exist _ (t,l) _
              | inright _ =>
                match fresh (tvar n) (tapp f r) l with
                  | exist x _ => exist _ ((tvar x), ((tvar n, tapp f r, tvar x) :: l)) _
                end
            end
       | tcon n, tvar n' => 
            match lookup_gen_list (tcon n) (tvar n') l with
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
                match lookup_gen_list (tcon n) (tcon n') l with
                  | inleft (exist t _) => exist _ (t,l) _
                  | inright _ =>
                        match fresh (tcon n) (tcon n') l with
                          | exist x _ => exist _ ((tvar x), ((tcon n, tcon n', tvar x) :: l)) _
                        end
                end
            end
       | tcon n, tapp f r => 
            match lookup_gen_list (tcon n) (tapp f r) l with
              | inleft (exist t _) => exist _ (t,l) _
              | inright _ =>
                 match fresh (tcon n) (tapp f r) l with
                   | exist x _ => exist _ ((tvar x), ((tcon n, tapp f r, tvar x) :: l)) _
                 end
            end
       | tapp f r, tvar n' => 
            match lookup_gen_list (tapp f r) (tvar n') l with
              | inleft (exist t _) => exist _ (t,l) _
              | inright _ =>
                match fresh (tapp f r) (tvar n') l with
                  | exist x _ => exist _ ((tvar x), (tapp f r, tvar n', tvar x) :: l) _
                end
            end
       | tapp f r, tcon n' => 
            match lookup_gen_list (tapp f r) (tcon n') l with
              | inleft (exist t _) => exist _ (t,l) _
              | inright _ =>
                 match fresh (tapp f r) (tvar n') l with
                   | exist x _ => exist _ ((tvar x), (tapp f r, tcon n', tvar x) :: l) _
                 end
            end
       | tapp f r, tapp f' r' => 
            match F f f' l with
              | exist p _ => match F r r' (snd p) with
                               | exist p' _ => exist _ (tapp (fst p) (fst p'), snd p') _
                             end
            end
     end) ; unfold least_gen ; try (repeat split) ; simpl fst in * ; 
             try intros ; my_simpl ; try (exists* (@nil (ty * ty * ty)) ; fail).
          destruct (leq_var_inv_r _ _ H) ; subst.
          exists (M.add x (tvar x0) (@M.empty ty)). simpl. rewrite add_o. 
          destruct* (eq_dec x x). 
          destruct H. destruct (leq_var_inv_r _ _ H1) ; subst.
          exists (M.add x1 (tvar x) (@M.empty ty)). simpl. rewrite add_o. 
          destruct* (eq_dec x1 x1).
          exists* ((tvar n, tvar n', tvar x) :: nil).
          destruct (leq_var_inv_r _ _ H) ; subst.
          destruct (leq_con_inv_r _ _ H2) ; subst.
          destruct H1 as [s1 H1] ; inverts* H1.
          destruct H3 as [n1 H3] ; subst.
          exists (M.add n1 (tvar x) (@M.empty ty)). simpl. rewrite add_o.
          destruct* (eq_dec n1 n1).
          destruct (leq_var_inv_r _ _ H1) ; subst.
          destruct (leq_con_inv_r _ _ H2) ; subst.
          congruence.
          exists (M.add x0 (tvar x) (@M.empty ty)). simpl. rewrite add_o.
          destruct* (eq_dec x0 x0).
          exists* ((tvar n, tcon n', tvar x) :: nil).
          destruct (leq_var_inv_r _ _ H) ; subst.
          destruct (leq_var_inv_r _ _ H1) ; subst.
          exists (M.add x0 (tvar x) (@M.empty ty)). simpl. rewrite add_o.
          destruct* (eq_dec x0 x0).
          destruct (leq_var_inv_r _ _ H1) ; subst.
          exists (M.add x0 (tvar x) (@M.empty ty)). simpl. rewrite add_o.
          destruct* (eq_dec x0 x0).
          exists* ((tvar n, tapp f r, tvar x) :: nil).       
          destruct (leq_var_inv_r _ _ H0) ; subst.
          destruct (leq_var_inv_r _ _ H2) ; subst.
          exists (M.add x0 (tvar x) (@M.empty ty)). simpl. rewrite add_o.
          destruct* (eq_dec x0 x0).
          destruct (leq_var_inv_r _ _ H2) ; subst.
          exists (M.add x0 (tvar x) (@M.empty ty)). simpl. rewrite add_o.
          destruct* (eq_dec x0 x0).
          exists* ((tcon n, tvar n', tvar x) :: nil).
          subst. 
          destruct (leq_con_inv_r _ _ H1) ; subst.
          apply leq_ty_refl.
          destruct H3 as [n1 H3] ; subst.
          exists (M.add n1 (tcon n') (@M.empty ty)). simpl. rewrite add_o.
          destruct* (eq_dec n1 n1).
          destruct (leq_con_inv_r _ _ H) ; subst.
          destruct H as [s1 H]. simpl in H.
          congruence. destruct H3 as [n1 H3] ; subst.
          destruct (leq_con_inv_r _ _ H1) ; subst.
          destruct H2 as [n2 H2] ; simpl in H2 ; congruence.
          destruct H3 as [n3 H3] ; subst.
          exists (M.add n3 (tvar n1) (@M.empty ty)). simpl. rewrite add_o.
          destruct* (eq_dec n3 n3).
          destruct (leq_con_inv_r _ _ H1) ; subst.
          destruct H2 as [n2 H2] ; simpl in H2 ; congruence.
          destruct H3 as [n3 H3] ; subst.
          exists (M.add n3 (tvar x) (@M.empty ty)). simpl. rewrite add_o.
          destruct* (eq_dec n3 n3).
          exists* ((tcon n, tcon n', tvar x) :: nil).
          destruct (leq_con_inv_r _ _ H) ; subst.
          destruct H0 as [s1 H0] ; inverts* H0.
          destruct H3 as [n1 H3] ; subst.
          destruct (leq_app_inv_r _ _ _ H2) ; subst.
          destruct H3 as [l1 [r1 H3]] ; subst.
          destruct H1 as [s1 H1] ; inverts* H1.
          destruct H3 as [n2 H3] ; subst.
          exists (M.add n2 (tvar n1) (@M.empty ty)). simpl. rewrite add_o.
          destruct* (eq_dec n2 n2).     
          destruct (leq_app_inv_r _ _ _ H2) ; subst.
          destruct H3 as [l1 [r1 H3]] ; subst.
          destruct H1 as [s1 H1] ; inverts* H1.
          destruct H3 as [n2 H3] ; subst.
          exists (M.add n2 (tvar x) (@M.empty ty)). simpl. rewrite add_o.
          destruct* (eq_dec n2 n2).
          exists* ((tcon n, tapp f r, tvar x) :: nil).
          destruct (leq_app_inv_r _ _ _ H).
          destruct H3 as [l1 [r1 H3]] ; subst.
          destruct H0 as [s1 H0] ; inverts* H0.
          destruct H3 as [n1 H3] ; subst.
          destruct (leq_app_inv_r _ _ _ H1).
          destruct H3 as [l1 [r1 H3]] ; subst.
          destruct H2 as [s1 H2] ; inverts* H2.
          destruct H3 as [n3 H3] ; subst.
          exists (M.add n3 (tvar n1) (@M.empty ty)). simpl. rewrite add_o.
          destruct* (eq_dec n3 n3).     
          destruct (leq_var_inv_r _ _ H2) ; subst.
          exists (M.add x0 (tvar x) (@M.empty ty)). simpl. rewrite add_o.
          destruct* (eq_dec x0 x0).
          exists* ((tapp f r, tvar n', tvar x) :: nil).
          destruct (leq_app_inv_r _ _ _ H).
          destruct H3 as [l1 [r1 H3]] ; subst.
          destruct H0 as [s0 H0] ; inverts* H0.
          destruct H3 as [n1 H3] ; subst.
          destruct (leq_con_inv_r _ _ H2) ; subst.
          destruct H1 as [s1 H1] ; inverts* H1.
          destruct H3 as [n3 H3] ; subst.
          exists (M.add n3 (tvar n1) (@M.empty ty)). simpl. rewrite add_o.
          destruct* (eq_dec n3 n3).          
          destruct (leq_con_inv_r _ _ H2) ; subst.
          destruct H1 as [s1 H1] ; inverts* H1.
          destruct H3 as [n3 H3 ] ; subst.
          exists (M.add n3 (tvar x) (@M.empty ty)). simpl. rewrite add_o.
          destruct* (eq_dec n3 n3).
          exists* ((tapp f r, tcon n', tvar x) :: nil).   
          
          destruct p ; destruct p'. simpl fst in *. simpl snd in *.
          unfolds in H3 ; unfolds in H5 ; unfolds in H1 ; unfolds in H2.
          destruct (leq_app_inv_r _ _ _ H1).
          destruct H7 as [l1 [r1 H7]] ; subst. 
          destruct H1 as [s1 H1]. destruct H2 as [s2 H2].
          destruct (subst_app_compat _ _ _ _ _ H1) as [H11 H12].
          destruct H2 as [s2 H2].
          apply subst_app_compat in H2. destruct H1 as [H11 H12] ; destruct H2 as [H21 H22].
          destruct H as [s3 H] ; apply subst_app_compat in H ; destruct H as [H31 H32].
          destruct H0 as [s4 H0] ; apply subst_app_compat in H0 ; destruct H0 as [H41 H42].
          
          destruct (leq_app_inv _ _ _ _ H) as [s1 [H11 H12]].
          destruct (leq_app_inv _ _ _ _ H0) as [s2 [H21 H22]].
          destruct (leq_app_inv _ _ _ _ H1) as [s3 [H31 H32]].
          destruct (leq_app_inv _ _ _ _ H2) as [s4 [H41 H42]].
          apply (H5 H11) with (u := l1) in H21.
          apply (H3 H12) with (u := r1) in H22.
          apply leq_app_inv1 ; auto.
          splits*. splits*.
          destruct H7 as [n3 H7] ; subst.
          exists (M.add n3 (tapp t t0) (@M.empty ty)). simpl. rewrite add_o.
          destruct* (eq_dec n3 n3). 
          destruct p ; destruct p' ; simpl fst in *; simpl snd in *.
          exists (x ++ x0). rewrite H0. rewrite H2. rewrite app_assoc.
          auto.
 Defined. 

Definition lgen (t t' : ty) := lgen_aux t t' nil.