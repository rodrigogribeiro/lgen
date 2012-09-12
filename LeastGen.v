Set Implicit Arguments.

Require Import Recdef List.

Require Import LibTactics.
Require Import TyOrder Subst Ty Monad Arith_base.

Include SUBST.
Include TYORDER.

Fixpoint lgen_aux (t t' : ty) : M ty :=
  match t,t' with
    | tvar n, tvar n' => 
      _ <- freshVar ;
      _ <- freshVar ;
      lookup_gen (tvar n) (tvar n')
    | tvar n, tcon n' =>
      _ <- freshVar ;
      lookup_gen (tvar n) (tcon n')
    | tvar n, tapp l r =>
      _ <- freshVar ;
      lookup_gen (tvar n) (tapp l r)
    | tcon n, tvar n' =>
      _ <- freshVar ;
      lookup_gen (tcon n) (tvar n')
    | tcon n, tcon n' =>
      if eq_nat_dec n n' then 
        ret (tcon n) 
        else 
          lookup_gen (tcon n) (tcon n')
    | tcon n, tapp l r =>
      lookup_gen (tcon n) (tapp l r)
    | tapp l r, tvar n =>
      _ <- freshVar  ;
      lookup_gen (tapp l r) (tvar n)
    | tapp l r, tcon n =>
      lookup_gen (tapp l r) (tcon n)
    | tapp l r, tapp l' r' =>
      lg <- lgen_aux l l' ;
      rg <- lgen_aux r r' ;
      ret (tapp lg rg)
  end.

Definition lgen (t t' : ty) : ty :=
  snd (lgen_aux t t' (mkState 0 nil)).

Section LGEN_Properties.
 Ltac my_simpl := 
   repeat (
     match goal with
       | [H : (tcon _) <=: (tvar _) |- _] => destruct H as [x Hx] ; inverts Hx
       | [H : (tapp _ _) <=: (tvar _) |- _] => destruct H as [x Hx] ; inverts Hx
       | [H : (tapp _ _) <=: (tcon _) |- _] => destruct H as [x Hx] ; inverts Hx
       | [H : (tcon _) <=: (tapp _ _) |- _] => destruct H as [x Hx] ; inverts Hx
       | [|- exists _, TyOrder.apply_subst_on_ty _ (tvar ?n) = ?s] => 
         exists (M.add n s (@M.empty ty)) ; simpl ; rewrite add_o ; case_if*
     end).
  
  (** first property: generalization **)

  Theorem lgen_is_gen : forall t t' s, lgen t t' = s -> s <=: t /\ s <=: t'.
  Proof.
    intros t ; induction t ; intros t' s H ; split ; 
      cases* t' as Ht ; inverts H ; unfolds ; unfold lgen ; simpl.

    exists (M.add 2 (tvar n) (@M.empty ty)). rewrite add_o. case_if*.
     
    exists (M.add 1 (tvar n) (@M.empty ty)). rewrite add_o. case_if*.

    exists (M.add 1 (tvar n) (@M.empty ty)). rewrite add_o. case_if*.

    exists (M.add 2 (tvar n0) (@M.empty ty)). rewrite add_o. case_if*.
    
    exists (M.add 1 (tcon n0) (@M.empty ty)). rewrite add_o. case_if*.

    exists (M.add 1 (tapp TEMP1 TEMP2) (@M.empty ty)). rewrite add_o. case_if*.

    exists (M.add 1 (tcon n) (@M.empty ty)). rewrite add_o. case_if*.

    exists (M.add 0 (tcon n) (@M.empty ty)). case_if*.

    exists (M.add 0 (tcon n) (@M.empty ty)). rewrite add_o. case_if*.

    exists (M.add 1 (tvar n0) (@M.empty ty)). rewrite add_o. case_if*.

    case_if*. exists (@M.empty ty). simpl. auto.

    simpl. exists (M.add 0 (tcon n0) (@M.empty ty)). rewrite add_o. case_if*.
    
    exists (M.add 0 (tapp TEMP1 TEMP2) (@M.empty ty)). rewrite add_o. case_if*.

    exists (M.add 1 (tapp t1 t2) (@M.empty ty)). rewrite add_o. case_if*.

    exists (M.add 0 (tapp t1 t2) (@M.empty ty)). rewrite add_o. case_if*.

    admit.

    exists (M.add 1 (tvar n) (@M.empty ty)). rewrite add_o. case_if*.
    
    exists (M.add 0 (tcon n) (@M.empty ty)). rewrite add_o. case_if*.

    admit.
  Qed. 

  Theorem lgen_is_least : forall t t' s, lgen t t' = s -> forall u, u <=: t /\ u <=: t' -> u <=: s.
  Proof.
    intro t ; induction t ; intros t' s H ; destruct t' ; intros u [Hu1 Hu2] ; destruct* u ; unfolds ; try my_simpl.

    destruct Hu1 as [s1 Hu1]. destruct Hu2 as [s2 Hu2]. simpl in Hu1, Hu2.
    rewrite <- Hu1 in H. rewrite Hu2 in H. unfolds in H. simpl in H. cases_if*.
    simpl in H. subst. rewrite Hu2. exists (@M.empty ty). auto.

  Qed.
End LGEN_Properties.







