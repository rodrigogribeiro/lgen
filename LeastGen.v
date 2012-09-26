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
  snd (lgen_aux t t' (empty_state t t')).

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
       | [s : state |- _] => destruct s ; simpl in *
     end) ; simpl ; auto.
  
  (** first property: generalization **)

  Theorem lgen_is_gen : forall t t' s, exists s' t1, lgen_aux t t' s = (s',t1) /\ t1 <=: t /\ t1 <=: t'.
  Proof.
    intros t ; induction t ; intros t' ; destruct t' ; my_simpl.
    Focus 9.
    intros s.
    destruct (IHt1 t'1 s) as [s1 [t11 [H1 [H2 H3]]]] ; clear IHt1.
    destruct (IHt2 t'2 s1) as [s2 [t22 [H4 [H5 H6]]]] ; clear IHt2.
    exists s2 (tapp t11 t22) ; splits. unfolds.
    rewrite H1. rewrite H2.
    cases* (lgen_aux t1 t'1 s) as H7. cases* (lgen_aux t2 t'2 s0) as H8.
    unfolds.
    rewrite H1 ; clear H1. rewrite H2.
  Qed.

  Theorem lgen_is_unique : forall t t' s, exists s' t1, lgen_aux t t' = (s',t1) /\
    forall u, u <=: t /\ u <=: t' -> u <=: t1.
  Proof.
  Qed.
 
End LGEN_Properties.







