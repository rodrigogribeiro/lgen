Require Import LibTactics Ty Subst.

Include SUBST.

Module TYORDER.
    Definition leq_ty (t t' : ty) := exists (s : subst), apply_subst_on_ty s t = t'.
    
    Notation "t '<=:' t'" := (leq_ty t t') (at level 60).

    (** proving that <=: is pre-order **)

    Lemma leq_ty_refl : forall t, t <=: t.
    Proof.
      intros t ; exists (M.empty ty) ; induction t ; simpl ; auto.
      rewrite IHt1 ; rewrite* IHt2.
    Qed.

    Lemma leq_ty_trans : forall t1 t2 t3, t1 <=: t2 -> t2 <=: t3 -> t1 <=: t3.
    Proof.
      introv H1 H2 ; unfold leq_ty in *.
      destruct H1 as [s1 H1] ; destruct H2 as [s2 H2].
      exists (s1 @@ s2).
      rewrite compose_apply.
      rewrite* <- H1 in H2.
    Qed.
    
    (** some inversion lemmas **)

    Lemma leq_var_inv_r : forall t n, t <=: (tvar n) -> exists n', t = (tvar n').
    Proof.
      introv H. unfolds in H.
      destruct H as [s H].
      induction t ; try (inverts* H ; fail).
    Qed.

    Lemma leq_var_inv_l : forall t n n', t = (tvar n') -> t <=: (tvar n).
    Proof.
      intros t n n' H ; subst ; unfolds ; 
        exists (M.add n' (tvar n) (@M.empty ty)) ; simpl ; rewrite add_o ; cases_if*.
    Qed.

    Lemma leq_con_inv_r : forall t n, t <=: (tcon n) -> t = tcon n \/ exists n', t = tvar n'.
    Proof.
      introv H. unfolds in H. destruct H as [s H]. induction t ; try (inverts* H ; fail).
    Qed.

    Lemma leq_app_inv_r : forall t l r, t <=: (tapp l r) -> (exists l' r', t = tapp l' r') \/ (exists n', t = tvar n').
    Proof.
      introv H. unfolds in H. destruct H as [s H]. induction t ; try (inverts* H ; fail).
    Qed.

    Lemma subst_app_compat : forall l l' r r' s, apply_subst_on_ty s (tapp l r) = (tapp l' r') <->
                                                 apply_subst_on_ty s l = l' /\ apply_subst_on_ty s r = r'.
    Proof.
      intros l l' r r' s ; split ; intros H ; inverts* H.
    Qed.
                         
End TYORDER.
