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
End TYORDER.
