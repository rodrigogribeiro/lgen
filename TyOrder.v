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

    (** Definition of alpha-equivalence between types **)

    Definition renaming_subst (s : subst) := forall n t, M.find n s = Some t -> exists v, t = tvar v.

    Remark null_subst_is_renaming : renaming_subst (@M.empty ty).
    Proof.
      unfolds ; introv H.
      rewrite empty_o in H. congruence.
    Qed.

    Remark compose_renaming : forall (s1 s2 : subst), renaming_subst s1 -> renaming_subst s2 -> renaming_subst (s1 @@ s2).
    Proof.
      introv H1 H2 ; unfold renaming_subst in * ; introv H3.
      admit.
    Qed.

    Inductive alpha_eq : ty -> ty -> Prop :=
      | ae_var : forall n n', alpha_eq (tvar n) (tvar n')
      | ae_con : forall n n', n = n' -> alpha_eq (tcon n) (tcon n')
      | ae_app : forall t1 t2 t1' t2',  alpha_eq t1 t1' ->
                                        alpha_eq t2 t2' ->
                                        alpha_eq (tapp t1 t2) (tapp t1' t2').

    Theorem alpha_eq_is_renaming : 
      forall t t', alpha_eq t t' <-> exists s, renaming_subst s /\ apply_subst_on_ty s t = t'.
    Proof.
      intros t t' ; split ; intros H ; [induction H | idtac].
        exists (M.add n (tvar n') (@M.empty ty)) ; split.
          unfolds. introv H. rewrite add_o in H.
          cases_if in H. inverts* H. 
          rewrite empty_o in H. congruence.
          simpl. rewrite add_o. cases_if*.         
        subst. exists (@M.empty ty) ; split ; [apply null_subst_is_renaming | auto].
        destruct IHalpha_eq1 as [s1 [Hr1 Ha1]].
        destruct IHalpha_eq2 as [s2 [Hr2 Ha2]].
        exists (s2 @@ s1) ; split. applys* compose_renaming. rewrite compose_apply ; auto.
        simpl. admit.
      admit.
    Qed.
End TYORDER.
