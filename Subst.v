Require Import LibTactics Ty.
Require Import OrderedTypeEx FMapInterface FMapAVL FMapFacts Arith_base.

(** substitution and its operations **)

Module Nat_as_UOT <: UsualOrderedType := Nat_as_OT.

Module M <: FMapInterface.S := FMapAVL.Make Nat_as_OT.

Module SUBST.
  Module MapFacts := WFacts_fun (M.E) (M).
  
  Include MapFacts.

  Definition subst := M.t ty.

  Definition id_subst := (@M.empty ty).

  Definition dom (s : subst) := map (fun t => fst t) (M.elements s).

  Fixpoint apply_subst_on_ty (s : subst) (t : ty) : ty :=
      match t with
        | tvar v => match (M.find v s) with
                      | None => tvar v
                      | Some t' => t'
                    end
        | tcon c => tcon c
        | tapp l r => tapp (apply_subst_on_ty s l) (apply_subst_on_ty s r)
      end.

  Notation "s '#' t" := (apply_subst_on_ty s t) (at level 60).
  
  Definition apply_subst_to_subst (s1: subst) (s2: subst) := 
      M.map (apply_subst_on_ty s2) s1.

  Definition choose_subst (t1: option ty) (t2:option ty) :=
      match (t1,t2) with
        | (Some t3, Some t4) => Some t3
        | (Some t3, None) => Some t3
        | (None, Some t3) => Some t3
        | (None, None) => None
      end.

    Definition subst_diff (s1 : subst) (s2 : subst) := 
      M.map2 choose_subst s1 s2. 

    Definition compose_subst (s1 : subst) (s2 : subst) :=
      subst_diff (apply_subst_to_subst s1 s2) s2.

    Notation "s1 '@@' s2" := (compose_subst s1 s2) (at level 60, right associativity).

    Lemma membership_and_apply_subst_to_subst:
      forall (s1 s2 : subst) (n : nat), M.In n s1 /\ M.In n (s1 @@ s2) 
        -> M.In n (apply_subst_to_subst s1 s2).
    Proof.
      intros s1 s2 n [H1 H2].
      unfold compose_subst in H2.
      unfold subst_diff in H2.
      apply M.map2_2 in H2.
      destruct* H2.
      unfold apply_subst_to_subst.
      unfold M.In.
      unfold M.In in H1. destruct H1 as [t H1].
      exists (apply_subst_on_ty s2 t).
      applys* M.map_1.      
    Qed.


    Lemma map_and_mapsto : forall (s1 s2 : subst) (n : nat) (t t' : ty),
      M.MapsTo n t' s1  /\  M.MapsTo n t (s1 @@ s2)
           ->  t = apply_subst_on_ty s2 t'.
    Proof.
      intros s1 s2 n t t' [H1 H2]. 
      apply M.map_1 with (f:= apply_subst_on_ty s2) in H1.
      unfold compose_subst,subst_diff in H2.
      apply M.find_1 in H2.
      rewrite M.map2_1 in H2.
      unfold apply_subst_to_subst in H2.
      apply M.find_1 in H1.
      rewrite H1 in H2.
      cases (M.find n s2).
      unfold choose_subst in H2.
      inverts* H2.
      inverts* H1. unfold choose_subst in H2.     
      inverts* H2.
      branch* 1.
      apply membership_and_apply_subst_to_subst ; split.
      apply M.map_2 with (f:= apply_subst_on_ty s2).
      unfold M.In.
      exists (apply_subst_on_ty s2 t'); auto.
      apply M.find_2 in H2.
      unfold compose_subst, subst_diff.
      unfold M.In; exists t; auto.
    Qed.

    Lemma find_and_map_apply : forall (s1 s2 : subst) (n : nat),
      M.find n s1 = None -> M.find n (M.map (apply_subst_on_ty s2) s1) = None. 
    Proof.
      intros.
      assert (not (M.In n s1)).
      unfold not.
      intros.
      unfold M.In in H0.
      elim H0; intros.
      apply M.find_1 in H1.
      rewrite H in H1. congruence.    
      cases (M.find n (M.map (apply_subst_on_ty s2) s1)) as H1.
      apply M.find_2 in H1.
      assert ((M.In n (M.map (apply_subst_on_ty s2) s1))).
      unfold M.In.
      exists* t. 
      apply M.map_2 in H2.
      unfold M.In in H2.
      elim H2 ; intros.
      apply M.find_1 in H3.
      rewrite H3 in H. congruence.
      reflexivity.
    Qed.    

    Lemma membership_and_apply_subst_to_subst_with_map:
      forall (s1 s2 : subst) (n : nat), M.In n s1 -> M.In n (s1 @@ s2).
    Proof.
      intros.
      unfold compose_subst, subst_diff, apply_subst_to_subst.
      unfold M.In in *.
      destruct H as [t H].
      exists (apply_subst_on_ty s2 t).
      apply M.find_2.
      rewrite M.map2_1.
      unfold choose_subst.
      cases (M.find n (M.map (apply_subst_on_ty s2) s1)) as H1.
      cases (M.find n s2) as H2. fequals.
      apply M.find_2 in H2.
      apply M.map_1 with (f:= apply_subst_on_ty s2) in H.
      apply M.find_1 in H.
      apply M.find_1 in H2.
      rewrite H in H1.
      congruence.
      fequals.
      apply M.find_2 in H1.
      apply M.map_1 with (f:= apply_subst_on_ty s2) in H.
      apply M.find_1 in H.
      apply M.find_1 in H1.
      rewrite H1 in H. congruence.
      apply M.map_1 with (f:= apply_subst_on_ty s2) in H.
      apply M.find_1 in H.
      rewrite H1 in H. congruence.
      left.
      apply  M.map_1 with (f:= apply_subst_on_ty s2) in H.
      unfold M.In.
      exists* (apply_subst_on_ty s2 t).
    Qed.

    Theorem compose_apply : forall (s1 s2 : subst) (t : ty), 
      apply_subst_on_ty (s1 @@ s2) t = apply_subst_on_ty s2 (apply_subst_on_ty s1 t).
    Proof.
      intros s1 ; induction t ; simpl ; auto.
      cases (M.find n (s1 @@ s2)) as H.
      cases (M.find n s1) as H1.
      apply M.find_2 in H. apply M.find_2 in H1.
      apply map_and_mapsto with (s1 := s1) (n := n) ; jauto.
      cases (M.find n s2) as H2.
      unfold compose_subst, subst_diff, apply_subst_to_subst in H.
      rewrite M.map2_1 in H.
      rewrite H2 in H. unfold choose_subst in H.
      apply find_and_map_apply with (s2 := s2) in H1.
      rewrite H1 in H. inverts* H.
      simpl. rewrite* H2.
      branch* 2. apply M.find_2 in H2 ; unfold M.In ; eexists ; eauto.
      unfold compose_subst, subst_diff in H.
      assert (not (M.In n s1)).
      intro H3. unfold M.In in H3.
      destruct* H3 as [t' H3].
      apply M.find_1 in H3.
      congruence.
      apply M.find_2 in H.
      assert (M.In n  (M.map2 choose_subst (apply_subst_to_subst s1 s2) s2)).
      unfold M.In.
      exists* t.
      apply M.map2_2 in H3.
      destruct* H3.
      unfold apply_subst_to_subst in H3.
      apply M.map_2 in H3. contradiction.
      unfold M.In in H3.
      destruct* H3.
      apply M.find_1 in H3. congruence.
      cases (M.find n s1) as H1.
      apply M.find_2 in H1.
      assert (M.In n s1). unfold M.In ; exists* t.
      apply membership_and_apply_subst_to_subst_with_map with (s2 := s2) in H0.
      unfold M.In in H0. destruct H0 as [t' H0].
      apply M.find_1 in H0. congruence.
      cases (M.find n s2) as H2.
      apply find_and_map_apply with (s2 := s2) in H1.
      unfold compose_subst, apply_subst_to_subst, subst_diff in H.
      rewrite M.map2_1 in H. unfold choose_subst in H. rewrite H1 in H ; rewrite H2 in H.
      congruence. right. unfold M.In ; exists t ; applys* M.find_2.
      simpl. rewrite* H2. 
      rewrite IHt1 ; rewrite IHt2 ; jauto.
    Qed.

    (** restricting a substitution **)

    Definition restrict (s : subst) (vs : list nat) : subst :=
      M.fold (fun (n : nat) (t : ty) (acc : subst) => 
                if in_dec eq_nat_dec n vs then M.add n t acc else acc) (M.empty ty) s.

    Lemma restrict_idem : forall t s, apply_subst_on_ty (restrict s (fv t)) t = apply_subst_on_ty s t.
    Proof.
      intros t ; induction t ; intros s ; simpl ; auto.
    Qed.
End SUBST.

