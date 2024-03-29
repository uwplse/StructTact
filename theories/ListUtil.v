From Coq Require Import Arith Lia ZArith List.
From Coq Require Import Sorting.Permutation.
From StructTact Require Import StructTactics ListTactics.
Import ListNotations.

Set Default Proof Using "Type".

Set Implicit Arguments.

Notation member := (in_dec eq_nat_dec).

Lemma seq_range :
  forall n a x,
    In x (seq a n) ->
    a <= x < a + n.
Proof.
  induction n; intros; simpl in *.
  - intuition auto.
  - break_or_hyp; try find_apply_hyp_hyp; intuition lia.
Qed.

Lemma plus_gt_0 :
  forall a b,
    a + b > 0 ->
    a > 0 \/ b > 0.
Proof.
  intros.
  destruct (eq_nat_dec a 0); intuition lia.
Qed.

Section list_util.
  Variables A B C : Type.
  Hypothesis A_eq_dec : forall x y : A, {x = y} + {x <> y}.

  Lemma list_neq_cons :
    forall (l : list A) x,
      x :: l <> l.
  Proof.
    intros l x H.
    symmetry in H.
    induction l;
      now inversion H.
  Qed.

  Lemma remove_preserve :
    forall (x y : A) xs,
      x <> y ->
      In y xs ->
      In y (remove A_eq_dec x xs).
  Proof.
    induction xs; intros.
    - intuition auto.
    - simpl in *.
      concludes.
      break_or_hyp; break_if; subst; try congruence; intuition (auto with datatypes).
  Qed.

  Lemma in_remove :
    forall (x y : A) xs,
      In y (remove A_eq_dec x xs) ->
      In y xs.
  Proof.
    induction xs; intros.
    - auto.
    - simpl in *. break_if; simpl in *; intuition auto.
  Qed.

  Lemma remove_partition :
    forall xs (p : A) ys,
      remove A_eq_dec p (xs ++ p :: ys) = remove A_eq_dec p (xs ++ ys).
  Proof.
    induction xs; intros; simpl; break_if; congruence.
  Qed.

  Lemma remove_not_in :
    forall (x : A) xs,
      ~ In x xs ->
      remove A_eq_dec x xs = xs.
  Proof.
    intros. induction xs; simpl in *; try break_if; intuition congruence.
  Qed.

  Lemma remove_app_comm :
    forall a xs ys,
      remove A_eq_dec a (xs ++ ys) = remove A_eq_dec a xs ++ remove A_eq_dec a ys.
  Proof.
    intros.
    generalize dependent ys.
    induction xs; intros.
    - tauto.
    - destruct (A_eq_dec a0 a);
      simpl;
      break_if;
      try rewrite <- app_comm_cons;
      rewrite IHxs; 
      congruence.
  Qed.

  Lemma filter_app : forall (f : A -> bool) xs ys,
      filter f (xs ++ ys) = filter f xs ++ filter f ys.
  Proof.
    induction xs; intros.
    - auto.
    - simpl. rewrite IHxs. break_if; auto.
  Qed.

  Lemma filter_fun_ext_eq : forall f g xs,
      (forall a : A, In a xs -> f a = g a) ->
      filter f xs = filter g xs.
  Proof.
    induction xs; intros.
    - auto.
    - simpl. rewrite H by intuition (auto with datatypes). 
      rewrite IHxs by intuition (auto with datatypes). auto.
  Qed.

  Lemma not_in_filter_false :
    forall (f : A -> bool) l x,
      In x l ->
      ~ In x (filter f l) ->
      f x = false.
  Proof.
    intros.
    destruct (f x) eqn:?H; [|tauto].
    unfold not in *; find_false.
    now eapply filter_In.
  Qed.

  Lemma filter_length_bound :
    forall f (l : list A),
      length (filter f l) <= length l.
  Proof.
    induction l.
    - easy.
    - simpl.
      break_if; simpl; lia.
  Qed.

  Lemma NoDup_map_injective : forall (f : A -> B) xs,
      (forall x y, In x xs -> In y xs ->
              f x = f y -> x = y) ->
      NoDup xs -> NoDup (map f xs).
  Proof.
    induction xs; intros.
    - constructor.
    - simpl. invc_NoDup. constructor.
      + intro. do_in_map.
        assert (x = a) by intuition (auto with datatypes).
        congruence.
      + intuition (auto with datatypes).
  Qed.

  Lemma NoDup_disjoint_append :
    forall (l : list A) l',
      NoDup l ->
      NoDup l' ->
      (forall a, In a l -> ~ In a l') ->
      NoDup (l ++ l').
  Proof.
    induction l; intros.
    - auto.
    - simpl. invc_NoDup. constructor.
      + intro. do_in_app. intuition eauto with datatypes.
      + intuition eauto with datatypes.
  Qed.

  Lemma NoDup_map_partition :
    forall (f : A -> B) xs l y zs xs' y' zs',
      NoDup (map f l) ->
      l = xs ++ y :: zs ->
      l = xs' ++ y' :: zs' ->
      f y = f y' ->
      xs = xs'.
  Proof.
    induction xs; simpl; intros; destruct xs'.
    - auto.
    - subst. simpl in *. find_inversion.
      invc H. exfalso. rewrite map_app in *. simpl in *.
      repeat find_rewrite. intuition (auto with datatypes).
    - subst. simpl in *. find_inversion.
      invc H. exfalso. rewrite map_app in *. simpl in *.
      repeat find_rewrite. intuition (auto with datatypes).
    - subst. simpl in *. find_injection. intros. subst.
      f_equal. eapply IHxs; eauto. solve_by_inversion.
  Qed.

  Lemma filter_NoDup :
    forall p (l : list A),
      NoDup l ->
      NoDup (filter p l).
  Proof.
    induction l; intros.
    - auto.
    - invc_NoDup. simpl. break_if; auto.
      constructor; auto.
      intro. apply filter_In in H. intuition auto.
  Qed.

  Lemma NoDup_map_filter :
    forall (f : A -> B) g l,
      NoDup (map f l) ->
      NoDup (map f (filter g l)).
  Proof.
    intros. induction l; simpl in *.
    - constructor.
    - invc_NoDup. concludes.
      break_if; simpl in *; auto.
      constructor; auto.
      intro. do_in_map.
      find_apply_lem_hyp filter_In. intuition auto.
      match goal with | H : _ -> False |- False => apply H end.
      apply in_map_iff. eauto.
  Qed.

  Lemma filter_true_id : forall (f : A -> bool) xs,
      (forall x, In x xs -> f x = true) ->
      filter f xs = xs.
  Proof.
    induction xs; intros.
    - auto.
    - simpl. now rewrite H, IHxs by intuition (auto with datatypes).
  Qed.

  Lemma map_of_map : forall (f : A -> B) (g : B -> C) xs,
      map g (map f xs) = map (fun x => g (f x)) xs.
  Proof.
    induction xs; simpl; auto using f_equal2.
  Qed.

  Lemma filter_except_one : forall (f g : A -> bool) x xs,
      (forall y, In y xs ->
            x <> y ->
            f y = g y) ->
      g x = false ->
      filter f (remove A_eq_dec x xs) = filter g xs.
  Proof.
    induction xs; intros.
    - auto.
    - simpl.
      break_if.
      + subst. repeat find_rewrite. eauto with datatypes.
      + simpl. rewrite H by auto with datatypes.
        break_if; eauto using f_equal2 with datatypes.
  Qed.

  Lemma flat_map_nil : forall (f : A -> list B) l,
      flat_map f l = [] ->
      l = [] \/ (forall x, In x l -> f x = []).
  Proof.
    induction l; intros.
    - intuition auto.
    - right. simpl in *.
      apply app_eq_nil in H.
      intros; break_and; break_or_hyp; concludes; break_or_hyp; auto.
      contradiction.
  Qed.

  Theorem NoDup_Permutation_NoDup :
    forall (l l' : list A),
      NoDup l ->
      Permutation l l' ->
      NoDup l'.
  Proof.
    intros l l' Hnd Hp.
    induction Hp; auto; invc_NoDup; constructor;
      eauto using Permutation_in, Permutation_sym;
      simpl in *; intuition (auto with struct_util).
  Qed.

  Theorem NoDup_append :
    forall l (a : A),
      NoDup (l ++ [a]) <-> NoDup (a :: l).
  Proof. 
    intuition eauto using NoDup_Permutation_NoDup, Permutation_sym, Permutation_cons_append.
  Qed.

  Lemma NoDup_map_elim :
    forall (f : A -> B) xs x y,
      f x = f y ->
      NoDup (map f xs) ->
      In x xs ->
      In y xs ->
      x = y.
  Proof.
    induction xs; intros; simpl in *.
    - intuition auto.
    - invc_NoDup. intuition auto; subst; auto; exfalso.
      + repeat find_rewrite. auto using in_map.
      + repeat find_reverse_rewrite. auto using in_map.
  Qed.

  Lemma remove_length_not_in : forall (x : A) xs,
      ~ In x xs ->
      length (remove A_eq_dec x xs) = length xs.
  Proof.
    induction xs; intros.
    - auto.
    - simpl in *. intuition auto.
      break_if; subst; simpl; intuition auto.
  Qed.

  Lemma remove_length_in : forall (x : A) xs,
      In x xs ->
      NoDup xs ->
      S (length (remove A_eq_dec x xs)) = length xs.
  Proof.
    induction xs; intros; simpl in *; intuition; invc_NoDup;
      break_if; subst; intuition (simpl; try congruence).
    now rewrite remove_length_not_in.
  Qed.

  Lemma subset_size_eq :
    forall xs,
      NoDup xs ->
      forall ys,
        NoDup ys ->
        (forall x : A, In x xs -> In x ys) ->
        length xs = length ys ->
        (forall x, In x ys -> In x xs).
  Proof.
    induction xs; intros.
    - destruct ys; simpl in *; congruence.
    - invc_NoDup. concludes.
      assert (In a ys) by eauto with datatypes.
      find_apply_lem_hyp in_split.
      break_exists_name l1.
      break_exists_name l2.
      subst.
      specialize (IHxs (l1 ++ l2)).
      conclude_using (eauto using NoDup_remove_1).
      forward IHxs.
      intros x' Hx'.
      assert (In x' (l1 ++ a :: l2)) by eauto with datatypes.
      do_in_app. simpl in *. intuition auto with datatypes. subst. congruence.
      concludes.
      forward IHxs.
      rewrite app_length in *. simpl in *. lia.
      concludes.
      do_in_app. simpl in *. intuition auto with datatypes.
  Qed.

  Lemma remove_NoDup :
    forall (x : A) xs,
      NoDup xs ->
      NoDup (remove A_eq_dec x xs).
  Proof.
    induction xs; intros.
    - auto with struct_util.
    - invc_NoDup. simpl. break_if; eauto 6 using in_remove with struct_util.
  Qed.

  Lemma remove_length_ge : forall (x : A) xs,
      NoDup xs ->
      length (remove A_eq_dec x xs) >= length xs - 1.
  Proof.
    induction xs; intros.
    - auto.
    - invc_NoDup. simpl. break_if.
      + rewrite Nat.sub_0_r.
        subst.
        rewrite remove_length_not_in; auto.
      + simpl. concludes. lia.
  Qed.

  Lemma remove_length_le :
    forall (x : A) xs eq_dec,
      length xs >= length (remove eq_dec x xs).
  Proof.
    induction xs; intros.
    - auto.
    - simpl in *.
      specialize (IHxs eq_dec).
      break_if; subst; simpl; lia.
  Qed.

  Lemma remove_length_lt :
    forall (x : A) xs eq_dec,
      In x xs ->
      length xs > length (remove eq_dec x xs).
  Proof.
    induction xs; intros; simpl in *; [contradiction|]; break_or_hyp.
    - subst.
      break_if; try congruence.
      pose proof remove_length_le x xs eq_dec.
      lia.
    - specialize (IHxs ltac:(eauto) ltac:(eauto)).
      break_if; subst; simpl; lia.
  Qed.

  Lemma subset_length :
    forall xs ys,
      NoDup xs ->
      (forall x : A, In x xs -> In x ys) ->
      length ys >= length xs.
  Proof using A_eq_dec.
    induction xs; intros.
    - simpl. lia.
    - specialize (IHxs (remove A_eq_dec a ys)).
      invc_NoDup.
      concludes.
      forward IHxs.
      intros.
      apply remove_preserve;
       [congruence|intuition (auto with datatypes)].
      concludes.
      pose proof remove_length_lt a ys A_eq_dec.
      assert (In a ys) by auto with datatypes.
      concludes.
      simpl. lia.
  Qed.

  Lemma app_cons_singleton_inv :
    forall xs (y : A) zs w,
      xs ++ y :: zs = [w] ->
      xs = [] /\ y = w /\ zs = [].
  Proof.
    intros.
    destruct xs.
    - solve_by_inversion.
    - destruct xs; solve_by_inversion.
  Qed.

  Lemma app_cons_in :
    forall (l : list A) xs a ys,
      l = xs ++ a :: ys ->
      In a l.
  Proof.
    intros. subst. auto with datatypes.
  Qed.
  Hint Resolve app_cons_in : struct_util.

  Lemma app_cons_in_rest:
    forall (l : list A) xs a b ys,
      l = xs ++ a :: ys ->
      In b (xs ++ ys) ->
      In b l.
  Proof.
    intros. subst.
    do_in_app; intuition auto with datatypes.
  Qed.
  Hint Resolve app_cons_in_rest : struct_util.

  Lemma in_rest_app_cons:
    forall (l xs ys : list A) a b,
      l = xs ++ a :: ys ->
      In b l ->
      a <> b ->
      In b (xs ++ ys).
  Proof.
    intros.
    subst_max.
    do_in_app.
    break_or_hyp.
    - auto with datatypes.
    - find_apply_lem_hyp in_inv.
      break_or_hyp; auto using in_or_app || congruence.
  Qed.
  Hint Resolve in_rest_app_cons : struct_util.

  Lemma remove_filter_commute :
    forall (l : list A) A_eq_dec f x,
      remove A_eq_dec x (filter f l) = filter f (remove A_eq_dec x l).
  Proof.
    induction l; intros; simpl in *; auto.
    repeat (break_if; subst; simpl in *; try congruence).
  Qed.

  Lemma In_filter_In :
    forall (f : A -> bool) x l l',
      filter f l = l' ->
      In x l' -> In x l.
  Proof.
    intros. subst.
    eapply filter_In; eauto.
  Qed.

  Lemma filter_partition :
    forall (l1 : list A) f l2 x l1' l2',
      NoDup (l1 ++ x :: l2) ->
      filter f (l1 ++ x :: l2) = (l1' ++ x :: l2') ->
      filter f l1 = l1' /\ filter f l2 = l2'.
  Proof.
    induction l1; intros; simpl in *; break_if; simpl in *; invc_NoDup.
    - destruct l1'; simpl in *.
      + solve_by_inversion.
      + find_inversion. exfalso. eauto using In_filter_In with datatypes.
    - exfalso. eauto using In_filter_In with datatypes.
    - destruct l1'; simpl in *; break_and; find_inversion.
      + exfalso. eauto with datatypes.
      + find_apply_hyp_hyp. intuition auto using f_equal2.
    - eauto.
  Qed.

  Lemma map_inverses :
    forall (la : list A) (lb : list B)  (f : A -> B) g,
      (forall a, g (f a) = a) ->
      (forall b, f (g b) = b) ->
      lb = map f la ->
      la = map g lb.
  Proof.
    destruct la; intros; simpl in *.
    - subst. reflexivity.
    - destruct lb; try congruence.
      simpl in *. find_inversion.
      find_higher_order_rewrite.
      f_equal.
      rewrite map_map.
      erewrite map_ext; [symmetry; apply map_id|].
      simpl in *. auto.
  Qed.

  Lemma In_notIn_implies_neq :
    forall x y l,
      In(A:=A) x l ->
      ~ In(A:=A) y l ->
      x <> y.
  Proof.
    intuition congruence.
  Qed.

  Lemma In_cons_neq :
    forall a x xs,
      In(A:=A) a (x :: xs) ->
      a <> x ->
      In a xs.
  Proof.
    simpl.
    intuition congruence.
  Qed.

  Lemma NoDup_app3_not_in_1 :
    forall (xs ys zs : list A) b,
      NoDup (xs ++ ys ++ b :: zs) ->
      In b xs ->
      False.
  Proof.
    intros.
    rewrite app_assoc in *.
    find_apply_lem_hyp NoDup_remove.
    rewrite <- app_assoc in *.
    intuition (auto with datatypes).
  Qed.

  Lemma NoDup_app3_not_in_2 :
    forall (xs ys zs : list A) b,
      NoDup (xs ++ ys ++ b :: zs) ->
      In b ys ->
      False.
  Proof.
    intros.
    rewrite app_assoc in *.
    find_apply_lem_hyp NoDup_remove_2.
    rewrite <- app_assoc in *.
    auto 10 with datatypes.
  Qed.

  Lemma NoDup_app3_not_in_3 :
    forall (xs ys zs : list A) b,
      NoDup (xs ++ ys ++ b :: zs) ->
      In b zs ->
      False.
  Proof.
    intros.
    rewrite app_assoc in *.
    find_apply_lem_hyp NoDup_remove_2.
    rewrite <- app_assoc in *.
    auto 10 with datatypes.
  Qed.

  Lemma In_cons_2_3 :
    forall xs ys zs x y a,
      In (A:=A) a (xs ++ ys ++ zs) ->
      In a (xs ++ x :: ys ++ y :: zs).
  Proof.
    intros.
    repeat (do_in_app; intuition auto 10 with datatypes).
  Qed.

  Lemma In_cons_2_3_neq :
    forall a x y xs ys zs,
      In (A:=A) a (xs ++ x :: ys ++ y :: zs) ->
      a <> x ->
      a <> y ->
      In a (xs ++ ys ++ zs).
  Proof.
    intros.
    repeat (do_in_app; simpl in *; intuition (auto with datatypes; try congruence)).
  Qed.

  Lemma in_middle_reduce :
    forall a xs y zs,
      In (A:=A) a (xs ++ y :: zs) ->
      a <> y ->
      In a (xs ++ zs).
  Proof.
    intros.
    do_in_app; simpl in *; intuition auto with datatypes. congruence.
  Qed.

  Lemma in_middle_insert :
    forall a xs y zs,
      In (A:=A) a (xs ++ zs) ->
      In a (xs ++ y :: zs).
  Proof.
    intros.
    do_in_app; simpl in *; intuition auto with datatypes.
  Qed.

  Lemma NoDup_rev :
    forall l,
      NoDup (A:=A) l ->
      NoDup (rev l).
  Proof.
    induction l; intros; simpl.
    - auto.
    - apply NoDup_append.
      invc_NoDup.
      constructor; auto.
      intuition.
      find_apply_lem_hyp in_rev.
      auto.
  Qed.

  Lemma NoDup_map_map :
    forall (f : A -> B) (g : A -> C) xs,
      (forall x y, In x xs -> In y xs -> f x = f y -> g x = g y) ->
      NoDup (map g xs) ->
      NoDup (map f xs).
  Proof.
    induction xs; intros; simpl in *.
    - constructor.
    - invc_NoDup.
      constructor; auto.
      intro.
      do_in_map.
      find_apply_hyp_hyp.
      find_reverse_rewrite.
      auto using in_map.
  Qed.

  Lemma pigeon :
    forall (l : list A) sub1 sub2,
      (forall a, In a sub1 -> In a l) ->
      (forall a, In a sub2 -> In a l) ->
      NoDup l ->
      NoDup sub1 ->
      NoDup sub2 ->
      length sub1 + length sub2 > length l ->
      exists a, In a sub1 /\ In a sub2.
  Proof using A_eq_dec.
    induction l.
    intros.
    + simpl in *. find_apply_lem_hyp plus_gt_0. intuition.
      * destruct sub1; simpl in *; [lia|].
        specialize (H a). intuition.
      * destruct sub2; simpl in *; [lia|].
        specialize (H0 a). intuition.
    + intros. simpl in *.
      destruct (in_dec A_eq_dec a sub1);
        destruct (in_dec A_eq_dec a sub2); eauto;
          specialize (IHl (remove A_eq_dec a sub1) (remove A_eq_dec a sub2));
          cut (exists a0, In a0 (remove A_eq_dec a sub1) /\ In a0 (remove A_eq_dec a sub2));
          try solve [intros; break_exists;
                     intuition eauto using in_remove];
          apply IHl; try solve [
                           intros; find_copy_apply_lem_hyp in_remove;
                           find_apply_hyp_hyp; intuition; subst; exfalso; eapply remove_In; eauto];
          eauto using remove_NoDup; try solve_by_inversion;
            repeat match goal with
                   | H : ~ In a ?sub |- _ =>
                     assert (length (remove A_eq_dec a sub) = length sub)
                       by eauto using remove_length_not_in; clear H
                   | H : In a ?sub |- _ =>
                     assert (length (remove A_eq_dec a sub) >= length sub - 1)
                       by eauto using remove_length_ge; clear H
                   end; lia.
  Qed.

  Lemma snoc_assoc :
    forall (l : list A) x y,
      l ++ [x; y] = (l ++ [x]) ++ [y].
  Proof.
    induction l; intros; simpl; intuition.
    auto using f_equal.
  Qed.

  Lemma cons_cons_app :
    forall (x y : A),
      [x; y] = [x] ++ [y].
  Proof.
    auto.
  Qed.

  Lemma map_eq_inv :
    forall (f : A -> B) l xs ys,
      map f l = xs ++ ys ->
      exists l1 l2,
        l = l1 ++ l2 /\
        map f l1 = xs /\
        map f l2 = ys.
  Proof.
    induction l; simpl; intros xs ys H.
    - symmetry in H. apply app_eq_nil in H. break_and. subst.
      exists [], []. auto.
    - destruct xs; simpl in *.
      + exists [], (a :: l). intuition.
      + invc H. find_apply_hyp_hyp.
        break_exists_name l1.
        break_exists_name l2.
        break_and.
        exists (a :: l1), l2. subst.
        intuition.
  Qed.

  Lemma map_partition :
    forall p l (x : B) p' (f : A -> B),
      map f l = (p ++ x :: p') ->
      exists ap a ap',
        l = ap ++ a :: ap' /\
        map f ap = p /\
        f a = x /\
        map f ap' = p'.
  Proof.
    intros p l x p' f H_m.
    pose proof map_eq_inv f _ _ _ H_m.
    break_exists_name l1.
    break_exists_name l2.
    break_and.
    find_rewrite.
    destruct l2; simpl in *.
    - match goal with H : [] = _ :: _ |- _ => contradict H end.
      auto with datatypes.
    - repeat find_rewrite.
      find_inversion.
      exists l1, a, l2. auto.
  Qed.

  Lemma map_eq_inv_eq :
    forall (f : A -> B),
      (forall a a', f a = f a' -> a = a') ->
      forall l l', map f l = map f l' -> l = l'.
  Proof.
    induction l; simpl; intros l' Heq; destruct l'; simpl in *; try congruence.
    find_inversion. auto using f_equal2.
  Qed.

  Lemma map_fst_snd_id :
    forall l, map (fun t : A * B => (fst t, snd t)) l = l.
  Proof.
    intros.
    rewrite <- map_id.
    apply map_ext.
    destruct a; auto.
  Qed.

  Lemma in_firstn : forall n (x : A) xs,
      In x (firstn n xs) -> In x xs.
  Proof.
    induction n; simpl; intuition; break_match; simpl in *; intuition.
  Qed.

  Lemma firstn_NoDup : forall n (xs : list A),
    NoDup xs ->
    NoDup (firstn n xs).
  Proof.
    induction n; intros; simpl; destruct xs; auto with struct_util.
    invc_NoDup.
    eauto 6 using in_firstn with struct_util.
  Qed.

  Lemma NoDup_mid_not_in :
    forall (a : A) (l l' : list A),
    NoDup (l ++ a :: l') ->
    ~ In a (l ++ l').
  Proof.
    induction l; intros; simpl in *.
    - invc_NoDup; auto.
    - invc_NoDup.
      intro.
      break_or_hyp.
      * match goal with H: ~ In _ _ |- _ => contradict H end.
        apply in_or_app.
        right; left. auto.
      * match goal with H: In _ _ |- _ => contradict H end.
        eauto.
    Qed.

  Lemma Permutation_split :
    forall (ns ns' : list A) (n : A),
      Permutation (n :: ns) ns' ->
      exists ns0, exists ns1, ns' = ns0 ++ n :: ns1.
  Proof.
    intros l l' a H_pm.
    assert (In a (a :: l)); auto with datatypes.
    assert (In a l'); eauto using Permutation_in.
    find_apply_lem_hyp In_split; auto.
  Qed.

  Lemma NoDup_app_left :
    forall (l l' : list A),
      NoDup (l ++ l') -> NoDup l.
  Proof.
    induction l; intros; simpl in *.
    - apply NoDup_nil.
    - invc_NoDup.
      find_apply_hyp_hyp.
      apply NoDup_cons; auto.
      intro.
      match goal with H: ~ In _ _ |- _ => contradict H end.
      apply in_or_app.
      left; auto.
  Qed.

  Lemma NoDup_app_right :
    forall (l l' : list A),
      NoDup (l ++ l') -> NoDup l'.
  Proof.
    induction l; intros; simpl in *; auto.
    invc_NoDup.
    find_apply_hyp_hyp; auto.
  Qed.

  Lemma NoDup_in_not_in_right :
    forall (l l' : list A) (a : A),
      NoDup (l ++ l') -> In a l -> ~ In a l'.
  Proof.
    induction l; intros; simpl in *; auto.
    invc_NoDup.
    break_or_hyp; eauto with datatypes.
  Qed.

  Lemma NoDup_in_not_in_left :
    forall (l l' : list A) (a : A),
    NoDup (l ++ l') -> In a l' -> ~ In a l.
  Proof.
    intros.
    induction l; simpl in *; auto.
    invc_NoDup.
    concludes.
    intro.
    break_or_hyp; auto with datatypes.
  Qed.

  Lemma count_occ_app :
    forall l l' (a : A),
      count_occ A_eq_dec (l ++ l') a = count_occ A_eq_dec l a + count_occ A_eq_dec l' a.
  Proof.
    intros.
    induction l; simpl in *; auto.
    break_if; auto.
    find_rewrite.
    auto.
  Qed.

  Lemma Permutation_map_fst :
    forall l l' : list (A * B),
      Permutation l l' ->
      Permutation (map fst l) (map fst l').
  Proof.
    induction l; intros; simpl in *.
    - find_apply_lem_hyp Permutation_nil.
      find_rewrite.
      auto.
    - assert (In a l').
        apply Permutation_in with (l := a :: l); auto with datatypes.
      find_apply_lem_hyp in_split.
      break_exists.
      find_rewrite.
      find_apply_lem_hyp Permutation_cons_app_inv.
      find_apply_hyp_hyp.
      find_rewrite.
      rewrite map_app.
      simpl.
      apply Permutation_cons_app.
      rewrite <- map_app.
      auto.
     Qed.

  Lemma snd_eq_not_in_map :
    forall (l : list (A * B)) n m,
      (forall nm, In nm l -> snd nm = m) ->
      ~ In (n, m) l ->
      ~ In n (map fst l).
  Proof.
    intros.
    induction l; simpl in *; auto.
    intro.
    break_or_hyp.
    - match goal with H: ~ _ |- _ => contradict H end.
      left.
      destruct a.
      match goal with H: forall _ : A * B, _ |- _ => specialize (H (a, b)) end.
      simpl in *.
      intuition eauto; repeat find_rewrite; auto.
    - match goal with H: In _ _ |- _ => contradict H end.
      apply IHl; eauto.
  Qed.

  Lemma NoDup_map_snd_fst :
    forall nms : list (A * B),
      NoDup nms ->
      (forall nm nm', In nm nms -> In nm' nms -> snd nm = snd nm') ->
      NoDup (map fst nms).
  Proof.
    intros.
    induction nms; simpl in *.
    - apply NoDup_nil.
    - invc_NoDup.
      apply NoDup_cons.
      * assert (forall nm, In nm nms -> snd nm = snd a).
          intuition eauto.
        destruct a.
        apply snd_eq_not_in_map with (m := b); auto.
      * apply IHnms; auto.
  Qed.

  Lemma in_fold_left_by_cons_in :
    forall (l : list B) (g : B -> A) x acc,
      In x (fold_left (fun a b => g b :: a) l acc) ->
      In x acc \/ exists y, In y l /\ x = g y.
  Proof using A_eq_dec.
    intros until l.
    induction l.
    - auto.
    - simpl; intros.
      destruct (A_eq_dec x (g a)); subst.
      + right; exists a; tauto.
      + find_apply_lem_hyp IHl.
        break_or_hyp; [left|right].
        * find_apply_lem_hyp In_cons_neq; tauto.
        * break_exists_exists; tauto.
  Qed.

  Lemma fold_left_for_each_not_in :
    forall (f : A -> B -> A) (g : A -> B -> C),
      (forall a b b',
          b <> b' ->
          g (f a b') b = g a b) ->
      forall l a b,
        ~ In b l ->
        g (fold_left f l a) b = g a b.
  Proof.
    induction l as [| b' l']; simpl in *; auto.
    - intros. intuition.
      rewrite IHl'; auto.
  Qed.

  Lemma fold_left_for_each_in :
    forall (f : A -> B -> A) (g : A -> B -> C) (B_eq_dec : forall x y : B, {x = y} + {x <> y}),
      (forall a b b',
          b <> b' ->
          g (f a b') b = g a b) ->
      forall l a b,
        In b l ->
        exists a',
          g (fold_left f l a) b = g (f a' b) b.
  Proof.
    induction l as [|b' l']; simpl in *; intuition; subst.
    destruct (in_dec B_eq_dec b l'); intuition.
    find_eapply_lem_hyp fold_left_for_each_not_in; eauto.
  Qed.

  Lemma hd_error_tl_exists :
    forall (l : list A) x,
      hd_error l = Some x ->
      exists tl,
        l = x :: tl.
  Proof.
    intros.
    destruct l; simpl in *.
    - congruence.
    - eexists; solve_by_inversion.
  Qed.

  Lemma hd_error_None :
    forall (l : list A),
      hd_error l = None ->
      l = [].
  Proof.
    now destruct l.
  Qed.

End list_util.

(* We have to repeat these Hint Resolve commands because hints don't survive
   past the ends of sections *)
#[global] Hint Resolve app_cons_in : struct_util.
#[global] Hint Resolve app_cons_in_rest : struct_util.
#[global] Hint Resolve in_rest_app_cons : struct_util.
