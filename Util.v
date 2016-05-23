Require Import Arith.
Require Import Omega.
Require Import NPeano.
Require Import List.
Import ListNotations.
Require Import Sorting.Permutation.
Require Import StructTact.StructTactics.

Set Implicit Arguments.

Notation member := (in_dec eq_nat_dec).

Ltac do_in_map :=
  match goal with
    | [ H : In _ (map _ _) |- _ ] => apply in_map_iff in H; break_exists; break_and
  end.

Ltac do_in_app :=
  match goal with
    | [ H : In _ (_ ++ _) |- _ ] => apply in_app_iff in H
  end.

Create HintDb struct_util.

Lemma filter_app : forall A (f : A -> bool) xs ys,
    filter f (xs ++ ys) = filter f xs ++ filter f ys.
Proof.
  induction xs; intros.
  - auto.
  - simpl. rewrite IHxs. break_if; auto.
Qed.

Ltac invc_NoDup :=
  repeat match goal with
  | [ H : NoDup (_ :: _) |- _ ] => invc H
  end.

Hint Constructors NoDup : struct_util.

Section dedup.
  Variable A : Type.
  Hypothesis A_eq_dec : forall x y : A, {x = y} + {x <> y}.

  Fixpoint dedup (xs : list A) : list A :=
    match xs with
    | [] => []
    | x :: xs => let tail := dedup xs in
                 if in_dec A_eq_dec x xs then
                   tail
                 else
                   x :: tail
    end.

  Lemma dedup_eliminates_duplicates : forall (a : A) b c,
      (dedup (a :: b ++ a :: c) = dedup (b ++ a :: c)).
  Proof.
    intros. simpl in *.
    break_match.
    + auto.
    + exfalso. intuition.
  Qed.

  Lemma dedup_In : forall (x : A) xs,
      In x xs ->
      In x (dedup xs).
  Proof.
    induction xs; intros; simpl in *.
    - intuition.
    - break_if; intuition; subst; simpl; auto.
  Qed.

  Lemma filter_dedup (pred : A -> bool) :
    forall xs (p : A) ys,
      pred p = false ->
      filter pred (dedup (xs ++ ys)) = filter pred (dedup (xs ++ p :: ys)).
  Proof.
    intros.
    induction xs; simpl; repeat (break_match; simpl);
      auto using f_equal2; try discriminate.
      + exfalso. apply n. apply in_app_iff. apply in_app_or in i. intuition.
      + exfalso. apply n. apply in_app_or in i. intuition.
        * simpl in *. intuition. congruence.
  Qed.

  Lemma dedup_app : forall (xs ys : list A),
      (forall x y, In x xs -> In y ys -> x <> y) ->
      dedup (xs ++ ys) = dedup xs ++ dedup ys.
  Proof.
    intros. induction xs; simpl; auto.
    repeat break_match.
    - apply IHxs.
      intros. apply H; intuition.
    - exfalso. specialize (H a a).
      apply H; intuition.
      do_in_app. intuition.
    - exfalso. apply n. intuition.
    - simpl. f_equal.
      apply IHxs.
      intros. apply H; intuition.
  Qed.

  Lemma in_dedup_was_in :
    forall xs (x : A),
      In x (dedup xs) ->
      In x xs.
  Proof.
    induction xs; intros; simpl in *.
    - intuition.
    - break_if; simpl in *; intuition.
  Qed.

  Lemma NoDup_dedup :
    forall (xs : list A),
      NoDup (dedup xs).
  Proof.
    induction xs; simpl.
    - constructor.
    - break_if; auto.
      constructor; auto.
      intro.
      apply n.
      eapply in_dedup_was_in; eauto.
  Qed.

  Lemma remove_preserve :
    forall (x y : A) xs,
      x <> y ->
      In y xs ->
      In y (remove A_eq_dec x xs).
  Proof.
    induction xs; intros.
    - intuition.
    - simpl in *.
      concludes.
      intuition; break_if; subst; try congruence; intuition.
  Qed.

  Lemma in_remove :
    forall (x y : A) xs,
      In y (remove A_eq_dec x xs) ->
      In y xs.
  Proof.
    induction xs; intros.
    - auto.
    - simpl in *. break_if; simpl in *; intuition.
  Qed.

  Lemma remove_dedup_comm : forall (x : A) xs,
      remove A_eq_dec x (dedup xs) =
      dedup (remove A_eq_dec x xs).
  Proof.
    induction xs; intros.
    - auto.
    - simpl. repeat (break_match; simpl); auto using f_equal.
      + exfalso. apply n0. apply remove_preserve; auto.
      + exfalso. apply n. eapply in_remove; eauto.
  Qed.

  Lemma remove_partition :
    forall xs (p : A) ys,
      remove A_eq_dec p (xs ++ p :: ys) = remove A_eq_dec p (xs ++ ys).
  Proof.
    induction xs; intros; simpl; break_if; congruence.
  Qed.

  Lemma remove_not_in : forall (x : A) xs,
      ~ In x xs ->
      remove A_eq_dec x xs = xs.
  Proof.
    intros. induction xs; simpl in *; try break_if; intuition congruence.
  Qed.

  Lemma dedup_partition :
    forall xs (p : A) ys xs' ys',
      dedup (xs ++ p :: ys) = xs' ++ p :: ys' ->
      remove A_eq_dec p (dedup (xs ++ ys)) = xs' ++ ys'.
  Proof.
    intros xs p ys xs' ys' H.
    f_apply H (remove A_eq_dec p).
    rewrite remove_dedup_comm, remove_partition in *.
    find_rewrite.
    rewrite remove_partition.

    apply remove_not_in.
    apply NoDup_remove_2.
    rewrite <- H.
    apply NoDup_dedup.
  Qed.

  Lemma dedup_NoDup_id : forall (xs : list A),
      NoDup xs -> dedup xs = xs.
  Proof.
    induction xs; intros.
    - auto.
    - simpl. invc_NoDup. concludes.
      break_if; congruence.
  Qed.

  Lemma dedup_not_in_cons :
    forall x xs,
      (~ In x xs) ->
      x :: dedup xs = dedup (x :: xs).
  Proof.
    induction xs; intros.
    - auto.
    - simpl in *. intuition. repeat break_match; intuition.
  Qed.
End dedup.

Lemma filter_fun_ext_eq : forall A f g xs,
                            (forall a : A, In a xs -> f a = g a) ->
                            filter f xs = filter g xs.
Proof.
  induction xs; intros.
  - auto.
  - simpl. rewrite H by intuition. rewrite IHxs by intuition. auto.
Qed.



Lemma NoDup_map_injective : forall A B (f : A -> B) xs,
                              (forall x y, In x xs -> In y xs ->
                                           f x = f y -> x = y) ->
                              NoDup xs -> NoDup (map f xs).
Proof.
  induction xs; intros.
  - constructor.
  - simpl. invc_NoDup. constructor.
    + intro. do_in_map.
      assert (x = a) by intuition.
      congruence.
    + intuition.
Qed.

Lemma NoDup_disjoint_append :
  forall A (l : list A) l',
    NoDup l ->
    NoDup l' ->
    (forall a, In a l -> ~ In a l') ->
    NoDup (l ++ l').
Proof.
  induction l; intros.
  - auto.
  - simpl. invc_NoDup. constructor.
    + intro. do_in_app. intuition eauto with *.
    + intuition eauto with *.
Qed.

Lemma filter_NoDup :
  forall A p (l : list A),
    NoDup l ->
    NoDup (filter p l).
Proof.
  induction l; intros.
  - auto.
  - invc_NoDup. simpl. break_if; auto.
    constructor; auto.
    intro. apply filter_In in H. intuition.
Qed.


Lemma NoDup_map_filter :
  forall A B (f : A -> B) g l,
    NoDup (map f l) ->
    NoDup (map f (filter g l)).
Proof.
  intros. induction l; simpl in *.
  - constructor.
  - invc_NoDup. concludes.
    break_if; simpl in *; auto.
    constructor; auto.
    intro. do_in_map.
    find_apply_lem_hyp filter_In. intuition.
    match goal with | H : _ -> False |- False => apply H end.
    apply in_map_iff. eauto.
Qed.


Lemma filter_true_id : forall A (f : A -> bool) xs,
                         (forall x, In x xs -> f x = true) ->
                         filter f xs = xs.
Proof.
  induction xs; intros.
  - auto.
  - simpl. now rewrite H, IHxs by intuition.
Qed.

Lemma map_of_map : forall A B C (f : A -> B) (g : B -> C) xs,
                     map g (map f xs) = map (fun x => g (f x)) xs.
Proof.
  induction xs; simpl; auto using f_equal2.
Qed.

Lemma filter_except_one : forall A A_eq_dec (f g : A -> bool) x xs,
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
    + subst. repeat find_rewrite. eauto with *.
    + simpl. rewrite H by auto with *.
      break_if; eauto using f_equal2 with *.
Qed.

Lemma flat_map_nil : forall A B (f : A -> list B) l,
                       flat_map f l = [] ->
                       l = [] \/ (forall x, In x l -> f x = []).
Proof.
  induction l; intros.
  - intuition.
  - right. simpl in *.
    apply app_eq_nil in H.
    intuition; subst; simpl in *; intuition.
Qed.

Fixpoint remove_first {A : Set} (A_eq_dec : forall x y : A, {x = y} + {x <> y}) (x : A) (l : list A) : list A :=
  match l with
    | [] => []
    | y::tl => if (A_eq_dec x y) then tl else y::(remove_first A_eq_dec x tl)
  end.


Fixpoint subseq {A} (xs ys : list A) : Prop :=
  match xs, ys with
    | [], _ => True
    | x :: xs', y :: ys' => (x = y /\ subseq xs' ys') \/ subseq xs ys'
    | _, _ => False
  end.

Lemma subseq_refl : forall A (l : list A), subseq l l.
Proof.
  induction l; simpl; tauto.
Qed.

Lemma subseq_trans :
  forall A (zs xs ys : list A),
    subseq xs ys ->
    subseq ys zs ->
    subseq xs zs.
Proof.
  induction zs; intros; simpl in *;
  repeat break_match; subst; simpl in *; intuition; subst; eauto;
  right; (eapply IHzs; [|eauto]); simpl; eauto.
Qed.

Lemma subseq_In :
  forall A (ys xs : list A) x,
    subseq xs ys ->
    In x xs ->
    In x ys.
Proof.
  induction ys; intros.
  - destruct xs; simpl in *; intuition.
  - simpl in *. break_match; simpl in *; intuition; subst; intuition eauto;
                right; (eapply IHys; [eauto| intuition]).
Qed.

Theorem subseq_NoDup :
  forall A (ys xs : list A),
    subseq xs ys ->
    NoDup ys ->
    NoDup xs.
Proof.
  induction ys; intros.
  - destruct xs; simpl in *; intuition.
  - simpl in *. invc_NoDup.
    break_match.
    + constructor.
    + intuition.
      subst. constructor; eauto using subseq_In.
Qed.

Lemma subseq_remove :
  forall A A_eq_dec (x : A) xs,
    subseq (remove A_eq_dec x xs) xs.
Proof.
  induction xs; intros; simpl.
  - auto.
  - repeat break_match; auto.
    + intuition congruence.
    + find_inversion. auto.
Qed.

Theorem NoDup_Permutation_NoDup :
  forall A (l l' : list A),
    NoDup l ->
    Permutation l l' ->
    NoDup l'.
Proof.
  intros A l l' Hnd Hp.
  induction Hp; auto; invc_NoDup; constructor;
    eauto using Permutation_in, Permutation_sym;
    simpl in *; intuition.
Qed.

Theorem NoDup_append :
  forall A l (a : A),
    NoDup (l ++ [a]) <-> NoDup (a :: l).
Proof.
  intuition eauto using NoDup_Permutation_NoDup, Permutation_sym, Permutation_cons_append.
Qed.

Lemma leb_false_lt : forall m n, leb m n = false -> n < m.
Proof.
  induction m; intros.
  - discriminate.
  - simpl in *. break_match; subst; auto with arith.
Qed.

Lemma leb_true_le : forall m n, leb m n = true -> m <= n.
Proof.
  induction m; intros.
  - auto with arith.
  - simpl in *. break_match; subst; auto with arith.
    discriminate.
Qed.

Lemma ltb_false_le : forall m n, m <? n = false -> n <= m.
Proof.
  induction m; intros; destruct n; try discriminate; auto with arith.
Qed.

Lemma ltb_true_lt : forall m n, m <? n = true -> m < n.
  induction m; intros; destruct n; try discriminate; auto with arith.
Qed.

Ltac do_bool :=
  repeat match goal with
    | [ H : beq_nat _ _ = true |- _ ] => apply beq_nat_true in H
    | [ H : beq_nat _ _ = false |- _ ] => apply beq_nat_false in H
    | [ H : andb _ _ = true |- _ ] => apply Bool.andb_true_iff in H
    | [ H : andb _ _ = false |- _ ] => apply Bool.andb_false_iff in H
    | [ H : orb _ _ = true |- _ ] => apply Bool.orb_prop in H
    | [ H : negb _ = true |- _ ] => apply Bool.negb_true_iff in H
    | [ H : negb _ = false |- _ ] => apply Bool.negb_false_iff in H
    | [ H : PeanoNat.Nat.ltb _ _ = true |- _ ] => apply ltb_true_lt in H
    | [ H : PeanoNat.Nat.ltb _ _ = false |- _ ] => apply ltb_false_le in H
    | [ H : leb _ _ = true |- _ ] => apply leb_true_le in H
    | [ H : leb _ _ = false |- _ ] => apply leb_false_lt in H
    | [ |- context [ andb _ _ ] ] => apply Bool.andb_true_iff
    | [ |- context [ andb _ _ ] ] => apply Bool.andb_false_iff
    | [ |- context [ leb _ _ ] ] => apply leb_correct
    | [ |- context [ _ <> false ] ] => apply Bool.not_false_iff_true
    | [ |- beq_nat _ _ = false ] => apply beq_nat_false_iff
    | [ |- beq_nat _ _ = true ] => apply beq_nat_true_iff
  end.


Lemma NoDup_map_elim :
  forall A B (f : A -> B) xs x y,
    f x = f y ->
    NoDup (map f xs) ->
    In x xs ->
    In y xs ->
    x = y.
Proof.
  induction xs; intros; simpl in *.
  - intuition.
  - invc_NoDup. intuition; subst; auto; exfalso.
    + repeat find_rewrite. auto using in_map.
    + repeat find_reverse_rewrite. auto using in_map.
Qed.

Lemma subseq_map :
  forall A B (f : A -> B) ys xs,
    subseq xs ys ->
    subseq (map f xs) (map f ys).
Proof.
  induction ys; intros; simpl in *.
  - repeat break_match; try discriminate; auto.
  - repeat break_match; try discriminate; auto.
    intuition.
    + subst. simpl in *. find_inversion. auto.
    + right. repeat find_reverse_rewrite. auto.
Qed.

Lemma subseq_cons_drop :
  forall A xs ys (a : A),
    subseq (a :: xs) ys -> subseq xs ys.
Proof.
  induction ys; intros; simpl in *; intuition; break_match; eauto.
Qed.

Lemma subseq_length :
  forall A (ys xs : list A),
    subseq xs ys ->
    length xs <= length ys.
Proof.
  induction ys; intros; simpl in *; break_match; intuition.
  subst. simpl in *. specialize (IHys l). concludes. auto with *.
Qed.

Lemma subseq_subseq_eq :
  forall A (xs ys : list A),
    subseq xs ys ->
    subseq ys xs ->
    xs = ys.
Proof.
  induction xs; intros; destruct ys; simpl in *;
    intuition eauto using f_equal2, subseq_cons_drop.
  exfalso.
  repeat find_apply_lem_hyp subseq_length.
  simpl in *. omega.
Qed.

Lemma subseq_filter :
  forall A (f : A -> bool) xs,
    subseq (filter f xs) xs.
Proof.
  induction xs; intros; simpl.
  - auto.
  - repeat break_match; intuition congruence.
Qed.

Fixpoint take A (n : nat) (xs : list A) : list A :=
  match n with
    | O => []
    | S n' => match xs with
               | [] => []
               | x :: xs' => x :: take n' xs'
             end
  end.

Lemma remove_length_not_in : forall A A_eq_dec (x : A) xs,
                               ~ In x xs ->
                               length (remove A_eq_dec x xs) = length xs.
Proof.
  induction xs; intros.
  - auto.
  - simpl in *. intuition.
    break_if; subst; simpl; intuition.
Qed.

Lemma remove_length_in : forall A A_eq_dec (x : A) xs,
                           In x xs ->
                           NoDup xs ->
                           S (length (remove A_eq_dec x xs)) = length xs.
Proof.
  induction xs; intros; simpl in *; intuition; invc_NoDup;
    break_if; subst; intuition (simpl; try congruence).
  now rewrite remove_length_not_in.
Qed.


Lemma subset_size_eq :
  forall A xs,
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
    assert (In a ys) by eauto with *.

    find_apply_lem_hyp in_split.
    break_exists_name l1.
    break_exists_name l2.
    subst.

    specialize (IHxs (l1 ++ l2)).

    conclude_using ltac:(eauto using NoDup_remove_1).

    forward IHxs.
    intros x' Hx'.
    assert (In x' (l1 ++ a :: l2)) by eauto with *.
    do_in_app. simpl in *. intuition. subst. congruence.
    concludes.

    forward IHxs.
    rewrite app_length in *. simpl in *. omega.
    concludes.

    do_in_app. simpl in *. intuition.
Qed.

Lemma in_take : forall A n (x : A) xs,
                  In x (take n xs) -> In x xs.
Proof.
  induction n; simpl; intuition; break_match; simpl in *; intuition.
Qed.

Lemma take_NoDup : forall A n (xs : list A),
                     NoDup xs ->
                     NoDup (take n xs).
Proof.
  induction n; intros; simpl; destruct xs; auto with struct_util.
  invc_NoDup.
  eauto 6 using in_take with struct_util.
Qed.

Lemma remove_NoDup :
  forall A A_eq_dec (x : A) xs,
    NoDup xs ->
    NoDup (remove A_eq_dec x xs).
Proof.
  induction xs; intros.
  - auto with struct_util.
  - invc_NoDup. simpl. break_if; eauto 6 using in_remove with struct_util.
Qed.

Lemma seq_range :
  forall n a x,
    In x (seq a n) ->
    a <= x < a + n.
Proof.
  induction n; intros; simpl in *.
  - intuition.
  - break_or_hyp; try find_apply_hyp_hyp; intuition.
Qed.


Lemma take_length : forall A n (xs : list A),
                      length xs >= n ->
                      length (take n xs) = n.
Proof.
  induction n; intros.
  - auto.
  - simpl. break_match; simpl in *.
    + omega.
    + now rewrite IHn by omega.
Qed.


Lemma seq_NoDup : forall n a ,
                    NoDup (seq a n).
Proof.
  induction n; intros; simpl in *; constructor; auto.
  intro. apply seq_range in H. omega.
Qed.

Lemma remove_length_ge : forall A A_eq_dec (x : A) xs,
                           NoDup xs ->
                           length (remove A_eq_dec x xs) >= length xs - 1.
Proof.
  induction xs; intros.
  - auto.
  - invc_NoDup. simpl. break_if.
    + rewrite <- minus_n_O.
      subst.
      rewrite remove_length_not_in; auto.
    + simpl. concludes. omega.
Qed.

Lemma remove_length_le :
  forall A (x : A) xs eq_dec,
    length xs >= length (remove eq_dec x xs).
Proof.
  induction xs; intros.
  - auto.
  - simpl in *.
    specialize (IHxs eq_dec).
    break_if; subst; simpl; omega.
Qed.

Lemma remove_length_lt :
  forall A (x : A) xs eq_dec,
    In x xs ->
    length xs > length (remove eq_dec x xs).
Proof.
  induction xs; intros; simpl in *; intuition.
  - subst.
    break_if; try congruence.
    pose proof remove_length_le x xs eq_dec.
    omega.
  - specialize (IHxs ltac:(eauto) ltac:(eauto)).
    break_if; subst; simpl; omega.
Qed.

Lemma subset_length :
  forall A xs ys,
    (forall a b : A, {a = b} + {a <> b}) ->
    NoDup xs ->
    (forall x : A, In x xs -> In x ys) ->
    length ys >= length xs.
Proof.
  induction xs; intros.
  - simpl. omega.
  - specialize (IHxs (remove X a ys) X).
    invc_NoDup.
    concludes.

    forward IHxs.
    intros.
    apply remove_preserve; [congruence|intuition].
    concludes.

    pose proof remove_length_lt a ys X.
    conclude_using intuition.

    simpl. omega.
Qed.

Lemma take_length_ge : forall A n m (xs : list A),
                         length (take n xs) >= m ->
                         length xs >= m.
Proof.
  induction n; intros; simpl in *.
  - omega.
  - break_match.
    + omega.
    + simpl in *.
      destruct m; try omega.
      unfold ge in *.
      auto with arith.
Qed.


Lemma or_false :
  forall P : Prop, P -> (P \/ False).
Proof.
  firstorder.
Qed.

Ltac map_crush :=
  repeat match goal with
                   | [ H : context [ map _ (_ ++ _) ] |- _ ] => rewrite map_app in H
                   | [ |- context [ map _ (_ ++ _) ] ] => rewrite map_app
                   | [ H : context [ map _ (map _ _) ] |- _ ] => rewrite map_map in H
                   | [ |- context [ map _ (map _ _) ] ] => rewrite map_map
         end; simpl in *.


Ltac in_crush_finish :=
  repeat match goal with
    | [ |- _ \/ _ ] => try first [solve [apply or_introl; in_crush_finish]|
                                 solve [apply or_intror; in_crush_finish]]
    | [ |- In _ (_ ++ _) ] => apply in_or_app; in_crush_finish
    | [ |- In _ (map _ _) ] => apply in_map_iff; eexists; eauto
  end.
Ltac in_crush_start :=
  intuition; simpl in *;
  repeat
    (match goal with
       | [ H : In _ (map _ _) |- _ ] => apply in_map_iff in H; break_exists; break_and
       | [ H : In _ (_ ++ _) |- _ ] => apply in_app_iff in H
     end; intuition; simpl in *); subst.

Ltac in_crush := repeat (in_crush_start; in_crush_finish).

Fixpoint Prefix {A} (l1 : list A) l2 : Prop :=
  match l1, l2 with
    | a :: l1', b :: l2' => a = b /\ Prefix l1' l2'
    | [], _ => True
    | _, _ => False
  end.

Lemma Prefix_nil :
  forall A (l : list A),
    Prefix l [] ->
    l = [].
Proof.
  intros. destruct l.
  - reflexivity.
  - contradiction.
Qed.

Lemma Prefix_cons :
  forall A (l l' : list A) a,
    Prefix l' l ->
    Prefix (a :: l') (a :: l).
Proof.
  simpl. intuition.
Qed.

Lemma Prefix_in :
  forall A (l l' : list A),
    Prefix l' l ->
    (forall x, In x l' -> In x l).
Proof.
  induction l; intros l' H.
  - find_apply_lem_hyp Prefix_nil. subst. contradiction.
  - destruct l'.
    + contradiction.
    + intros. simpl Prefix in *. break_and. subst. simpl in *. intuition.
      right. eapply IHl; eauto.
Qed.

Lemma app_Prefix :
  forall A (xs ys zs : list A),
    xs ++ ys = zs ->
    Prefix xs zs.
Proof.
  induction xs; intros; simpl in *.
  - auto.
  - break_match.
    + discriminate.
    + subst. find_inversion. eauto.
Qed.

Lemma Prefix_In :
  forall A (l : list A) l' x,
    Prefix l l' ->
    In x l ->
    In x l'.
Proof.
  induction l; intros; simpl in *; intuition;
  subst; break_match; intuition; subst; intuition.
Qed.


Fixpoint filterMap {A B} (f : A -> option B) (l : list A) : list B :=
  match l with
    | [] => []
    | x :: xs => match f x with
                   | None => filterMap f xs
                   | Some y => y :: filterMap f xs
                 end
  end.

Lemma app_cons_singleton_inv :
  forall A xs (y : A) zs w,
    xs ++ y :: zs = [w] ->
    xs = [] /\ y = w /\ zs = [].
Proof.
  intros.
  destruct xs.
  - solve_by_inversion.
  - destruct xs; solve_by_inversion.
Qed.

Definition null {A : Type} (xs : list A) : bool :=
  match xs with
    | [] => true
    | _ => false
  end.

Lemma null_sound :
  forall A (l : list A),
    null l = true -> l = [].
Proof.
  destruct l; simpl in *; auto; discriminate.
Qed.

Lemma null_false_neq_nil :
  forall A (l : list A),
    null l = false -> l <> [].
Proof.
  destruct l; simpl in *; auto; discriminate.
Qed.

Lemma map_of_filterMap :
  forall A B C (f : A -> option B) (g : B -> C) l,
    map g (filterMap f l) = filterMap (fun x => match f x with
                                                  | Some y => Some (g y)
                                                  | None => None
                                                end) l.
Proof.
  induction l; intros; simpl in *.
  - auto.
  - repeat break_match; simpl; auto using f_equal.
Qed.

Lemma filterMap_ext :
  forall A B (f g : A -> option B) l,
    (forall x, f x = g x) ->
    filterMap f l = filterMap g l.
Proof.
  induction l; intros; simpl in *.
  - auto.
  - repeat find_higher_order_rewrite; auto.
Qed.

Lemma filterMap_defn :
  forall A B (f : A -> option B) x xs,
    filterMap f (x :: xs) = match f x with
                              | Some y => y :: filterMap f xs
                              | None => filterMap f xs
                            end.
Proof.
  simpl. auto.
Qed.

Lemma In_filterMap :
  forall A B (f : A -> option B) b xs,
    In b (filterMap f xs) ->
    exists a,
      In a xs /\ f a = Some b.
Proof.
  intros.
  induction xs; simpl in *; intuition.
  break_match.
  - simpl in *. intuition; subst; eauto.
    break_exists_exists; intuition.
  - concludes. break_exists_exists; intuition.
Qed.

Lemma app_cons_in :
  forall A (l : list A) xs a ys,
    l = xs ++ a :: ys ->
    In a l.
Proof.
  intros. subst. auto with *.
Qed.
Hint Resolve app_cons_in : struct_util.

Lemma app_cons_in_rest:
  forall A (l : list A) xs a b ys,
    l = xs ++ a :: ys ->
    In b (xs ++ ys) ->
    In b l.
Proof.
  intros. subst. in_crush.
Qed.
Hint Resolve app_cons_in_rest : struct_util.

Lemma remove_filter_commute :
  forall A  (l : list A) A_eq_dec f x,
    remove A_eq_dec x (filter f l) = filter f (remove A_eq_dec x l).
Proof.
  induction l; intros; simpl in *; auto.
  repeat (break_if; subst; simpl in *; try congruence).
Qed.

Lemma In_filter_In :
  forall A (f : A -> bool) x l l',
    filter f l = l' ->
    In x l' -> In x l.
Proof.
  intros. subst.
  eapply filter_In; eauto.
Qed.

Lemma filter_partition :
  forall A (l1 : list A) f l2 x l1' l2',
    NoDup (l1 ++ x :: l2) ->
    filter f (l1 ++ x :: l2) = (l1' ++ x :: l2') ->
    filter f l1 = l1' /\ filter f l2 = l2'.
Proof.
  induction l1; intros; simpl in *; break_if; simpl in *; invc_NoDup.
  - destruct l1'; simpl in *.
    + solve_by_inversion.
    + find_inversion. exfalso. eauto using In_filter_In with *.
  - exfalso. eauto using In_filter_In with *.
  - destruct l1'; simpl in *; break_and; find_inversion.
    + exfalso. eauto with *.
    + find_apply_hyp_hyp. intuition auto using f_equal2.
  - eauto.
Qed.

Lemma map_inverses :
  forall A B (la : list A) (lb : list B)  (f : A -> B) g,
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

Lemma if_sum_bool_fun_comm :
  forall A B C D (b : {A}+{B}) (c1 c2 : C) (f : C -> D),
    f (if b then c1 else c2) = if b then f c1 else f c2.
Proof.
  intros. break_if; auto.
Qed.

Section assoc.
  Variable K V : Type.
  Variable K_eq_dec : forall k k' : K, {k = k'} + {k <> k'}.

  Fixpoint assoc (l : list (K * V)) (k : K) : option V :=
    match l with
      | [] => None
      | (k', v) :: l' =>
        if K_eq_dec k k' then
          Some v
        else
          assoc l' k
    end.

  Definition assoc_default (l : list (K * V)) (k : K) (default : V) : V :=
    match (assoc l k) with
      | Some x => x
      | None => default
    end.

  Fixpoint assoc_set (l : list (K * V)) (k : K) (v : V) : list (K * V) :=
    match l with
      | [] => [(k, v)]
      | (k', v') :: l' =>
        if K_eq_dec k k' then
          (k, v) :: l'
        else
          (k', v') :: (assoc_set l' k v)
    end.

  Fixpoint assoc_del (l : list (K * V)) (k : K) : list (K * V) :=
    match l with
      | [] => []
      | (k', v') :: l' =>
        if K_eq_dec k k' then
          assoc_del l' k
        else
          (k', v') :: (assoc_del l' k)
    end.

  Lemma get_set_same :
    forall k v l,
      assoc (assoc_set l k v) k = Some v.
  Proof.
    induction l; intros; simpl; repeat (break_match; simpl); subst; congruence.
  Qed.

  Lemma get_set_same' :
    forall k k' v l,
      k = k' ->
      assoc (assoc_set l k v) k' = Some v.
  Proof.
    intros. subst. auto using get_set_same.
  Qed.

  Lemma get_set_diff :
    forall k k' v l,
      k <> k' ->
      assoc (assoc_set l k v) k' = assoc l k'.
  Proof.
    induction l; intros; simpl; repeat (break_match; simpl); subst; try congruence; auto.
  Qed.

  Lemma not_in_assoc :
    forall k l,
      ~ In k (map (@fst _ _) l) ->
      assoc l k = None.
  Proof.
    intros.
    induction l.
    - auto.
    - simpl in *. repeat break_match; intuition.
      subst. simpl in *. congruence.
  Qed.

  Lemma get_del_same :
    forall k l,
      assoc (assoc_del l k) k = None.
  Proof.
    induction l; intros; simpl in *.
    - auto.
    - repeat break_match; subst; simpl in *; auto.
      break_if; try congruence.
  Qed.

  Lemma get_del_diff :
    forall k k' l,
      k <> k' ->
      assoc (assoc_del l k') k = assoc l k.
  Proof.
    induction l; intros; simpl in *.
    - auto.
    - repeat (break_match; simpl); subst; try congruence; auto.
  Qed.

  Lemma get_set_diff_default :
    forall (k k' : K) (v : V) l d,
      k <> k' ->
      assoc_default (assoc_set l k v) k' d = assoc_default l k' d.
  Proof.
    unfold assoc_default.
    intros.
    repeat break_match; auto;
    rewrite get_set_diff in * by auto; congruence.
  Qed.

  Lemma get_set_same_default :
    forall (k : K) (v : V) l d,
      assoc_default (assoc_set l k v) k d = v.
  Proof.
    unfold assoc_default.
    intros.
    repeat break_match; auto;
    rewrite get_set_same in *; congruence.
  Qed.
End assoc.

Fixpoint before {A: Type} (x : A) y l : Prop :=
  match l with
    | [] => False
    | a :: l' =>
      a = x \/
      (a <> y /\ before x y l')
  end.

Lemma before_In :
  forall A x y l,
    before (A:=A) x y l ->
    In x l.
Proof.
  induction l; intros; simpl in *; intuition.
Qed.


Lemma before_split :
  forall A l (x y : A),
    before x y l ->
    x <> y ->
    In x l ->
    In y l ->
    exists xs ys zs,
      l = xs ++ x :: ys ++ y :: zs.
Proof.
  induction l; intros; simpl in *; intuition; subst; try congruence.
  - exists nil. simpl. find_apply_lem_hyp in_split. break_exists. subst. eauto.
  - exists nil. simpl. find_apply_lem_hyp in_split. break_exists. subst. eauto.
  - exists nil. simpl. find_apply_lem_hyp in_split. break_exists. subst. eauto.
  - eapply_prop_hyp In In; eauto. break_exists. subst.
    exists (a :: x0), x1, x2. auto.
Qed.

Lemma In_app_before :
  forall A xs ys x y,
    In(A:=A) x xs ->
    (~ In y xs) ->
    before x y (xs ++ y :: ys).
Proof.
  induction xs; intros; simpl in *; intuition.
Qed.

Fixpoint before_func {A: Type} (f : A -> bool) (g : A -> bool) (l : list A) : Prop :=
  match l with
    | [] => False
    | a :: l' =>
      f a = true \/
      (g a = false /\ before_func f g l')
  end.

Definition before_func_dec :
  forall A f g (l : list A),
    {before_func f g l} + {~ before_func f g l}.
Proof.
  intros. induction l; simpl in *.
  - intuition.
  - destruct (f a); destruct (g a); intuition.
Qed.

Lemma before_func_app :
  forall A f g l x,
    before_func (A := A) f g l ->
    before_func f g (l ++ x).
Proof.
  intros. induction l; simpl in *; intuition.
Qed.


Lemma if_decider_true :
  forall A B (P : A -> Prop) (dec : forall x, {P x} + {~ P x}) a (b1 b2 : B),
    P a ->
    (if dec a then b1 else b2) = b1.
Proof.
  intros.
  break_if; congruence.
Qed.

Lemma if_decider_false :
  forall A B (P : A -> Prop) (dec : forall x, {P x} + {~ P x}) a (b1 b2 : B),
    ~ P a ->
    (if dec a then b1 else b2) = b2.
Proof.
  intros.
  break_if; congruence.
Qed.

Lemma filterMap_app :
  forall A B (f : A -> option B) xs ys,
    filterMap f (xs ++ ys) = filterMap f xs ++ filterMap f ys.
Proof.
  induction xs; intros; simpl in *; repeat break_match; simpl in *; intuition auto using f_equal.
Qed.

Lemma filterMap_In :
  forall A B (f : A -> option B) a b xs,
    f a = Some b ->
    In a xs ->
    In b (filterMap f xs).
Proof.
  induction xs; simpl; repeat break_match; simpl; intuition (auto; try congruence).
Qed.

Lemma In_notIn_implies_neq :
  forall A x y l,
    In(A:=A) x l ->
    ~ In(A:=A) y l ->
    x <> y.
Proof.
  intuition congruence.
Qed.

Lemma In_cons_neq :
  forall A a x xs,
    In(A:=A) a (x :: xs) ->
    a <> x ->
    In a xs.
Proof.
  simpl.
  intuition congruence.
Qed.

Lemma NoDup_app3_not_in_1 :
  forall A (xs ys zs : list A) b,
    NoDup (xs ++ ys ++ b :: zs) ->
    In b xs ->
    False.
Proof.
  intros.
  rewrite <- app_ass in *.
  find_apply_lem_hyp NoDup_remove.
  rewrite app_ass in *.
  intuition.
Qed.

Lemma NoDup_app3_not_in_2 :
  forall A (xs ys zs : list A) b,
    NoDup (xs ++ ys ++ b :: zs) ->
    In b ys ->
    False.
Proof.
  intros.
  rewrite <- app_ass in *.
  find_apply_lem_hyp NoDup_remove_2.
  rewrite app_ass in *.
  auto 10 with *.
Qed.

Lemma NoDup_app3_not_in_3 :
  forall A (xs ys zs : list A) b,
    NoDup (xs ++ ys ++ b :: zs) ->
    In b zs ->
    False.
Proof.
  intros.
  rewrite <- app_ass in *.
  find_apply_lem_hyp NoDup_remove_2.
  rewrite app_ass in *.
  auto 10 with *.
Qed.

Lemma In_cons_2_3 :
  forall A xs ys zs x y a,
    In (A:=A) a (xs ++ ys ++ zs) ->
    In a (xs ++ x :: ys ++ y :: zs).
Proof.
  intros.
  repeat (do_in_app; intuition auto 10 with *).
Qed.

Lemma In_cons_2_3_neq :
  forall A a x y xs ys zs,
    In (A:=A) a (xs ++ x :: ys ++ y :: zs) ->
    a <> x ->
    a <> y ->
    In a (xs ++ ys ++ zs).
Proof.
  intros.
  repeat (do_in_app; simpl in *; intuition (auto with *; try congruence)).
Qed.

Lemma in_middle_reduce :
  forall A a xs y zs,
    In (A:=A) a (xs ++ y :: zs) ->
    a <> y ->
    In a (xs ++ zs).
Proof.
  intros.
  do_in_app; simpl in *; intuition. congruence.
Qed.

Lemma before_2_3_insert :
  forall A xs ys zs x y a b,
    before(A:=A) a b (xs ++ ys ++ zs) ->
    b <> x ->
    b <> y ->
    before a b (xs ++ x :: ys ++ y :: zs).
Proof.
  induction xs; intros; simpl in *; intuition.
  induction ys; intros; simpl in *; intuition.
Qed.

Lemma before_middle_insert :
  forall A xs y zs a b,
    before(A:=A) a b (xs ++ zs) ->
    b <> y ->
    before a b (xs ++ y :: zs).
Proof.
  intros.
  induction xs; intros; simpl in *; intuition.
Qed.

Lemma in_middle_insert :
  forall A a xs y zs,
    In (A:=A) a (xs ++ zs) ->
    In a (xs ++ y :: zs).
Proof.
  intros.
  do_in_app; simpl in *; intuition.
Qed.

Lemma before_2_3_reduce :
  forall A xs ys zs x y a b,
    before(A:=A) a b (xs ++ x :: ys ++ y :: zs) ->
    a <> x ->
    a <> y ->
    before a b (xs ++ ys ++ zs).
Proof.
  induction xs; intros; simpl in *; intuition; try congruence; eauto.
  induction ys; intros; simpl in *; intuition; try congruence.
Qed.

Lemma before_middle_reduce :
  forall A xs zs a b y,
    before(A:=A) a b (xs ++ y :: zs) ->
    a <> y ->
    before a b (xs ++ zs).
Proof.
  induction xs; intros; simpl in *; intuition; try congruence; eauto.
Qed.

Lemma subseq_nil :
  forall A xs,
    subseq (A:=A) [] xs.
Proof.
  destruct xs; simpl; auto.
Qed.

Lemma subseq_skip :
  forall A a xs ys,
    subseq(A:=A) xs ys ->
    subseq xs (a :: ys).
Proof.
  induction ys; intros; simpl in *; repeat break_match; intuition.
Qed.

Lemma subseq_filterMap :
  forall A B (f : A -> option B) ys xs,
    subseq xs ys ->
    subseq (filterMap f xs) (filterMap f ys).
Proof.
  induction ys; intros; simpl in *; repeat break_match; auto; try discriminate; intuition; subst.
  - simpl. find_rewrite. auto.
  - auto using subseq_skip.
  - auto using subseq_nil.
  - simpl. find_rewrite. auto.
Qed.

Lemma subseq_app_r :
  forall A xs ys,
    subseq (A:=A) ys (xs ++ ys).
Proof.
  induction xs; intros; simpl.
  + auto using subseq_refl.
  + break_match.
    * auto.
    * right. auto using subseq_nil.
Qed.

Lemma subseq_app_tail :
  forall A ys xs zs,
    subseq (A:=A) xs ys ->
    subseq (xs ++ zs) (ys ++ zs).
Proof.
  induction ys; intros; simpl in *.
  - break_match; intuition auto using subseq_refl.
  - repeat break_match.
    + auto.
    + discriminate.
    + simpl in *. subst. right. auto using subseq_app_r.
    + simpl in *. find_inversion. intuition.
      rewrite app_comm_cons. auto.
Qed.

Lemma subseq_app_head :
  forall A xs ys zs,
    subseq (A:=A) ys zs ->
    subseq (A:=A) (xs ++ ys) (xs ++ zs).
Proof.
  induction xs; intros; simpl; intuition.
Qed.

Lemma subseq_2_3 :
  forall A xs ys zs x y,
    subseq(A:=A) (xs ++ ys ++ zs) (xs ++ x :: ys ++ y :: zs).
Proof.
  auto using subseq_refl, subseq_skip, subseq_app_head.
Qed.

Lemma subseq_middle :
  forall A xs y zs,
    subseq (A:=A) (xs ++ zs) (xs ++ y :: zs).
Proof.
  intros.
  apply subseq_app_head.
  apply subseq_skip.
  apply subseq_refl.
Qed.

Lemma filterMap_of_filterMap :
  forall A B C (f : B -> option C) (g : A -> option B) xs,
    filterMap f (filterMap g xs) =
    filterMap (fun a => match g a with
                          | Some b => f b
                          | None => None
                        end) xs.
Proof.
  induction xs; simpl; intuition.
  repeat break_match; simpl; repeat find_rewrite; auto.
Qed.

Lemma filterMap_all_None :
  forall A B (f : A -> option B) xs,
    (forall x, In x xs -> f x = None) ->
    filterMap f xs = [].
Proof.
  induction xs; intros; simpl in *; intuition.
  rewrite H; auto.
Qed.

Lemma NoDup_rev :
  forall A l,
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
  forall A B C (f : A -> B) (g : A -> C) xs,
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

Lemma plus_gt_0 :
  forall a b,
    a + b > 0 ->
    a > 0 \/ b > 0.
Proof.
  intros.
  destruct (eq_nat_dec a 0); intuition.
Qed.

Lemma pigeon :
  forall A (A_eq_dec : forall a a': A, {a = a'} + {a <> a'}) (l : list A) sub1 sub2,
    (forall a, In a sub1 -> In a l) ->
    (forall a, In a sub2 -> In a l) ->
    NoDup l ->
    NoDup sub1 ->
    NoDup sub2 ->
    length sub1 + length sub2 > length l ->
    exists a, In a sub1 /\ In a sub2.
Proof.
  induction l.
  intros.
  + simpl in *. find_apply_lem_hyp plus_gt_0. intuition.
    * destruct sub1; simpl in *; [omega|].
      specialize (H a). intuition.
    * destruct sub2; simpl in *; [omega|].
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
             end; omega.
Qed.

Section remove_all.
  Variable (A : Type).
  Hypothesis (A_eq_dec : forall x y : A, {x = y} + {x <> y}).

  Fixpoint remove_all (to_delete l : list A) : list A :=
    match to_delete with
      | [] => l
      | d :: ds => remove_all ds (remove A_eq_dec d l)
    end.

  Lemma in_remove_all_was_in :
    forall ds l x,
      In x (remove_all ds l) ->
      In x l.
  Proof.
    induction ds; intros; simpl in *; intuition.
    eauto using in_remove.
  Qed.

  Lemma in_remove_all_preserve :
    forall ds l x,
      ~ In x ds ->
      In x l ->
      In x (remove_all ds l).
  Proof.
    induction ds; intros; simpl in *; intuition auto using remove_preserve.
  Qed.
End remove_all.
Arguments in_remove_all_was_in : clear implicits.

Lemma filterMap_NoDup_inj :
  forall A B (f : A -> option B) l,
    (forall x1 x2 y,
       f x1 = Some y ->
       f x2 = Some y ->
       x1 = x2) ->
    NoDup l ->
    NoDup (filterMap f l).
Proof.
  induction l; intros.
  - constructor.
  - simpl. invc_NoDup.
    break_match; auto.
    constructor; auto.
    intro.
    find_apply_lem_hyp In_filterMap. break_exists. break_and.
    assert (a = x) by eauto.
    subst. contradiction.
Qed.

Lemma subseq_remove_all :
  forall A A_eq_dec (ds l l' : list A),
    subseq l l' ->
    subseq (remove_all A_eq_dec ds l) l'.
Proof.
  induction ds; intros; simpl.
  - auto.
  - apply IHds.
    eapply subseq_trans.
    apply subseq_remove.
    auto.
Qed.

Lemma in_remove_all_not_in :
  forall A A_eq_dec ds l x,
    In x (remove_all (A:=A) A_eq_dec ds l) ->
    In x ds ->
    False.
Proof.
  induction ds; intros; simpl in *; intuition.
  - subst. find_apply_lem_hyp in_remove_all_was_in.
    eapply remove_In; eauto.
  - eauto.
Qed.

Lemma before_remove :
  forall A x y l y' dec,
    before (A := A) x y (remove dec y' l) ->
    y <> y' ->
    before x y l.
Proof.
  induction l; intros; simpl in *; intuition.
  break_if; subst; simpl in *; intuition eauto.
Qed.


Lemma before_remove_if :
  forall A (x : A) y l x' dec,
    before x y l ->
    x <> x' ->
    before x y (remove dec x' l).
Proof.
  induction l; intros; simpl in *; intuition;
  break_if; subst; simpl in *; intuition eauto.
Qed.

Lemma remove_all_nil :
  forall A dec ys,
    remove_all (A := A) dec ys [] = [].
Proof.
  intros. induction ys; simpl in *; intuition.
Qed.

Lemma remove_all_cons :
  forall A dec ys a l,
    (remove_all (A := A) dec ys (a :: l) = remove_all dec ys l /\
     In a ys) \/
    (remove_all (A := A) dec ys (a :: l) = a :: (remove_all dec ys l) /\
     ~In a ys).
Proof.
  induction ys; intros; simpl in *; intuition.
  break_if; subst; simpl in *; intuition.
  specialize (IHys a0 (remove dec a l)). intuition.
Qed.

Lemma before_remove_all :
  forall A x y l ys dec,
    before (A := A) x y (remove_all dec ys l) ->
    ~ In y ys ->
    before x y l.
Proof.
  induction l; intros; simpl in *; intuition.
  - rewrite remove_all_nil in *. simpl in *. intuition.
  - pose proof remove_all_cons dec ys a l. intuition.
    + repeat find_rewrite. right. intuition eauto.
      subst; intuition.
    + repeat find_rewrite. simpl in *. intuition eauto.
Qed.

Lemma before_remove_all_if :
  forall A x y l xs dec,
    before x y l ->
    ~ In x xs ->
    before (A := A) x y (remove_all dec xs l).
Proof.
  induction l; intros; simpl in *; intuition;
  pose proof remove_all_cons dec xs a l; subst; intuition;
  repeat find_rewrite; simpl in *; intuition.
Qed.

Lemma before_app :
  forall A x y l' l,
    before (A := A) x y (l' ++ l) ->
    ~ In x l' ->
    before (A := A) x y l.
Proof.
  induction l'; intros; simpl in *; intuition.
Qed.

Lemma before_app_if :
  forall A x y l' l,
    before (A := A) x y l ->
    ~ In y l' ->
    before (A := A) x y (l' ++ l).
Proof.
  induction l'; intros; simpl in *; intuition.
Qed.

Lemma before_antisymmetric :
  forall A x y l,
    before (A := A) x y l ->
    before y x l ->
    x = y.
Proof.
  intros.
  induction l; simpl in *; intuition; congruence.
Qed.

Lemma snoc_assoc :
  forall A (l : list A) x y,
    l ++ [x; y] = (l ++ [x]) ++ [y].
Proof.
  induction l; intros; simpl; intuition.
  auto using f_equal.
Qed.

Lemma cons_cons_app :
  forall A (x y : A),
    [x; y] = [x] ++ [y].
Proof.
  auto.
Qed.

(* from SF's tactics library *)
Section equatesLemma.
Variables
  (A0 A1 : Type)
  (A2 : forall(x1 : A1), Type)
  (A3 : forall(x1 : A1) (x2 : A2 x1), Type)
  (A4 : forall(x1 : A1) (x2 : A2 x1) (x3 : A3 x2), Type)
  (A5 : forall(x1 : A1) (x2 : A2 x1) (x3 : A3 x2) (x4 : A4 x3), Type)
  (A6 : forall(x1 : A1) (x2 : A2 x1) (x3 : A3 x2) (x4 : A4 x3) (x5 : A5 x4), Type).

Lemma equates_0 : forall(P Q:Prop),
  P -> P = Q -> Q.
Proof. intros. subst. auto. Qed.

Lemma equates_1 :
  forall(P:A0->Prop) x1 y1,
  P y1 -> x1 = y1 -> P x1.
Proof. intros. subst. auto. Qed.

Lemma equates_2 :
  forall y1 (P:A0->forall(x1:A1),Prop) x1 x2,
  P y1 x2 -> x1 = y1 -> P x1 x2.
Proof. intros. subst. auto. Qed.

Lemma equates_3 :
  forall y1 (P:A0->forall(x1:A1)(x2:A2 x1),Prop) x1 x2 x3,
  P y1 x2 x3 -> x1 = y1 -> P x1 x2 x3.
Proof. intros. subst. auto. Qed.

Lemma equates_4 :
  forall y1 (P:A0->forall(x1:A1)(x2:A2 x1)(x3:A3 x2),Prop) x1 x2 x3 x4,
  P y1 x2 x3 x4 -> x1 = y1 -> P x1 x2 x3 x4.
Proof. intros. subst. auto. Qed.

Lemma equates_5 :
  forall y1 (P:A0->forall(x1:A1)(x2:A2 x1)(x3:A3 x2)(x4:A4 x3),Prop) x1 x2 x3 x4 x5,
  P y1 x2 x3 x4 x5 -> x1 = y1 -> P x1 x2 x3 x4 x5.
Proof. intros. subst. auto. Qed.

Lemma equates_6 :
  forall y1 (P:A0->forall(x1:A1)(x2:A2 x1)(x3:A3 x2)(x4:A4 x3)(x5:A5 x4),Prop)
  x1 x2 x3 x4 x5 x6,
  P y1 x2 x3 x4 x5 x6 -> x1 = y1 -> P x1 x2 x3 x4 x5 x6.
Proof. intros. subst. auto. Qed.

End equatesLemma.

Lemma map_partition :
  forall A B p l (x : B) p' (f : A -> B),
    map f l = (p ++ x :: p') ->
    exists ap a ap',
      l = ap ++ a :: ap' /\
      map f ap = p /\
      f a = x /\
      map f ap' = p'.
Proof.
  induction p; intros; intuition; simpl in *.
  - destruct l; simpl in *; try congruence.
    find_inversion.
    exists [],a,l. simpl. auto.
  - destruct l; simpl in *; try congruence.
    find_inversion.
    find_apply_hyp_hyp.
    break_exists_name ap.
    break_exists_name a.
    break_exists_name ap'.
    intuition.
    exists (a0 :: ap), a, ap'. simpl.
    repeat find_rewrite. intuition.
Qed.

Lemma map_eq_inv :
  forall (A B : Type) (f : A -> B) (l : list A) xs ys,
    map f l = xs ++ ys ->
    exists l1, exists l2, l = l1 ++ l2 /\ map f l1 = xs /\ map f l2 = ys.
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

Lemma map_eq_inv_eq :
  forall (A B : Type) (f : A -> B),
    (forall a a', f a = f a' -> a = a') ->
    forall l l', map f l = map f l' -> l = l'.
Proof.
  induction l; simpl; intros l' Heq; destruct l'; simpl in *; try congruence.
  find_inversion. auto using f_equal2.
Qed.

Lemma map_fst_snd_id :
  forall A B l, map (fun t : A * B => (fst t, snd t)) l = l.
Proof.
  intros.
  rewrite <- map_id.
  apply map_ext.
  destruct a; auto.
Qed.

Inductive Nth {A : Type} : list A -> nat -> A -> Prop :=
| Nth_0 : forall x l, Nth (x :: l) 0 x
| Nth_S : forall l x n y, Nth l n x -> Nth (y :: l) (S n) x.

Lemma nth_error_Nth :
  forall A n l (x : A),
    nth_error l n = Some x ->
    Nth l n x.
Proof.
  induction n; intros; simpl in *; auto.
  - break_match; try discriminate.
    unfold value in *.
    find_inversion.
    constructor.
  - break_match; try discriminate.
    subst. constructor.
    eauto.
Qed.

Lemma Nth_nth_error :
  forall A n l (x : A),
    Nth l n x ->
    nth_error l n = Some x.
Proof.
  intros.
  induction H; simpl in *; auto.
Qed.