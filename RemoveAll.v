Require Import List.
Import ListNotations.
Require Import StructTact.StructTactics.
Require Import StructTact.ListUtil.
Require Import StructTact.Before.

Set Implicit Arguments.

Section remove_all.
  Variable A : Type.
  Hypothesis A_eq_dec : forall x y : A, {x = y} + {x <> y}.

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

  Lemma in_remove_all_not_in :
    forall ds l x,
      In x (remove_all ds l) ->
      In x ds ->
      False.
  Proof.
    induction ds; intros; simpl in *; intuition.
    - subst. find_apply_lem_hyp in_remove_all_was_in.
      eapply remove_In; eauto.
    - eauto.
  Qed.

  Lemma remove_all_nil :
    forall ys,
      remove_all ys [] = [].
  Proof.
    intros. induction ys; simpl in *; intuition.
  Qed.

  Lemma remove_all_cons :
    forall ys a l,
      (remove_all ys (a :: l) = remove_all ys l /\
       In a ys) \/
      (remove_all ys (a :: l) = a :: (remove_all ys l) /\
       ~In a ys).
  Proof.
    induction ys; intros; simpl in *; intuition.
    break_if; subst; simpl in *; intuition.
    specialize (IHys a0 (remove A_eq_dec a l)). intuition.
  Qed.

  Lemma before_remove_all :
    forall x y l ys,
      before x y (remove_all ys l) ->
      ~ In y ys ->
      before x y l.
  Proof.
    induction l; intros; simpl in *; intuition.
    - rewrite remove_all_nil in *. simpl in *. intuition.
    - pose proof remove_all_cons ys a l. intuition.
      + repeat find_rewrite. right. intuition eauto.
        subst; intuition.
      + repeat find_rewrite. simpl in *. intuition eauto.
  Qed.

  Lemma before_remove_all_if :
    forall x y l xs,
      before x y l ->
      ~ In x xs ->
      before x y (remove_all xs l).
  Proof.
    induction l; intros; simpl in *; intuition;
      pose proof remove_all_cons xs a l; subst; intuition;
        repeat find_rewrite; simpl in *; intuition.
  Qed.
End remove_all.
Arguments in_remove_all_was_in : clear implicits.
