Require Import Omega.
Require Import List.
Import ListNotations.
Require Import StructTact.StructTactics.
Require Import StructTact.ListTactics.

Set Implicit Arguments.

Section take.
  Variable A : Type.

  Fixpoint take (n : nat) (xs : list A) : list A :=
    match n with
    | O => []
    | S n' => match xs with
             | [] => []
             | x :: xs' => x :: take n' xs'
             end
    end.

  Lemma in_take : forall n (x : A) xs,
      In x (take n xs) -> In x xs.
  Proof.
    induction n; simpl; intuition; break_match; simpl in *; intuition.
  Qed.

  Lemma take_NoDup : forall n (xs : list A),
      NoDup xs ->
      NoDup (take n xs).
  Proof.
    induction n; intros; simpl; destruct xs; auto with struct_util.
    invc_NoDup.
    eauto 6 using in_take with struct_util.
  Qed.

  Lemma take_length : forall n (xs : list A),
      length xs >= n ->
      length (take n xs) = n.
  Proof.
    induction n; intros.
    - auto.
    - simpl. break_match; simpl in *.
      + omega.
      + now rewrite IHn by omega.
  Qed.

  Lemma take_length_ge : forall n m (xs : list A),
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
End take.
