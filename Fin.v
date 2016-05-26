Require Import List.
Import ListNotations.
Require Import StructTact.StructTactics.
Require Import StructTact.Util.
Require Import OrderedType.

Set Implicit Arguments.

Fixpoint fin (n : nat) : Type :=
  match n with
    | 0 => False
    | S n' => option (fin n')
  end.

Fixpoint fin_eq_dec (n : nat) : forall (a b : fin n), {a = b} + {a <> b}.
  refine match n with
    | 0 => fun a b : fin 0 => right (match b with end)
    | S n' => fun a b : fin (S n') =>
               match a, b with
                 | Some a', Some b' =>
                   match fin_eq_dec n' a' b' with
                     | left _ H => left _
                     | right _ H => right _
                   end
                 | Some a', None => right _
                 | None, Some b' => right _
                 | None, None => left _
               end
  end; congruence.
Defined.

Fixpoint all_fin (n : nat) : list (fin n) :=
  match n with
    | 0 => []
    | S n' => None :: map (fun x => Some x) (all_fin n')
  end.

Lemma all_fin_all :
  forall n (x : fin n),
    In x (all_fin n).
Proof.
  induction n; intros.
  - solve_by_inversion.
  - simpl in *. destruct x; auto using in_map.
Qed.

Lemma all_fin_NoDup :
  forall n, NoDup (all_fin n).
Proof.
  induction n; intros; simpl; constructor.
  - intro. apply in_map_iff in H. firstorder. discriminate.
  - apply NoDup_map_injective; auto. congruence.
Qed.

Fixpoint fin_to_nat {n : nat} : fin n -> nat :=
  match n with
  | 0 => fun x : fin 0 => match x with end
  | S n' => fun x : fin (S n') =>
             match x with
             | None => 0
             | Some y => S (fin_to_nat y)
             end
  end.

Definition fin_lt {n : nat} (a b : fin n) : Prop := lt (fin_to_nat a) (fin_to_nat b).

Lemma fin_lt_Some_elim :
  forall n (a b : fin n), 
    @fin_lt (S n) (Some a) (Some b) -> fin_lt a b.
Proof.
  intros.
  unfold fin_lt. simpl.
  intuition.
Qed.

Lemma fin_lt_Some_intro :
  forall n (a b : fin n), 
    fin_lt a b -> @fin_lt (S n) (Some a) (Some b).
Proof.
  intros.
  unfold fin_lt. simpl.
  intuition.
Qed.

Lemma None_lt_Some :
  forall n (x : fin n),
    @fin_lt (S n) None (Some x).
Proof.
  unfold fin_lt. simpl. auto with *.
Qed.

Lemma fin_lt_trans : 
  forall n (x y z : fin n),
    fin_lt x y -> fin_lt y z -> fin_lt x z.
Proof.
  induction n; intros.
  - destruct x.
  - destruct x, y, z; simpl in *;
    repeat match goal with
    | [ H : fin_lt (Some _) (Some _) |- _ ] => apply fin_lt_Some_elim in H
    | [ |- fin_lt (Some _) (Some _) ] => apply fin_lt_Some_intro
    end; eauto using None_lt_Some; solve_by_inversion.
Qed.

Lemma fin_lt_not_eq : 
  forall n (x y : fin n), 
    fin_lt x y -> x <> y.
Proof.
  induction n; intros.
  - destruct x.
  - destruct x, y;
    repeat match goal with
    | [ H : fin_lt (Some _) (Some _) |- _ ] => apply fin_lt_Some_elim in H
    | [ |- fin_lt (Some _) (Some _) ] => apply fin_lt_Some_intro
    end; try congruence.
    + specialize (IHn f f0). concludes. congruence.
    + solve_by_inversion.
Qed.

Fixpoint fin_compare (n : nat) : forall (x y : fin n), Compare fin_lt eq x y :=
  match n with
    | 0 => fun x y : fin 0 => match x with end
    | S n' => fun x y : fin (S n') =>
               match x, y with
                 | Some x', Some y' =>
                   match fin_compare n' x' y' with
                     | LT pf => LT (fin_lt_Some_intro pf)
                     | EQ pf => EQ (f_equal _ pf)
                     | GT pf => GT (fin_lt_Some_intro pf)
                   end
                 | Some x', None => GT (None_lt_Some n' x')
                 | None, Some y' => LT (None_lt_Some n' y')
                 | None, None => EQ eq_refl
               end
  end.

Module Type NatValue.
  Parameter n : nat.
End NatValue.

Module fin_OT_compat (N : NatValue) <: OrderedType.
  Definition t := fin N.n.
  Definition eq : t -> t -> Prop := eq.
  Definition lt : t -> t -> Prop := fin_lt.
  Definition eq_refl : forall x : t, eq x x := @eq_refl _.
  Definition eq_sym : forall x y: t, eq x y -> eq y x := @eq_sym _.
  Definition eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z := @eq_trans _.
  Definition lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z := @fin_lt_trans N.n.
  Definition lt_not_eq : forall x y : t, lt x y -> ~ eq x y := @fin_lt_not_eq N.n. 
  Definition compare : forall x y : t, Compare lt eq x y := fin_compare N.n.
  Definition eq_dec : forall x y : t, {eq x y} + {~ eq x y} := fin_eq_dec N.n.
End fin_OT_compat.

Require Import Orders.

Lemma fin_lt_irrefl : 
  forall n, Irreflexive (@fin_lt n).
Proof.
  intros.
  unfold Irreflexive, complement, Reflexive, fin_lt.
  intuition.
Qed.

Lemma fin_lt_strorder : forall n, StrictOrder (@fin_lt n).
Proof.
  intros.
  apply (Build_StrictOrder _ (@fin_lt_irrefl n) (@fin_lt_trans n)).
Qed.

Lemma fin_lt_lt_compat : 
  forall n, Proper (eq ==> eq ==> iff) (@fin_lt n).
Proof.
  intros; split; intros; repeat find_rewrite; assumption.
Qed.

Lemma CompSpec_Eq_Some : 
  forall n' (x' y' : fin n'),
    CompSpec eq fin_lt x' y' Eq ->
    Some x' = Some y'.
Proof.
  intros.
  apply f_equal.
  solve_by_inversion.
Qed.

Lemma CompSpec_Lt : 
  forall n' (x' y' : fin n'),
    CompSpec eq fin_lt x' y' Lt ->
    fin_lt x' y'.
Proof.
  intros.
  solve_by_inversion.
Qed.

Lemma CompSpec_Gt : 
  forall n' (x' y' : fin n'),
    CompSpec eq fin_lt x' y' Gt ->
    fin_lt y' x'.
Proof.
  intros.
  solve_by_inversion.
Qed.

Fixpoint fin_comparison_dec (n : nat) :
  forall (x y : fin n), { cmp : comparison | CompSpec eq fin_lt x y cmp } :=
  match n with
    | 0 => fun x y : fin 0 => match x with end
    | S n' => fun x y : fin (S n') =>
             match x, y with
               | Some x', Some y' =>
                 match fin_comparison_dec n' x' y' with
                   | exist _ Lt Hc => exist _ Lt (CompLt _ _ (fin_lt_Some_intro (CompSpec_Lt Hc)))
                   | exist _ Eq Hc => exist _ Eq (CompEq _ _ (CompSpec_Eq_Some Hc))
                   | exist _ Gt Hc => exist _ Gt (CompGt _ _ (fin_lt_Some_intro (CompSpec_Gt Hc)))
                 end
               | Some x', None => exist _ Gt (CompGt _ _ (None_lt_Some n' x'))
               | None, Some y' => exist _ Lt (CompLt _ _ (None_lt_Some n' y'))
               | None, None => exist _ Eq (CompEq _ _ eq_refl)
             end
  end.

Definition fin_comparison (n : nat) (x y : fin n) : comparison :=
match fin_comparison_dec n x y with exist _ cmp _ => cmp end.

Lemma fin_compare_spec : forall (n : nat) (x y : fin n), 
    CompSpec eq fin_lt x y (fin_comparison n x y).
Proof.
  intros.
  unfold fin_comparison.
  break_match.
  assumption.
Qed.

Module fin_OT (N : NatValue) <: OrderedType.
  Definition t := fin N.n.
  Definition eq := eq (A := fin N.n).
  Definition eq_equiv := eq_equivalence (A := fin N.n).
  Definition lt := fin_lt (n := N.n).
  Definition lt_strorder := fin_lt_strorder N.n.
  Definition lt_compat := fin_lt_lt_compat N.n.
  Definition compare := fin_comparison N.n.
  Definition compare_spec := fin_compare_spec N.n.
  Definition eq_dec := fin_eq_dec N.n.
End fin_OT.

Fixpoint fin_of_nat (m n : nat) : fin n + {exists p, m = n + p} :=
  match n as n0 return fin n0 + {exists p, m = n0 + p} with
  | 0 => inright (ex_intro _ m eq_refl)
  | S n' =>
    match m as m0 return fin (S n') + {exists p, m0 = (S n') + p} with
    | 0 => inleft None
    | S m' =>
      match fin_of_nat m' n' with
      | inleft f => inleft (Some f)
      | inright pf => inright (let 'ex_intro _ x H := pf in
                              ex_intro _ x (f_equal S H))
      end
    end
  end.

Lemma fin_of_nat_fin_to_nat:
  forall (n : nat) (a : fin n), fin_of_nat (fin_to_nat a) n = inleft a.
Proof.
  induction n; simpl; intuition.
  destruct a; simpl in *; auto.
  now rewrite IHn.
Qed.
