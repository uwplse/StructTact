Require Import List.
Import ListNotations.
Require Import StructTact.StructTactics.
Require Import StructTact.ListUtil.
Require Import StructTact.RemoveAll.
Require Import FunctionalExtensionality.
Require Import Sumbool.
Require Import Sorting.Permutation.
Require Import Relation_Definitions.
Require Import RelationClasses.

Definition update2 {A B : Type} (A_eq_dec : forall x y : A, {x = y} + {x <> y}) (f : A -> A -> B) (x y : A) (v : B) :=
  fun x' y' => if sumbool_and _ _ _ _ (A_eq_dec x x') (A_eq_dec y y') then v else f x' y'.

Fixpoint collate {A B : Type} (A_eq_dec : forall x y : A, {x = y} + {x <> y}) (from : A) (f : A -> A -> list B) (ms : list (A * B)) :=
  match ms with
   | [] => f
   | (to, m) :: ms' => collate A_eq_dec from (update2 A_eq_dec f from to (f from to ++ [m])) ms'
  end.

Fixpoint collate_ls {A B : Type} (A_eq_dec : forall x y : A, {x = y} + {x <> y}) (s : list A) (f : A -> A -> list B) (to : A) (m : B) :=
  match s with
   | [] => f
   | from :: s' => collate_ls A_eq_dec s' (update2 A_eq_dec f from to (f from to ++ [m])) to m
  end.

Fixpoint filter_rel {A : Type} {rel : relation A} (A_rel_dec : forall x y : A, {rel x y} + {~ rel x y}) (x : A) (l : list A) :=
  match l with
   | [] => []
   | y :: tl => if A_rel_dec x y then y :: filter_rel A_rel_dec x tl else filter_rel A_rel_dec x tl
  end.

Definition map2fst {A B : Type} (a : A) := map (fun (b : B) => (a, b)).

Definition map2snd {A B : Type} (b : B) := map (fun (a : A) => (a, b)).
