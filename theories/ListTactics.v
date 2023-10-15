From Coq Require Import List.
From StructTact Require Import StructTactics.

Ltac do_in_map :=
  match goal with
    | [ H : In _ (map _ _) |- _ ] => apply in_map_iff in H; break_exists; break_and
  end.

Ltac do_in_app :=
  match goal with
    | [ H : In _ (_ ++ _) |- _ ] => apply in_app_iff in H
  end.

Ltac invc_NoDup :=
  repeat match goal with
  | [ H : NoDup (_ :: _) |- _ ] => invc H
  end.

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

Ltac in_crush_start_tac tac :=
  tac; simpl in *;
  repeat
    (match goal with
       | [ H : In _ (map _ _) |- _ ] => apply in_map_iff in H; break_exists; break_and
       | [ H : In _ (_ ++ _) |- _ ] => apply in_app_iff in H
     end; tac; simpl in *); subst.

Tactic Notation "in_crush_start" := in_crush_start_tac intuition.

Ltac in_crush_tac tac := repeat (in_crush_start_tac tac; in_crush_finish).

Tactic Notation "in_crush" := in_crush_tac intuition.

Create HintDb struct_util.

#[global] Hint Constructors NoDup : struct_util.
