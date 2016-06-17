Require Import StructTact.StructTactics.


(* subst_max *)
(* like subst but better *)
(* Desired properties: *)
(* make sure substitutes everything *)
(* doesn't barf on recursive equalities *)
Lemma subst_max_test_1 :
  forall (A : Type) (a b c d : A),
    a = a ->
    a = b ->
    b = a ->
    a = c ->
    c = a ->
    b = c ->
    c = b ->
    d = a ->
    d = d ->
    d = c.
Proof.
  intros.
  (* make sure goal is solveable by substitution *)
  match goal with
  | [ |- ?G ] =>
    let H := fresh "H" in
    assert (H : G) by congruence;
      clear H
  end.
  subst_max.
  (* make sure all hypotheses are fully substituted *)
  repeat match goal with
         | [ H : ?X = ?Y |- _ ] =>
           let H2 := fresh "H" in
           assert (H2 : X = Y) by reflexivity;
             clear H; clear H2 (* clear all that pass the test *)
         end.
  (* make sure no more hypotheses *)
  match goal with
  | [ H : _ = _ |- _ ] => fail "subst_max didn't substitute everything"
  | [ |- _ ] => idtac
  end.
  (* make sure goal solvable by reflexivity *)
  match goal with
  | [ |- ?X = ?X ] => reflexivity
  | _ => fail "subst_max didn't fully substitute in goal"
  end.
Qed.

(* TODO: test these tactics *)
(* inv *)
(* invc *)
(* invcs *)


(* break_if *)
(* Desired properties: *)
(* - does in fact break apart if statements *)
