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
  | [ H : _ = _ |- _ ] => fail 2 "subst_max didn't substitute everything"
  | [ |- _ ] => idtac
  end.
  (* make sure goal solvable by reflexivity *)
  match goal with
  | [ |- ?X = ?X ] => reflexivity
  | _ => fail 2 "subst_max didn't fully substitute in goal"
  end.
Qed.

(* TODO: test these tactics *)
(* inv *)
(* invc *)
(* invcs *)


(* break_if *)
(* Desired properties: *)
(* - does in fact break apart if statements *)
Lemma break_if_test_bool_1 :
  forall (x : bool) (A : Type) (a b y : A),
         (y = if x then a else b) ->
         y = a \/ y = b.
Proof.
  intros.
  break_if;
    firstorder.
Qed.

(* break_if *)
(* make sure gets many different if expressions *)
Lemma break_if_test_many :
  forall (x1 x2 x3 x4 x5 : bool) (A : Type) (a b y : A),
         (y = if x1 then a else b) ->
         (y = if x2 then a else b) ->
         (y = if x3 then a else b) ->
         (y = if x4 then a else b) ->
         (y = if x5 then a else b) ->
         y = a \/ y = b.
Proof.
  intros.
  repeat break_if;
    (* make sure no more if exprs in hypotheses *)
    match goal with
    | [ H : context[if _ then _ else _ ] |- _] => fail 2 "still if exprs in hypotheses"
    | [ |- _ ] => idtac
    end;
    try solve [left; auto].
  right. auto.
Qed.

Inductive threecon :=
| A
| B
| C.

(* break_if doesn't get other matches *)
Lemma break_if_no_destruct_match :
  forall (n : threecon) (A : Type) (a b c x : A),
    (x = match n with
        | A => a
        | B => b
        | C => c
         end) ->
    False.
Proof.
  intros.
  repeat break_if;
    match goal with
    | [ H : context[match _ with _ => _ end] |- _ ] => idtac
    | [ |- _ ] => fail 2 "break_if destructed the match"
    end.
Abort. (* we make sure that we don't break apart the match, don't need to prove the goal *)

Lemma break_if_destructs_goal :
  forall (x : bool) (A : Type) (a b y : A),
    a = b ->
    y = a ->
    (y = if x then a else b).
Proof.
  intros.
  break_if;
  match goal with
  | [ |- context[if _ then _ else _]] => fail 2 "break if didn't destruct goal"
  | [ |- _ ] => idtac
  end;
  congruence.

Qed.

(* Email Coq-Club about this *)
Ltac no_run tac := idtac.
  (* let flag := fresh "flag" in *)
  (* evar (flag : bool); *)
  (* try (idtac; (instantiate (1 := true) in (Value of flag))); *)
  (* instantiate (1 := false) in (Value of flag). *)

Ltac x := match goal with
          | [ |- _ ] => assert (true = false) by congruence
          | [ H : _ |- _ ] => idtac
          end.

Ltac y := fail 9999 "oops".

(* 
Lemma break_match_hyp_test_1 :
  forall (n : threecon) (A : Type) (a b c x : A),
    (x = match n with
        | A => a
        | B => b
        | C => c
         end) ->
    x = a \/ x = b \/ x = c.
Proof.
  no_run x.
  let flag := fresh "flag" in
  evar (flag : bool);
  try (x; (instantiate (1 := true) in (Value of flag)));
  instantiate (1 := false) in (Value of flag).
  
  no_run x.
  no_run break_match_hyp.
  no_run fail.
  no_run auto.

  ((break_match_hyp; fail 1 "could run but shouldn't") || idtac).
  intros.
  break_match_hyp;
    solve [auto].
Qed.
  *)

  
  
  



