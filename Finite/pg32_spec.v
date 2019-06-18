Require Import ords ssrbool ssrfun ssreflect pg32_ind.

(** PG(3,2) the smallest projective space*)
(** http://demonstrations.wolfram.com/15PointProjectiveSpace/ *)
(** 15 points and 35 lines, 15 planes*)

(** Data structures and induction principles are defined using the generator: *)
(** ./s pg32_ind.v 15 35 *)

(** Incidence relation *)

Definition three_points (p1 p2 p3:Point) :=
[ fun p : Point => false with p1 |-> true, p2 |-> true, p3 |-> true].

Notation o n m := (@Ordinal n m is_true_true).

Notation online3 p p1 p2 p3 := (three_points (o 15 p1) (o 15 p2) (o 15 p3) p).

Definition incid_lp :=
  [ fun p:Point => [ fun l : Line => false with 
    0  |-> online3 p 0 1 2, 
    1  |-> online3 p 0 3 4,
    2  |-> online3 p 0 5 6,
    3  |-> online3 p 0 7 8,
    4  |-> online3 p 0 10 9,
    5  |-> online3 p 0 11 12,
    6  |-> online3 p 0 13 14,
    
    7  |-> online3 p 1 4 6,
    8  |-> online3 p 1 8 10,
    9  |-> online3 p 1 12 14,
    10 |-> online3 p 1 7 9,
    11 |-> online3 p 1 13 11,
    12 |-> online3 p 1 3 5,

    13 |-> online3 p 2 7 10,
    14 |-> online3 p 2 11 14,
    15 |-> online3 p 2 3 6,
    16 |-> online3 p 2 12 13,
    17 |-> online3 p 2 4 5,
    18 |-> online3 p 2 8 9,

    19 |-> online3 p 3 10 14,
    20 |-> online3 p 3 8 12,
    21 |-> online3 p 3 9 13,
    22 |-> online3 p 3 7 11,

    23 |-> online3 p 4 9 14,
    24 |-> online3 p 4 8 11,
    25 |-> online3 p 4 10 13,
    26 |-> online3 p 4 7 12,

    27 |-> online3 p 5 8 14,
    28 |-> online3 p 5 7 13,
    29 |-> online3 p 5 9 11,
    30 |-> online3 p 5 10 12,
    
    31 |-> online3 p 6 7 14,
    32 |-> online3 p 6 8 13,
    33 |-> online3 p 6 9 12,
    34 |-> online3 p 6 10 11
  ]].

Check incid_lp.

(*Definition Incid : Point -> Line -> Prop := fun P L => (incid_lp P L = true).*)
(** a small tactic to deal with degenerated cases *)
Lemma degen_ord : forall P, forall t x, forall p1 p2: x<t, Ordinal p1 <> Ordinal p2 -> P.
Proof.
  intros.
  apply False_rect.
  apply H; apply : val_inj; reflexivity.
Qed.

Ltac remove_cases :=
  match goal with
  | H:Ordinal (n:=?t) (m:=?x) ?p1 <> Ordinal (n:=?t) (m:=?x) ?p2 |- ?G =>
    exact (@degen_ord G t x p1 p2 H)
  | H:is_true _ |- ?G => exact (@degen_bool G H)
  | H:@eq bool _ true |- ?G => exact (@degen_bool G H)
  end.

(** tactics designed to test all possible lines/points *)

Ltac try_all_aux n p tac := match p with
                      | O => fail
                      | S ?q =>  tac (o n q) || try_all_aux n q tac end.

Ltac try_all n tac := try_all_aux n n tac.


Ltac try_all_l tac := try_all 35 tac.
Ltac try_all_p tac := try_all 15 tac.

(* Local Variables: *)
(* coq-prog-name: "/Users/magaud/.opam/4.07.0/bin/coqtop" *)
(* coq-load-path: (("." "Top") ) *)
(* suffixes: .v *)
(* End: *)