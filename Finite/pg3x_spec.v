Require Import ssreflect ssrfun ssrbool.

(** specification *)


Module Type ProjectiveSpace.

  Parameter Point : Type.

  Parameter Line: Type.

  (* eventuellement FinType *)
  (* Check ([forall p1 : Point, forall p2:Point, p1==p2]). *)
  (* Search _ [exists _ : _,_]. *)
  (* Search _ pick. *)
  (* Check (forall p1 p2:Point, forall l:Line, ((a1_exists p1) p2)=l). *)
  Parameter eqP : Point -> Point -> bool.
  Parameter eqL : Line -> Line -> bool.

  Parameter incid_lp : Point -> Line -> bool.
  
  (* A1 : any two points lie on a unique Line *)
  
  Axiom a1_exists : forall A B : Point,
                          {l : Line| incid_lp A l && incid_lp B l}.

  Axiom uniqueness : forall (A B :Point)(l1 l2:Line),
      incid_lp A l1 -> incid_lp B l1  ->
      incid_lp A l2 -> incid_lp B l2 -> A = B \/ l1 = l2.

(* A2 : Pasch's axiom *)
  Definition dist_4p  (A B C D:Point) : bool :=
    (negb (eqP A B)) && (negb (eqP A C)) && (negb (eqP A D))
                     && (negb (eqP B C)) && (negb (eqP B D)) && (negb (eqP C D)).

  Axiom a2 : forall A B C D:Point, forall lAB lCD lAC lBD :Line,
  	dist_4p A B C D -> 
	incid_lp A lAB && incid_lp B lAB ->
	incid_lp C lCD && incid_lp D lCD ->
	incid_lp A lAC && incid_lp C lAC ->
	incid_lp B lBD && incid_lp D lBD ->
	(exists I:Point, incid_lp I lAB && incid_lp I lCD) ->
        exists J:Point, incid_lp J lAC && incid_lp J lBD.

    (** A3 : dimension-related axioms *)
  Definition dist_3p  (A B C :Point) : bool := (negb (eqP A B)) && (negb (eqP A C)) && (negb (eqP B C)).

  Axiom a3_1 :
    forall l:Line,{A:Point & {B:Point & {C:Point |
                                         (dist_3p A B C) &&
                                         (incid_lp A l && incid_lp B l && incid_lp C l)}}}.

  (** there exists 2 lines which do not intersect *)
  Axiom a3_2 (* dim >= 3 *) :
    exists l1:Line, exists l2:Line,
      forall p:Point, ~(incid_lp p l1 && incid_lp p l2).

  Definition Intersect_In (l1 l2 :Line) (P:Point) := incid_lp P l1 && incid_lp P l2.

  Definition dist_3l (A B C :Line) : bool :=
    (negb (eqL A B)) && (negb (eqL A C)) && (negb (eqL B C)).

  Axiom a3_3 :  forall l1 l2 l3:Line,
      dist_3l l1 l2 l3 ->
      exists l4 :Line,  exists J1:Point, exists J2:Point, exists J3:Point,
	     Intersect_In l1 l4 J1 && Intersect_In l2 l4 J2 && Intersect_In l3 l4 J3.

End ProjectiveSpace.

(* Local Variables: *)
(* coq-prog-name: "/Users/magaud/.opam/4.06.0/bin/coqtop" *)
(* coq-load-path: ( ("." "Top") ) *)
(* suffixes: .v *)
(* End: *)

