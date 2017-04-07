Require Export ProjectiveGeometry.Dev.fano_matroid_tactics.

(** Fano's plane **)
(** also known as Pg(2,2). **)

(** To show that our axiom system is consistent we build a finite model. **)


(*****************************************************************************)


Section s_fanoPlaneModelRk.

Parameter A B C D E F G : Point.

Parameter is_only_7_pts : forall P, {P=A}+{P=B}+{P=C}+{P=D}+{P=E}+{P=F}+{P=G}.

Parameter rk_points : rk(A :: nil) = 1 /\ rk(B :: nil) = 1 /\ rk(C :: nil) = 1 /\ rk(D :: nil) = 1 /\
rk(E :: nil) = 1 /\ rk(F :: nil) = 1 /\ rk(G :: nil) = 1.

Parameter rk_distinct_points : 
rk(A :: B :: nil) = 2 /\ rk(A :: C :: nil) = 2 /\ rk(A :: D :: nil) = 2 /\ rk(A :: E :: nil) = 2 /\rk(A :: F :: nil) = 2 /\ rk(A :: G :: nil) = 2 /\
rk(B :: C :: nil) = 2 /\ rk(B :: D :: nil) = 2 /\ rk(B :: E :: nil) = 2 /\ rk(B :: F :: nil) = 2 /\ rk(B :: G :: nil) = 2 /\
rk(C :: D :: nil) = 2 /\ rk(C :: E :: nil) = 2 /\ rk(C :: F :: nil) = 2 /\ rk(C :: G :: nil) = 2 /\
rk(D :: E :: nil) = 2 /\ rk(D :: F :: nil) = 2 /\ rk(D :: G :: nil) = 2 /\
rk(E :: F :: nil) = 2 /\ rk(E :: G :: nil) = 2 /\
rk(F :: G :: nil) = 2.

Parameter rk_lines : rk (A :: B :: F :: nil) = 2 /\ rk (B :: C :: D :: nil) = 2 /\ 
rk (C :: A :: E :: nil) = 2 /\ rk (A :: D :: G :: nil) = 2 /\ rk (B :: E :: G :: nil) = 2 /\
rk (C :: F :: G :: nil) = 2 /\ rk (D :: E :: F :: nil) = 2.

Parameter rk_planes : 
rk(A :: B :: C :: nil) = 3 /\ rk(A :: B :: D :: nil) = 3 /\ rk(A :: B :: E :: nil) = 3 /\ rk(A :: B :: G :: nil) = 3 /\
rk(A :: C :: D :: nil) = 3 /\ rk(A :: C :: F :: nil) = 3 /\ rk(A :: C :: G :: nil) = 3 /\ rk(A :: D :: E :: nil) = 3 /\
rk(A :: D :: F :: nil) = 3 /\ rk(A :: E :: F :: nil) = 3 /\ rk(A :: E :: G :: nil) = 3 /\ rk(A :: F :: G :: nil) = 3 /\
rk(B :: C :: E :: nil) = 3 /\ rk(B :: C :: F :: nil) = 3 /\ rk(B :: C :: G :: nil) = 3 /\ rk(B :: D :: E :: nil) = 3 /\
rk(B :: D :: F :: nil) = 3 /\ rk(B :: D :: G :: nil) = 3 /\ rk(B :: E :: F :: nil) = 3 /\ rk(B :: F :: G :: nil) = 3 /\
rk(C :: D :: E :: nil) = 3 /\ rk(C :: D :: F :: nil) = 3 /\ rk(C :: D :: G :: nil) = 3 /\ rk(C :: E :: F :: nil) = 3 /\
rk(C :: E :: G :: nil) = 3 /\ rk(D :: E :: G :: nil) = 3 /\ rk(D :: F :: G :: nil) = 3 /\ rk(E :: F :: G :: nil) = 3.


(*****************************************************************************)


Ltac new_case P := 
match (type of P) with 
| Point => generalize (is_only_7_pts P) ; let Q := fresh in (intros Q; decompose [sumor sumbool] Q; clear Q)
end.

Ltac case_eq_s O := new_case O.

Ltac case_clear_1 P := case_eq_s P.

Ltac case_clear_2 P :=
  case_clear_1 P;
  match goal with
| H : P = ?X |- _ => subst
end.

(** rk-singleton : The rank of a point is always greater than one  **) 
Lemma rk_singleton_ge : forall P, rk (P :: nil) >= 1.
Proof.
intros.
assert(HH := rk_points);use HH.
case_clear_2 P;intuition.
Qed.

Lemma rk_couple_ge_alt : forall P Q, rk(P :: Q :: nil) = 2 -> rk(P :: Q :: nil) >=2.
Proof.
intuition.
Qed.

(** rk-couple : The rank of a two distinct points is always greater than one  **)
Lemma rk_couple_ge : forall P Q, ~ P = Q -> rk(P :: Q :: nil) >= 2.
Proof.
intros.
assert(HH := rk_distinct_points);use HH.
apply rk_couple_ge_alt.
case_clear_2 P;case_clear_2 Q;try equal_degens;try assumption;rewrite couple_equal;assumption.
Qed.

Lemma triple_rk2_1 : forall P R, rk(P :: R :: nil) = 2 -> rk(P :: P :: R :: nil) = 2.
Proof.
intros.
assert(HH : equivlist (P :: P :: R :: nil) (P :: R :: nil));[my_inA|];rewrite HH;intuition.
Qed.

Lemma triple_rk2_2 : forall P R, rk(P :: R :: nil) = 2 -> rk(P :: R :: P :: nil) = 2.
Proof.
intros.
assert(HH : equivlist (P :: R :: P :: nil) (P :: R :: nil));[my_inA|];rewrite HH;intuition.
Qed.

Lemma triple_rk2_3 : forall P R, rk(P :: R :: nil) = 2 -> rk(R :: P :: P :: nil) = 2.
Proof.
intros.
assert(HH : equivlist (R :: P :: P :: nil) (P :: R :: nil));[my_inA|];rewrite HH;intuition.
Qed.

Ltac degens_rk2 :=
match goal with
| H : _ |- rk(?P :: ?P :: ?R :: nil) = 2 => try solve[apply triple_rk2_1;rk_couple_bis_bis;assumption]
| H : _ |- rk(?P :: ?R :: ?P :: nil) = 2 => try solve[apply triple_rk2_2;rk_couple_bis_bis;assumption]
| H : _ |- rk(?R :: ?P :: ?P :: nil) = 2 => try solve[apply triple_rk2_3;rk_couple_bis_bis;assumption]
end.

Ltac solve_ex_1 L := solve[exists L;repeat split;[try degens_rk2;assumption|rk_couple_bis_bis|rk_couple_bis_bis]].

Ltac solve_ex_p_1 := first [
        solve_ex_1 A
     |  solve_ex_1 B
     |  solve_ex_1 C
     |  solve_ex_1 D
     |  solve_ex_1 E
     |  solve_ex_1 F
     |  solve_ex_1 G
 ].

Ltac rk_three_points_simplify P Q :=
match goal with
| H : rk(P :: Q :: ?X :: nil) = 2 |- _ => solve_ex_1 X
| H : rk(P :: ?X :: Q :: nil) = 2 |- _ => rewrite <-triple_equal_1 in H;solve_ex_1 X
| H : rk(Q :: P :: ?X :: nil) = 2 |- _ => rewrite <-triple_equal_2 in H;solve_ex_1 X
| H : rk(Q :: ?X :: P :: nil) = 2 |- _ => rewrite <-triple_equal_3 in H;solve_ex_1 X
| H : rk(?X :: P :: Q :: nil) = 2 |- _ => rewrite <-triple_equal_4 in H;solve_ex_1 X
| H : rk(?X :: Q :: P :: nil) = 2 |- _ => rewrite <-triple_equal_5 in H;solve_ex_1 X
end.

Ltac rk_three_points_simplify_bis :=
match goal with
| H : _ |- exists R, rk (?P :: ?P :: _ :: nil) = 2 /\ _ /\ _ => solve_ex_p_1
| H : _ |- exists R, rk (?P :: ?Q :: _ :: nil) = 2 /\ _ /\ _ => rk_three_points_simplify P Q
end.

(** rk-three_point_on_lines : Each lines contains at least three points **)
Lemma rk_three_points_on_lines : forall P Q, exists R, 
rk (P :: Q :: R :: nil) = 2 /\ rk (Q :: R :: nil) = 2 /\ rk (P :: R :: nil) = 2.
Proof.
intros.
assert(HH := rk_distinct_points);assert(HH0 := rk_lines);use HH;use HH0.
case_clear_2 P;case_clear_2 Q;rk_three_points_simplify_bis.
Qed.

Ltac solve_ex_2 L := solve [exists L;repeat split;try degens_rk2;rk_triple_bis_bis].

Ltac solve_ex_p_2 := first [
        solve_ex_2 A
     |  solve_ex_2 B
     |  solve_ex_2 C
     |  solve_ex_2 D
     |  solve_ex_2 E
     |  solve_ex_2 F
     |  solve_ex_2 G
 ].

Ltac rk_inter_simplify P Q R S X Y :=
match goal with
| H : _ |- exists J, rk (_ :: Y :: _ :: nil) = 2 /\ rk (_ :: _ :: _ :: nil) = 2 => try solve_ex_2 Y
| H : _ |- exists J, rk (Y :: _ :: _ :: nil) = 2 /\ rk (_ :: _ :: _ :: nil) = 2 => try solve_ex_2 Y
| H : _ |- exists J, rk (_ :: _ :: _ :: nil) = 2 /\ rk (_ :: X :: _ :: nil) = 2 => try solve_ex_2 X
| H : _ |- exists J, rk (_ :: _ :: _ :: nil) = 2 /\ rk (X :: _ :: _ :: nil) = 2 => try solve_ex_2 X
| H : _ |- exists J, rk (_ :: _ :: _ :: nil) = 2 /\ rk (_ :: _ :: _ :: nil) = 2 => try solve_ex_2 X
end.

Ltac rk_inter_simplify_bis P Q R S X :=
match goal with
| H : rk(R :: S :: ?Y :: nil) = 2 |- _ => rk_inter_simplify P Q R S X Y 
| H : rk(R :: ?Y :: S :: nil) = 2 |- _ => rk_inter_simplify P Q R S X Y
| H : rk(S :: R :: ?Y :: nil) = 2 |- _ => rk_inter_simplify P Q R S X Y
| H : rk(S :: ?Y :: R :: nil) = 2 |- _ => rk_inter_simplify P Q R S X Y
| H : rk(?Y :: R :: S :: nil) = 2 |- _ => rk_inter_simplify P Q R S X Y
| H : rk(?Y :: S :: R :: nil) = 2 |- _ => rk_inter_simplify P Q R S X Y
end.

Ltac rk_inter_simplify_bis_bis P Q R S :=
match goal with
| H : rk(P :: Q :: ?X :: nil) = 2 |- _ => rk_inter_simplify_bis P Q R S X
| H : rk(P :: ?X :: Q :: nil) = 2 |- _ => rk_inter_simplify_bis P Q R S X
| H : rk(Q :: P :: ?X :: nil) = 2 |- _ => rk_inter_simplify_bis P Q R S X
| H : rk(Q :: ?X :: P :: nil) = 2 |- _ => rk_inter_simplify_bis P Q R S X
| H : rk(?X :: P :: Q :: nil) = 2 |- _ => rk_inter_simplify_bis P Q R S X
| H : rk(?X :: Q :: P :: nil) = 2 |- _ => rk_inter_simplify_bis P Q R S X
end.

Ltac rk_inter_simplify_bis_bis_bis :=
match goal with
| H : _ |- exists J, rk (?P :: ?P :: _ :: nil) = 2 /\ rk (?P :: ?P :: _ :: nil) = 2 => solve_ex_p_2
| H : _ |- exists J, rk (?P :: ?P :: _ :: nil) = 2 /\ rk (?Q :: ?Q :: _ :: nil) = 2 => solve_ex_p_2

| H : _ |- exists J, rk (?P :: ?Q :: _ :: nil) = 2 /\ rk (?P :: ?P :: _ :: nil) = 2 => solve_ex_2 P
| H : _ |- exists J, rk (?Q :: ?P :: _ :: nil) = 2 /\ rk (?Q :: ?Q :: _ :: nil) = 2 => solve_ex_2 P
| H : _ |- exists J, rk (?Q :: ?Q :: _ :: nil) = 2 /\ rk (?P :: ?Q :: _ :: nil) = 2 => solve_ex_2 P
| H : _ |- exists J, rk (?Q :: ?Q :: _ :: nil) = 2 /\ rk (?Q :: ?P :: _ :: nil) = 2 => solve_ex_2 P

| H : _ |- exists J, rk (?P :: ?Q :: _ :: nil) = 2 /\ rk (?R :: ?R :: _ :: nil) = 2 => solve_ex_2 P
| H : _ |- exists J, rk (?R :: ?R :: _ :: nil) = 2 /\ rk (?P :: ?Q :: _ :: nil) = 2 => solve_ex_2 P

| H : _ |- exists J, rk (?P :: ?Q :: _ :: nil) = 2 /\ rk (?R :: ?P :: _ :: nil) = 2 => solve_ex_2 P
| H : _ |- exists J, rk (?P :: ?Q :: _ :: nil) = 2 /\ rk (?P :: ?R :: _ :: nil) = 2 => solve_ex_2 P
| H : _ |- exists J, rk (?Q :: ?P :: _ :: nil) = 2 /\ rk (?R :: ?P :: _ :: nil) = 2 => solve_ex_2 P
| H : _ |- exists J, rk (?Q :: ?P :: _ :: nil) = 2 /\ rk (?P :: ?R :: _ :: nil) = 2 => solve_ex_2 P

| H : _ |- exists J, rk (?P :: ?Q :: _ :: nil) = 2 /\ rk (?R :: ?S :: _ :: nil) = 2 => rk_inter_simplify_bis_bis P Q R S
end.

(** rk-inter : Two lines always intersect in the plane **)
Lemma rk_inter : forall P Q R S, exists J, rk (P :: Q :: J :: nil) = 2 /\ rk (R :: S :: J :: nil) = 2.
Proof.
intros.
assert(HH := rk_distinct_points);assert(HH0 := rk_lines);use HH;use HH0.
case_clear_2 P;case_clear_2 Q;
abstract(case_clear_2 R;case_clear_2 S;try rk_inter_simplify_bis_bis_bis).
Qed.

(** rk-lower_dim : There exist three points which are not collinear **)
Lemma rk_lower_dim : exists P0 P1 P2, rk( P0 :: P1 :: P2 :: nil) >=3.
Proof.
intros.
assert(HH := rk_planes);use HH.
exists A;exists B;exists C;intuition.
Qed.

End s_fanoPlaneModelRk.