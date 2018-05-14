Require Export ProjectiveGeometry.Dev.fano_matroid_tactics.
Require Export ProjectiveGeometry.Dev.basic_rank_plane_list.

Lemma triple_rk3_to_quadruple_rk3 : forall P Q R S : Point,
rk(P :: Q ::  R :: nil) = 3 -> rk(P :: Q :: R :: S :: nil) = 3.
Proof.
intros.
assert(HH : incl (P :: Q :: R :: nil) (P :: Q :: R :: S :: nil));[my_inO|].
assert(HH0 := matroid2 (P :: Q :: R :: nil) (P :: Q :: R :: S :: nil) HH).
assert(HH1 := rk_quadruple_max_3 P Q R S).
omega.
Qed.

Lemma quadruple_rk2_to_triple_rk2 : forall P Q R S : Point,
~ P = Q -> rk(P :: Q ::  R :: S :: nil) = 2 -> rk(P :: Q :: R :: nil) = 2.
Proof.
intros.
assert(HH : incl (P :: Q :: R :: nil) (P :: Q :: R :: S :: nil));[my_inO|].
assert(HH0 := matroid2 (P :: Q :: R :: nil) (P :: Q :: R :: S :: nil) HH).
assert(HH1 := rk_couple P Q H).
assert(HH2 : incl (P :: Q :: nil) (P :: Q :: R :: nil));[my_inO|].
assert(HH3 := matroid2 (P :: Q :: nil) (P :: Q :: R :: nil) HH2).
omega.
Qed.

Ltac rk_quadruple :=
match goal with
| H : rk(?A :: ?B :: ?C :: ?D :: nil) = _ |- rk(?A :: ?B :: ?C :: ?D :: nil) = _ => assumption
| H : rk(?A :: ?B :: ?C :: ?D :: nil) = _ |- rk(?A :: ?B :: ?D :: ?C :: nil) = _ => rewrite <-quadruple_equal_1;assumption
| H : rk(?A :: ?B :: ?C :: ?D :: nil) = _ |- rk(?A :: ?C :: ?A :: ?D :: nil) = _ => rewrite <-quadruple_equal_2;assumption
| H : rk(?A :: ?B :: ?C :: ?D :: nil) = _ |- rk(?A :: ?C :: ?D :: ?A :: nil) = _ => rewrite <-quadruple_equal_3;assumption
| H : rk(?A :: ?B :: ?C :: ?D :: nil) = _ |- rk(?A :: ?D :: ?A :: ?C :: nil) = _ => rewrite <-quadruple_equal_4;assumption
| H : rk(?A :: ?B :: ?C :: ?D :: nil) = _ |- rk(?A :: ?D :: ?C :: ?A :: nil) = _ => rewrite <-quadruple_equal_5;assumption
| H : rk(?A :: ?B :: ?C :: ?D :: nil) = _ |- rk(?B :: ?A :: ?C :: ?D :: nil) = _ => rewrite <-quadruple_equal_6;assumption
| H : rk(?A :: ?B :: ?C :: ?D :: nil) = _ |- rk(?B :: ?A :: ?D :: ?C :: nil) = _ => rewrite <-quadruple_equal_7;assumption
| H : rk(?A :: ?B :: ?C :: ?D :: nil) = _ |- rk(?B :: ?C :: ?A :: ?D :: nil) = _ => rewrite <-quadruple_equal_8;assumption
| H : rk(?A :: ?B :: ?C :: ?D :: nil) = _ |- rk(?B :: ?C :: ?D :: ?A :: nil) = _ => rewrite <-quadruple_equal_9;assumption
| H : rk(?A :: ?B :: ?C :: ?D :: nil) = _ |- rk(?B :: ?D :: ?A :: ?C :: nil) = _ => rewrite <-quadruple_equal_10;assumption
| H : rk(?A :: ?B :: ?C :: ?D :: nil) = _ |- rk(?B :: ?D :: ?C :: ?A :: nil) = _ => rewrite <-quadruple_equal_11;assumption
| H : rk(?A :: ?B :: ?C :: ?D :: nil) = _ |- rk(?C :: ?A :: ?B :: ?D :: nil) = _ => rewrite <-quadruple_equal_12;assumption
| H : rk(?A :: ?B :: ?C :: ?D :: nil) = _ |- rk(?C :: ?A :: ?D :: ?B :: nil) = _ => rewrite <-quadruple_equal_13;assumption
| H : rk(?A :: ?B :: ?C :: ?D :: nil) = _ |- rk(?C :: ?B :: ?A :: ?D :: nil) = _ => rewrite <-quadruple_equal_14;assumption
| H : rk(?A :: ?B :: ?C :: ?D :: nil) = _ |- rk(?C :: ?B :: ?D :: ?A :: nil) = _ => rewrite <-quadruple_equal_15;assumption
| H : rk(?A :: ?B :: ?C :: ?D :: nil) = _ |- rk(?C :: ?D :: ?A :: ?B :: nil) = _ => rewrite <-quadruple_equal_16;assumption
| H : rk(?A :: ?B :: ?C :: ?D :: nil) = _ |- rk(?C :: ?D :: ?B :: ?A :: nil) = _ => rewrite <-quadruple_equal_17;assumption
| H : rk(?A :: ?B :: ?C :: ?D :: nil) = _ |- rk(?D :: ?A :: ?B :: ?C :: nil) = _ => rewrite <-quadruple_equal_18;assumption
| H : rk(?A :: ?B :: ?C :: ?D :: nil) = _ |- rk(?D :: ?A :: ?C :: ?B :: nil) = _ => rewrite <-quadruple_equal_19;assumption
| H : rk(?A :: ?B :: ?C :: ?D :: nil) = _ |- rk(?D :: ?B :: ?A :: ?C :: nil) = _ => rewrite <-quadruple_equal_20;assumption
| H : rk(?A :: ?B :: ?C :: ?D :: nil) = _ |- rk(?D :: ?B :: ?C :: ?A :: nil) = _ => rewrite <-quadruple_equal_21;assumption
| H : rk(?A :: ?B :: ?C :: ?D :: nil) = _ |- rk(?D :: ?C :: ?A :: ?B :: nil) = _ => rewrite <-quadruple_equal_22;assumption
| H : rk(?A :: ?B :: ?C :: ?D :: nil) = _ |- rk(?D :: ?C :: ?B :: ?A :: nil) = _ => rewrite <-quadruple_equal_23;assumption
end.

Ltac rk_quadruple_bis A B C D:=
match goal with
| H0 : rk(A :: B :: C :: D :: nil) = _ |- _ => assumption
| H0 : rk(A :: B :: D :: C :: nil) = _ |- _ => rewrite <-quadruple_equal_1 in H0;assumption
| H0 : rk(A :: C :: B :: D :: nil) = _ |- _ => rewrite <-quadruple_equal_2 in H0;assumption
| H0 : rk(A :: C :: D :: B :: nil) = _ |- _ => rewrite <-quadruple_equal_3 in H0;assumption
| H0 : rk(A :: D :: B :: C :: nil) = _ |- _ => rewrite <-quadruple_equal_4 in H0;assumption
| H0 : rk(A :: D :: C :: B :: nil) = _ |- _ => rewrite <-quadruple_equal_5 in H0;assumption
| H0 : rk(B :: A :: C :: D :: nil) = _ |- _ => rewrite <-quadruple_equal_6 in H0;assumption
| H0 : rk(B :: A :: D :: C :: nil) = _ |- _ => rewrite <-quadruple_equal_7 in H0;assumption
| H0 : rk(B :: C :: A :: D :: nil) = _ |- _ => rewrite <-quadruple_equal_8 in H0;assumption
| H0 : rk(B :: C :: D :: A :: nil) = _ |- _ => rewrite <-quadruple_equal_9 in H0;assumption
| H0 : rk(B :: D :: A :: C :: nil) = _ |- _ => rewrite <-quadruple_equal_10 in H0;assumption
| H0 : rk(B :: D :: C :: A :: nil) = _ |- _ => rewrite <-quadruple_equal_11 in H0;assumption
| H0 : rk(C :: A :: B :: D :: nil) = _ |- _ => rewrite <-quadruple_equal_12 in H0;assumption
| H0 : rk(C :: A :: D :: B :: nil) = _ |- _ => rewrite <-quadruple_equal_13 in H0;assumption
| H0 : rk(C :: B :: A :: D :: nil) = _ |- _ => rewrite <-quadruple_equal_14 in H0;assumption
| H0 : rk(C :: B :: D :: A :: nil) = _ |- _ => rewrite <-quadruple_equal_15 in H0;assumption
| H0 : rk(C :: D :: A :: B :: nil) = _ |- _ => rewrite <-quadruple_equal_16 in H0;assumption
| H0 : rk(C :: D :: B :: A :: nil) = _ |- _ => rewrite <-quadruple_equal_17 in H0;assumption
| H0 : rk(D :: A :: B :: C :: nil) = _ |- _ => rewrite <-quadruple_equal_18 in H0;assumption
| H0 : rk(D :: A :: C :: B :: nil) = _ |- _ => rewrite <-quadruple_equal_19 in H0;assumption
| H0 : rk(D :: B :: A :: C :: nil) = _ |- _ => rewrite <-quadruple_equal_20 in H0;assumption
| H0 : rk(D :: B :: C :: A :: nil) = _ |- _ => rewrite <-quadruple_equal_21 in H0;assumption
| H0 : rk(D :: C :: A :: B :: nil) = _ |- _ => rewrite <-quadruple_equal_22 in H0;assumption
| H0 : rk(D :: C :: B :: A :: nil) = _ |- _ => rewrite <-quadruple_equal_23 in H0;assumption
end.

Ltac rk_quadruple_bis_bis :=
match goal with
| H : _ |- rk(?A :: ?B :: ?C :: ?D :: nil) = 2 => solve[rk_quadruple_bis A B C D]
end.

Ltac rk_quadruple_2_3_bis HH0 A B C D:=
match goal with
| H0 : rk(A :: B :: C :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 A B C D H0));rewrite HH in HH0;inversion HH0
| H0 : rk(A :: B :: D :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 A B D C H0));rewrite <-quadruple_equal_1 in HH;rewrite HH in HH0;inversion HH0
| H0 : rk(A :: C :: B :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 A C B D H0));rewrite <-quadruple_equal_2 in HH;rewrite HH in HH0;inversion HH0
| H0 : rk(A :: C :: D :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 A C D B H0));rewrite <-quadruple_equal_3 in HH;rewrite HH in HH0;inversion HH0
| H0 : rk(A :: D :: B :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 A D B C H0));rewrite <-quadruple_equal_4 in HH;rewrite HH in HH0;inversion HH0
| H0 : rk(A :: D :: C :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 A D C B H0));rewrite <-quadruple_equal_5 in HH;rewrite HH in HH0;inversion HH0
| H0 : rk(B :: A :: C :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 B A C D H0));rewrite <-quadruple_equal_6 in HH;rewrite HH in HH0;inversion HH0
| H0 : rk(B :: A :: D :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 B A D C H0));rewrite <-quadruple_equal_7 in HH;rewrite HH in HH0;inversion HH0
| H0 : rk(B :: C :: A :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 B C A D H0));rewrite <-quadruple_equal_8 in HH;rewrite HH in HH0;inversion HH0
| H0 : rk(B :: C :: D :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 B C D A H0));rewrite <-quadruple_equal_9 in HH;rewrite HH in HH0;inversion HH0
| H0 : rk(B :: D :: A :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 B D A C H0));rewrite <-quadruple_equal_10 in HH;rewrite HH in HH0;inversion HH0
| H0 : rk(B :: D :: C :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 B D C A H0));rewrite <-quadruple_equal_11 in HH;rewrite HH in HH0;inversion HH0
| H0 : rk(C :: A :: B :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 C A B D H0));rewrite <-quadruple_equal_12 in HH;rewrite HH in HH0;inversion HH0
| H0 : rk(C :: A :: D :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 C A D B H0));rewrite <-quadruple_equal_13 in HH;rewrite HH in HH0;inversion HH0
| H0 : rk(C :: B :: A :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 C B A D H0));rewrite <-quadruple_equal_14 in HH;rewrite HH in HH0;inversion HH0
| H0 : rk(C :: B :: D :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 C B D A H0));rewrite <-quadruple_equal_15 in HH;rewrite HH in HH0;inversion HH0
| H0 : rk(C :: D :: A :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 C D A B H0));rewrite <-quadruple_equal_16 in HH;rewrite HH in HH0;inversion HH0
| H0 : rk(C :: D :: B :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 C D B A H0));rewrite <-quadruple_equal_17 in HH;rewrite HH in HH0;inversion HH0
| H0 : rk(D :: A :: B :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 D A B C H0));rewrite <-quadruple_equal_18 in HH;rewrite HH in HH0;inversion HH0
| H0 : rk(D :: A :: C :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 D A C B H0));rewrite <-quadruple_equal_19 in HH;rewrite HH in HH0;inversion HH0
| H0 : rk(D :: B :: A :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 D B A C H0));rewrite <-quadruple_equal_20 in HH;rewrite HH in HH0;inversion HH0
| H0 : rk(D :: B :: C :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 D B C A H0));rewrite <-quadruple_equal_21 in HH;rewrite HH in HH0;inversion HH0
| H0 : rk(D :: C :: A :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 D C A B H0));rewrite <-quadruple_equal_22 in HH;rewrite HH in HH0;inversion HH0
| H0 : rk(D :: C :: B :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 D C B A H0));rewrite <-quadruple_equal_23 in HH;rewrite HH in HH0;inversion HH0
end.

Ltac rk_quadruple_2_3_bis_bis :=
match goal with
| H : rk(?A :: ?B :: ?C :: ?D :: nil) = 2 |- _ => solve[rk_quadruple_2_3_bis H A B C D]
end.

Ltac rk_quadruple_to_triple_bis A B C D:=
match goal with
| H0 : rk(A :: B :: C :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 A B C D H0));assumption
| H0 : rk(A :: B :: D :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 A B D C H0));rewrite <-quadruple_equal_1 in HH;assumption
| H0 : rk(A :: C :: B :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 A C B D H0));rewrite <-quadruple_equal_2 in HH;assumption
| H0 : rk(A :: C :: D :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 A C D B H0));rewrite <-quadruple_equal_3 in HH;assumption
| H0 : rk(A :: D :: B :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 A D B C H0));rewrite <-quadruple_equal_4 in HH;assumption
| H0 : rk(A :: D :: C :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 A D C B H0));rewrite <-quadruple_equal_5 in HH;assumption
| H0 : rk(B :: A :: C :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 B A C D H0));rewrite <-quadruple_equal_6 in HH;assumption
| H0 : rk(B :: A :: D :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 B A D C H0));rewrite <-quadruple_equal_7 in HH;assumption
| H0 : rk(B :: C :: A :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 B C A D H0));rewrite <-quadruple_equal_8 in HH;assumption
| H0 : rk(B :: C :: D :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 B C D A H0));rewrite <-quadruple_equal_9 in HH;assumption
| H0 : rk(B :: D :: A :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 B D A C H0));rewrite <-quadruple_equal_10 in HH;assumption
| H0 : rk(B :: D :: C :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 B D C A H0));rewrite <-quadruple_equal_11 in HH;assumption
| H0 : rk(C :: A :: B :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 C A B D H0));rewrite <-quadruple_equal_12 in HH;assumption
| H0 : rk(C :: A :: D :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 C A D B H0));rewrite <-quadruple_equal_13 in HH;assumption
| H0 : rk(C :: B :: A :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 C B A D H0));rewrite <-quadruple_equal_14 in HH;assumption
| H0 : rk(C :: B :: D :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 C B D A H0));rewrite <-quadruple_equal_15 in HH;assumption
| H0 : rk(C :: D :: A :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 C D A B H0));rewrite <-quadruple_equal_16 in HH;assumption
| H0 : rk(C :: D :: B :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 C D B A H0));rewrite <-quadruple_equal_17 in HH;assumption
| H0 : rk(D :: A :: B :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 D A B C H0));rewrite <-quadruple_equal_18 in HH;assumption
| H0 : rk(D :: A :: C :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 D A C B H0));rewrite <-quadruple_equal_19 in HH;assumption
| H0 : rk(D :: B :: A :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 D B A C H0));rewrite <-quadruple_equal_20 in HH;assumption
| H0 : rk(D :: B :: C :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 D B C A H0));rewrite <-quadruple_equal_21 in HH;assumption
| H0 : rk(D :: C :: A :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 D C A B H0));rewrite <-quadruple_equal_22 in HH;assumption
| H0 : rk(D :: C :: B :: nil) = 3 |- _ => let HH := fresh in (assert(HH := triple_rk3_to_quadruple_rk3 D C B A H0));rewrite <-quadruple_equal_23 in HH;assumption
end.

Ltac rk_quadruple_to_triple_bis_bis:=
match goal with
| H : _ |- rk(?A :: ?B :: ?C :: ?D :: nil) = 3 => solve[rk_quadruple_to_triple_bis A B C D]
end.

Ltac rk_triple_to_quadruple_bis A B C :=
match goal with
| H0 : rk(A :: B :: C :: ?D :: nil) = 2 |- _ => let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);assumption);assumption
| H0 : rk(A :: B :: ?D :: C :: nil) = 2 |- _ => rewrite <-quadruple_equal_1 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);assumption);assumption
| H0 : rk(A :: C :: B :: ?D :: nil) = 2 |- _ => rewrite <-quadruple_equal_2 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);assumption);assumption
| H0 : rk(A :: C :: ?D :: B :: nil) = 2 |- _ => rewrite <-quadruple_equal_3 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);assumption);assumption
| H0 : rk(A :: ?D :: B :: C :: nil) = 2 |- _ => rewrite <-quadruple_equal_4 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);assumption);assumption
| H0 : rk(A :: ?D :: C :: B :: nil) = 2 |- _ => rewrite <-quadruple_equal_5 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);assumption);assumption
| H0 : rk(B :: A :: C :: ?D :: nil) = 2 |- _ => rewrite <-quadruple_equal_6 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);assumption);assumption
| H0 : rk(B :: A :: ?D :: C :: nil) = 2 |- _ => rewrite <-quadruple_equal_7 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);assumption);assumption
| H0 : rk(B :: C :: A :: ?D :: nil) = 2 |- _ => rewrite <-quadruple_equal_8 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);assumption);assumption
| H0 : rk(B :: C :: ?D :: A :: nil) = 2 |- _ => rewrite <-quadruple_equal_9 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);assumption);assumption
| H0 : rk(B :: ?D :: A :: C :: nil) = 2 |- _ => rewrite <-quadruple_equal_10 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);assumption);assumption
| H0 : rk(B :: ?D :: C :: A :: nil) = 2 |- _ => rewrite <-quadruple_equal_11 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);assumption);assumption
| H0 : rk(C :: A :: B :: ?D :: nil) = 2 |- _ => rewrite <-quadruple_equal_12 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);assumption);assumption
| H0 : rk(C :: A :: ?D :: B :: nil) = 2 |- _ => rewrite <-quadruple_equal_13 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);assumption);assumption
| H0 : rk(C :: B :: A :: ?D :: nil) = 2 |- _ => rewrite <-quadruple_equal_14 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);assumption);assumption
| H0 : rk(C :: B :: ?D :: A :: nil) = 2 |- _ => rewrite <-quadruple_equal_15 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);assumption);assumption
| H0 : rk(C :: ?D :: A :: B :: nil) = 2 |- _ => rewrite <-quadruple_equal_16 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);assumption);assumption
| H0 : rk(C :: ?D :: B :: A :: nil) = 2 |- _ => rewrite <-quadruple_equal_17 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);assumption);assumption
| H0 : rk(?D :: A :: B :: C :: nil) = 2 |- _ => rewrite <-quadruple_equal_18 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);assumption);assumption
| H0 : rk(?D :: A :: C :: B :: nil) = 2 |- _ => rewrite <-quadruple_equal_19 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);assumption);assumption
| H0 : rk(?D :: B :: A :: C :: nil) = 2 |- _ => rewrite <-quadruple_equal_20 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);assumption);assumption
| H0 : rk(?D :: B :: C :: A :: nil) = 2 |- _ => rewrite <-quadruple_equal_21 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);assumption);assumption
| H0 : rk(?D :: C :: A :: B :: nil) = 2 |- _ => rewrite <-quadruple_equal_22 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);assumption);assumption
| H0 : rk(?D :: C :: B :: A :: nil) = 2 |- _ => rewrite <-quadruple_equal_23 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);assumption);assumption
end.

Ltac rk_triple_to_quadruple_bis_bis :=
match goal with
| H : _ |- rk(?A :: ?B :: ?C :: nil) = 2 => solve[rk_triple_to_quadruple_bis A B C]
end.


(*****************************************************************************)

Lemma eq_neg_reverse :
forall A B : Point, ~ A = B -> ~ B = A /\ ~ A = B.
Proof.
intros.
intuition.
Qed.

Ltac eq_duplicate :=
repeat match goal with
| H : ~ ?X = ?Y  |- _ => let HH := fresh in (assert(HH := eq_neg_reverse X Y H));clear H
end.

Lemma triple_rk2_1 : forall P R, P <> R -> rk(P :: P :: R :: nil) = 2.
Proof.
intros.
assert(HH : equivlist (P :: P :: R :: nil) (P :: R :: nil));[my_inO|];rewrite HH;apply rk_couple;intuition.
Qed.

Lemma triple_rk2_2 : forall P R, P <> R -> rk(P :: R :: P :: nil) = 2.
Proof.
intros.
assert(HH : equivlist (P :: R :: P :: nil) (P :: R :: nil));[my_inO|];rewrite HH;apply rk_couple;intuition.
Qed.

Lemma triple_rk2_3 : forall P R, P <> R -> rk(R :: P :: P :: nil) = 2.
Proof.
intros.
assert(HH : equivlist (R :: P :: P :: nil) (P :: R :: nil));[my_inO|];rewrite HH;apply rk_couple;intuition.
Qed.

Lemma col_degen_1 : forall P R, rk(P :: P :: R :: nil) = 3 -> False.
Proof.
intros.
assert(HH : equivlist (P :: R :: nil) (P :: P :: R :: nil));[my_inO|].
rewrite <-HH in H.
assert(HH0 := rk_couple_2 P R).
omega.
Qed.

Lemma col_degen_2 : forall P R, rk(P :: R :: P :: nil) = 3 -> False.
Proof.
intros.
assert(HH : equivlist (P :: R :: nil) (P :: R :: P :: nil));[my_inO|].
rewrite <-HH in H.
assert(HH0 := rk_couple_2 P R).
omega.
Qed.

Lemma col_degen_3 : forall P R, rk(R :: P :: P :: nil) = 3 -> False.
Proof.
intros.
assert(HH : equivlist (P :: R :: nil) (R :: P :: P :: nil));[my_inO|].
rewrite <-HH in H.
assert(HH0 := rk_couple_2 P R).
omega.
Qed.

Lemma quadruple_permut_1 : forall P A B C, rk(P :: A :: B :: C :: nil) = rk(P :: A :: C :: B ::nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quadruple_permut_2 : forall P A B C, rk(P :: A :: B :: C :: nil) = rk(P :: B :: A :: C :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quadruple_permut_3 : forall P A B C, rk(P :: A :: B :: C :: nil) = rk(P :: B :: C :: A :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quadruple_permut_4 : forall P A B C, rk(P :: A :: B :: C :: nil) = rk(P :: C :: A :: B :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quadruple_permut_5 : forall P A B C, rk(P :: A :: B :: C :: nil) = rk(P :: C :: B :: A :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quintuple_permut_1 : forall P A B C D, rk(P :: A :: B :: C :: D :: nil) = rk(P :: A :: B :: D :: C :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quintuple_permut_2 : forall P A B C D, rk(P :: A :: B :: C :: D :: nil) = rk(P :: A :: C :: B :: D :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quintuple_permut_3 : forall P A B C D, rk(P :: A :: B :: C :: D :: nil) = rk(P :: A :: C :: D :: B :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quintuple_permut_4 : forall P A B C D, rk(P :: A :: B :: C :: D :: nil) = rk(P :: A :: D :: B :: C :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quintuple_permut_5 : forall P A B C D, rk(P :: A :: B :: C :: D :: nil) = rk(P :: A :: D :: C :: B :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quintuple_permut_6 : forall P A B C D, rk(P :: A :: B :: C :: D :: nil) = rk(P :: B :: A :: C :: D :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quintuple_permut_7 : forall P A B C D, rk(P :: A :: B :: C :: D :: nil) = rk(P :: B :: A :: D :: C :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quintuple_permut_8 : forall P A B C D, rk(P :: A :: B :: C :: D :: nil) = rk(P :: B :: C :: A :: D :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quintuple_permut_9 : forall P A B C D, rk(P :: A :: B :: C :: D :: nil) = rk(P :: B :: C :: D :: A :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quintuple_permut_10 : forall P A B C D, rk(P :: A :: B :: C :: D :: nil) = rk(P :: B :: D :: A :: C :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quintuple_permut_11 : forall P A B C D, rk(P :: A :: B :: C :: D :: nil) = rk(P :: B :: D :: C :: A :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quintuple_permut_12 : forall P A B C D, rk(P :: A :: B :: C :: D :: nil) = rk(P :: C :: A :: B :: D :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quintuple_permut_13 : forall P A B C D, rk(P :: A :: B :: C :: D :: nil) = rk(P :: C :: A :: D :: B :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quintuple_permut_14 : forall P A B C D, rk(P :: A :: B :: C :: D :: nil) = rk(P :: C :: B :: A :: D :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quintuple_permut_15 : forall P A B C D, rk(P :: A :: B :: C :: D :: nil) = rk(P :: C :: B :: D :: A :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quintuple_permut_16 : forall P A B C D, rk(P :: A :: B :: C :: D :: nil) = rk(P :: C :: D :: A :: B :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quintuple_permut_17 : forall P A B C D, rk(P :: A :: B :: C :: D :: nil) = rk(P :: C :: D :: B :: A :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quintuple_permut_18 : forall P A B C D, rk(P :: A :: B :: C :: D :: nil) = rk(P :: D :: A :: B :: C :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quintuple_permut_19 : forall P A B C D, rk(P :: A :: B :: C :: D :: nil) = rk(P :: D :: A :: C :: B :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quintuple_permut_20 : forall P A B C D, rk(P :: A :: B :: C :: D :: nil) = rk(P :: D :: B :: A :: C :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quintuple_permut_21 : forall P A B C D, rk(P :: A :: B :: C :: D :: nil) = rk(P :: D :: B :: C :: A :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quintuple_permut_22 : forall P A B C D, rk(P :: A :: B :: C :: D :: nil) = rk(P :: D :: C :: A :: B :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.

Lemma quintuple_permut_23 : forall P A B C D, rk(P :: A :: B :: C :: D :: nil) = rk(P :: D :: C :: B :: A :: nil).
Proof.
intros;apply rk_morph;my_inO.
Qed.