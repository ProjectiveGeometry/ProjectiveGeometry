
(** rk-singleton : The rank of a point is always greater than one  **) 
Lemma rk_singleton_ge : forall P, rk (P :: nil) >= 1.
Proof.
intros.
assert(HH := rk_points);use HH.
(*destruct (is_only_13_pts P) as [[[[[[[[[[[[HA | HB] | HC] | HD] | HE ] | HF ] | HG] | HH] |  HI ] | HJ] | HK] | HL] | HM]; subst.*)

case_clear_2 P ;intuition.
Qed.

Lemma rk_singleton_1 : forall A, rk(A :: nil) <= 1.
Proof.
intros.
apply matroid1_b_useful.
intuition.
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

Lemma rk_couple_2 : forall P Q, rk(P :: Q :: nil) <= 2.
Proof.
intros.
apply matroid1_b_useful.
intuition.
Qed.

Lemma rk_couple : forall P Q : Point,~ P = Q -> rk(P :: Q :: nil) = 2.
Proof.
intros.
assert(HH := rk_couple_2 P Q).
assert(HH0 := rk_couple_ge P Q H).
omega.
Qed.

Lemma couple_rk1 : forall P Q, rk(P :: Q :: nil) = 2 -> ~ P = Q.
Proof.
intros.
intro.
rewrite H0 in H.
assert(HH : equivlist (Q :: Q :: nil) (Q :: nil));[my_inO|].
rewrite HH in H.
assert(HH0 := rk_singleton_1 Q).
omega.
Qed.

Lemma quadruple_rk2_to_triple_rk2 : forall P Q R S : Point,
rk (P :: Q :: nil) = 2 -> rk(P :: Q ::  R :: S :: nil) = 2 -> rk(P :: Q :: R :: nil) = 2.
Proof.
intros.
assert(HH : incl (P :: Q :: R :: nil) (P :: Q :: R :: S :: nil));[my_inO|].
assert(HH0 := matroid2 (P :: Q :: R :: nil) (P :: Q :: R :: S :: nil) HH).
assert(HH1bis := couple_rk1 P Q H).
assert(HH1 := rk_couple P Q HH1bis).
assert(HH2 : incl (P :: Q :: nil) (P :: Q :: R :: nil));[my_inO|].
assert(HH3 := matroid2 (P :: Q :: nil) (P :: Q :: R :: nil) HH2).
omega.
Qed.

Ltac rk_triple_to_quadruple_bis :=
match goal with
| H0 : rk(?A :: ?B :: ?C :: ?D :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple_bis_bis |assumption]);assumption
| H0 : rk(?A :: ?B :: ?D :: ?C :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_1 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple_bis_bis|assumption]);assumption
| H0 : rk(?A :: ?C :: ?B :: ?D :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_2 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple_bis_bis|assumption]);assumption
| H0 : rk(?A :: ?C :: ?D :: ?B :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_3 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple_bis_bis|assumption]);assumption
| H0 : rk(?A :: ?D :: ?B :: ?C :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_4 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple_bis_bis|assumption]);assumption
| H0 : rk(?A :: ?D :: ?C :: ?B :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_5 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple_bis_bis|assumption]);assumption
| H0 : rk(?B :: ?A :: ?C :: ?D :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_6 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple_bis_bis|assumption]);assumption
| H0 : rk(?B :: ?A :: ?D :: ?C :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_7 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple_bis_bis|assumption]);assumption
| H0 : rk(?B :: ?C :: ?A :: ?D :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_8 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple_bis_bis|assumption]);assumption
| H0 : rk(?B :: ?C :: ?D :: ?A :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_9 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple_bis_bis|assumption]);assumption
| H0 : rk(?B :: ?D :: ?A :: ?C :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_10 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple_bis_bis|assumption]);assumption
| H0 : rk(?B :: ?D :: ?C :: ?A :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_11 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple_bis_bis|assumption]);assumption
| H0 : rk(?C :: ?A :: ?B :: ?D :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_12 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple_bis_bis|assumption]);assumption
| H0 : rk(?C :: ?A :: ?D :: ?B :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_13 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple_bis_bis|assumption]);assumption
| H0 : rk(?C :: ?B :: ?A :: ?D :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_14 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple_bis_bis|assumption]);assumption
| H0 : rk(?C :: ?B :: ?D :: ?A :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_15 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple_bis_bis|assumption]);assumption
| H0 : rk(?C :: ?D :: ?A :: ?B :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_16 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple_bis_bis|assumption]);assumption
| H0 : rk(?C :: ?D :: ?B :: ?A :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_17 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple_bis_bis|assumption]);assumption
| H0 : rk(?D :: ?A :: ?B :: ?C :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_18 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple_bis_bis|assumption]);assumption
| H0 : rk(?D :: ?A :: ?C :: ?B :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_19 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple_bis_bis|assumption]);assumption
| H0 : rk(?D :: ?B :: ?A :: ?C :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_20 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple_bis_bis|assumption]);assumption
| H0 : rk(?D :: ?B :: ?C :: ?A :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_21 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple_bis_bis|assumption]);assumption
| H0 : rk(?D :: ?C :: ?A :: ?B :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_22 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple_bis_bis|assumption]);assumption
| H0 : rk(?D :: ?C :: ?B :: ?A :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_23 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple_bis_bis|assumption]);assumption
end.
(*
Ltac rk_triple_to_quadruple_bis_bis :=
match goal with
| H : _ |- rk(?A :: ?B :: ?C :: nil) = 2 => solve[rk_triple_to_quadruple_bis A B C]
end.
*)
Lemma triple_rk2_1 : forall P R, rk(P :: R :: nil) = 2 -> rk(P :: P :: R :: nil) = 2.
Proof.
intros.
assert(HH : equivlist (P :: P :: R :: nil) (P :: R :: nil));[my_inO|];rewrite HH;intuition.
Qed.

Lemma triple_rk2_2 : forall P R, rk(P :: R :: nil) = 2 -> rk(P :: R :: P :: nil) = 2.
Proof.
intros.
assert(HH : equivlist (P :: R :: P :: nil) (P :: R :: nil));[my_inO|];rewrite HH;intuition.
Qed.

Lemma triple_rk2_3 : forall P R, rk(P :: R :: nil) = 2 -> rk(R :: P :: P :: nil) = 2.
Proof.
intros.
assert(HH : equivlist (R :: P :: P :: nil) (P :: R :: nil));[my_inO|];rewrite HH;intuition.
Qed.

Ltac degens_rk2 :=
match goal with
| H : _ |- rk(?P :: ?P :: ?R :: nil) = 2 => (*try*) solve[apply triple_rk2_1;rk_couple_triple_bis_bis]
| H : _ |- rk(?P :: ?R :: ?P :: nil) = 2 => (*try*) solve[apply triple_rk2_2;rk_couple_triple_bis_bis]
| H : _ |- rk(?R :: ?P :: ?P :: nil) = 2 => (*try*) solve[apply triple_rk2_3;rk_couple_triple_bis_bis]
end.

Ltac degens_rk2' :=
  solve[ first [apply triple_rk2_1 | apply triple_rk2_2 | apply triple_rk2_3];rk_couple_triple_bis_bis].

Ltac solve_ex_1 L := solve [exists L; repeat split;solve [ assumption |  degens_rk2' | rk_couple_triple_bis_bis | rk_triple_to_quadruple_bis]].

(*Ltac solve_ex_p_1 := solve_ex_p solve_ex_1.  first [
        solve_ex_1 A
     |  solve_ex_1 B
     |  solve_ex_1 C
     |  solve_ex_1 D
     |  solve_ex_1 E
     |  solve_ex_1 F
     |  solve_ex_1 G
     |  solve_ex_1 H
     |  solve_ex_1 I
     |  solve_ex_1 J
     |  solve_ex_1 K
     |  solve_ex_1 L
     |  solve_ex_1 M
 ].*)
Ltac solve_ex_p_1 := first [
 solve_ex_1 P0 |  solve_ex_1 P1 |  solve_ex_1 P2 |  solve_ex_1 P3 |  solve_ex_1 P4 |  solve_ex_1 P5 |  solve_ex_1 P6 |  solve_ex_1 P7 |  solve_ex_1 P8 |  solve_ex_1 P9 |  solve_ex_1 P10 |  solve_ex_1 P11 |  solve_ex_1 P12 |  solve_ex_1 P13 |  solve_ex_1 P14 |  solve_ex_1 P15 |  solve_ex_1 P16 |  solve_ex_1 P17 |  solve_ex_1 P18 |  solve_ex_1 P19 |  solve_ex_1 P20 |  solve_ex_1 P21 |  solve_ex_1 P22 |  solve_ex_1 P23 |  solve_ex_1 P24 |  solve_ex_1 P25 |  solve_ex_1 P26 |  solve_ex_1 P27 |  solve_ex_1 P28 |  solve_ex_1 P29 |  solve_ex_1 P30 ].


                                                                       
Ltac rk_three_points_simplify P Q :=
match goal with
| H0 : rk(P :: Q :: ?R :: ?X :: nil) = 2 |- _ => let HH := fresh in assert(HH : rk(P :: Q :: R :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 P Q R X);solve [ assumption|rk_couple_triple_bis_bis]);solve_ex_1 R
| H0 : rk(P :: ?R :: Q :: ?X :: nil) = 2 |- _ => rewrite <-quadruple_equal_2 in H0;let HH := fresh in assert(HH : rk(P :: Q :: R :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 P Q R X);solve [assumption|rk_couple_triple_bis_bis]);solve_ex_1 R
| H0 : rk(P :: ?R :: ?X :: Q :: nil) = 2 |- _ => rewrite <-quadruple_equal_3 in H0;let HH := fresh in assert(HH : rk(P :: Q :: R :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 P Q R X);solve [assumption|rk_couple_triple_bis_bis]);solve_ex_1 R
| H0 : rk(Q :: P :: ?R :: ?X :: nil) = 2 |- _ => rewrite <-quadruple_equal_6 in H0;let HH := fresh in assert(HH : rk(P :: Q :: R :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 P Q R X);solve [assumption|rk_couple_triple_bis_bis]);solve_ex_1 R
| H0 : rk(Q :: ?R :: P :: ?X :: nil) = 2 |- _ => rewrite <-quadruple_equal_8 in H0;let HH := fresh in assert(HH : rk(P :: Q :: R :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 P Q R X);solve [assumption|rk_couple_triple_bis_bis]);solve_ex_1 R
| H0 : rk(Q :: ?R :: ?X :: P :: nil) = 2 |- _ => rewrite <-quadruple_equal_9 in H0;let HH := fresh in assert(HH : rk(P :: Q :: R :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 P Q R X);solve [assumption|rk_couple_triple_bis_bis]);solve_ex_1 R
| H0 : rk(?R :: P :: Q :: ?X :: nil) = 2 |- _ => rewrite <-quadruple_equal_12 in H0;let HH := fresh in assert(HH : rk(P :: Q :: R :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 P Q R X);solve [assumption|rk_couple_triple_bis_bis]);solve_ex_1 R
| H0 : rk(?R :: P :: ?X :: Q :: nil) = 2 |- _ => rewrite <-quadruple_equal_13 in H0;let HH := fresh in assert(HH : rk(P :: Q :: R :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 P Q R X);solve [assumption|rk_couple_triple_bis_bis]);solve_ex_1 R
| H0 : rk(?R :: Q :: P :: ?X :: nil) = 2 |- _ => rewrite <-quadruple_equal_14 in H0;let HH := fresh in assert(HH : rk(P :: Q :: R :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 P Q R X);solve [assumption|rk_couple_triple_bis_bis]);solve_ex_1 R
| H0 : rk(?R :: Q :: ?X :: P :: nil) = 2 |- _ => rewrite <-quadruple_equal_15 in H0;let HH := fresh in assert(HH : rk(P :: Q :: R :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 P Q R X);solve [assumption|rk_couple_triple_bis_bis]);solve_ex_1 R
| H0 : rk(?R :: ?X :: P :: Q :: nil) = 2 |- _ => rewrite <-quadruple_equal_16 in H0;let HH := fresh in assert(HH : rk(P :: Q :: R :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 P Q R X);solve [assumption|rk_couple_triple_bis_bis]);solve_ex_1 R
| H0 : rk(?R :: ?X :: Q :: P :: nil) = 2 |- _ => rewrite <-quadruple_equal_17 in H0;let HH := fresh in assert(HH : rk(P :: Q :: R :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 P Q R X);solve [assumption|rk_couple_triple_bis_bis]);solve_ex_1 R
end.

Ltac rk_three_points_simplify_bis :=
match goal with
| H : _ |- exists R, rk (?P :: ?P :: _ :: nil) = 2 /\ _ /\ _ => solve_ex_p_1
| H : _ |- exists R, rk (?P :: ?Q :: R :: nil) = 2 /\ _ /\ _ => rk_three_points_simplify P Q
end.

Ltac my_inA :=
  intuition;unfold incl in *;unfold equivlist in *; simpl;
  repeat match goal with
  |[H : _ |- _] => progress intros
  |[H : _ |- _] => progress intro
  |[H : _ |- _] => progress intuition
  |[H : _ |- _] => split;intuition
  |[H : In _ (?P ::  _ ) |- _] => inversion H;clear H
  |[H : _ = _ |- _] => rewrite <-H
  |[H : In _ nil |- _] => inversion H
         end.

Lemma all_distinct_scheme : forall P Q T1 T2 T3 T4,
    rk (P :: Q :: T1 :: T2 :: T3 :: T4::nil)=2 -> 
    rk (P::Q::nil)=2 -> rk (P::T1::nil)=2 -> rk (P::T2::nil)=2 -> rk (P::T3::nil)=2 -> rk (P::T4::nil)=2 ->
    rk (Q::T1::nil)=2 -> rk (Q::T2::nil)=2 -> rk (Q::T3::nil)=2 -> rk (Q::T4::nil)=2 ->
    rk (T1::T2::nil)=2 -> rk (T1::T3::nil)=2 -> rk (T1::T4::nil)=2 -> 
    rk (T2::T3::nil)=2 -> rk (T2::T4::nil)=2 -> 
    rk (T3::T4::nil)=2 ->
    rk (P::Q::T1::nil)=2/\ rk (Q :: T1 :: nil) = 2 /\ rk (P :: T1 :: nil) = 2.
Proof.
  intros.
  split.
  assert (rk (P :: Q :: T1 :: nil) <= 2 /\ 2 <= rk (P :: Q :: T1 :: nil)).
  
  split.
  rewrite <- H.
  apply matroid2.
  my_inA.
  rewrite <- H0.
  apply matroid2.
  my_inA.
  omega.
  split; assumption.
Qed.

Lemma rk_sym12 : forall A B U, rk(A::B::U)=rk(B::A::U).
Proof.
  intros; apply rk_compat; unfold equivlist; split; my_inA.
Qed.

Lemma rk_sym13 : forall A B C U, rk(A::B::C::U)=rk(C::B::A::U).
Proof.
  intros; apply rk_compat; unfold equivlist; split; my_inA.
Qed.

Lemma rk_sym14 : forall A B C D U, rk(A::B::C::D::U)=rk(D::B::C::A::U).
Proof.
  intros; apply rk_compat; unfold equivlist; split; my_inA.
Qed.

Lemma rk_sym15 : forall A B C D E U, rk(A::B::C::D::E::U)=rk(E::B::C::D::A::U).
Proof.
  intros; apply rk_compat; unfold equivlist; split; my_inA.
Qed.

Lemma rk_sym16 : forall A B C D E F U, rk(A::B::C::D::E::F::U)=rk(F::B::C::D::E::A::U).
Proof.
  intros; apply rk_compat; unfold equivlist; split; my_inA.
Qed.

Lemma rk_sym23 : forall A B C U, rk(A::B::C::U)=rk(A::C::B::U).
Proof.
  intros; apply rk_compat; unfold equivlist; split; my_inA.
Qed.

Lemma rk_sym24 : forall A B C D U, rk(A::B::C::D::U)=rk(A::D::C::B::U).
Proof.
  intros; apply rk_compat; unfold equivlist; split; my_inA.
Qed.

Lemma rk_sym25 : forall A B C D E U, rk(A::B::C::D::E::U)=rk(A::E::C::D::B::U).
Proof.
  intros; apply rk_compat; unfold equivlist; split; my_inA.
Qed.

Lemma rk_sym26 : forall A B C D E F U, rk(A::B::C::D::E::F::U)=rk(A::F::C::D::E::B::U).
Proof.
  intros; apply rk_compat; unfold equivlist; split; my_inA.
Qed.

Lemma rk_sym34 : forall A B C D U, rk(A::B::C::D::U)=rk(A::B::D::C::U).
Proof.
  intros; apply rk_compat; unfold equivlist; split; my_inA.
Qed.

Lemma rk_sym35 : forall A B C D E U, rk(A::B::C::D::E::U)=rk(A::B::E::D::C::U).
Proof.
  intros; apply rk_compat; unfold equivlist; split; my_inA.
Qed.

Lemma rk_sym36 : forall A B C D E F U, rk(A::B::C::D::E::F::U)=rk(A::B::F::D::E::C::U).
Proof.
  intros; apply rk_compat; unfold equivlist; split; my_inA.
Qed.

Lemma rk_sym45 : forall A B C D E U, rk(A::B::C::D::E::U)=rk(A::B::C::E::D::U).
Proof.
  intros; apply rk_compat; unfold equivlist; split; my_inA.
Qed.

Lemma rk_sym46 : forall A B C D E F U, rk(A::B::C::D::E::F::U)=rk(A::B::C::F::E::D::U).
Proof.
  intros; apply rk_compat; unfold equivlist; split; my_inA.
Qed.

Lemma rk_sym56 : forall A B C D E F U, rk(A::B::C::D::E::F::U)=rk(A::B::C::D::F::E::U).
Proof.
  intros; apply rk_compat; unfold equivlist; split; my_inA.
Qed.

Lemma rk_13_12 : forall A B C U, rk(A::B::C::U) = rk (A::C::B::U).
Proof.
  intros; apply rk_compat; unfold equivlist; split; my_inA.
Qed.

Lemma rk_14_12 : forall A B C D U, rk(A::B::C::D::U) = rk (A::D::C::B::U).
Proof.
  intros; apply rk_compat; unfold equivlist; split; my_inA.
Qed.


Lemma rk_15_12 : forall A B C D E U, rk(A::B::C::D::E::U) = rk (A::E::C::D::B::U).
Proof.
  intros; apply rk_compat; unfold equivlist; split; my_inA.
Qed.


Lemma rk_16_12 : forall A B C D E F U, rk(A::B::C::D::E::F::U) = rk (A::F::C::D::E::B::U).
Proof.
Proof.
  intros; apply rk_compat; unfold equivlist; split; my_inA.
Qed.

Lemma rk_23_12 : forall A B C U, rk(A::B::C::U)= rk(B::C::A::U).
Proof.
Proof.
  intros; apply rk_compat; unfold equivlist; split; my_inA.
Qed.


Lemma rk_24_12 : forall A B C D U, rk(A::B::C::D::U)= rk(B::D::A::C::U).
Proof.
Proof.
  intros; apply rk_compat; unfold equivlist; split; my_inA.
Qed.

Lemma rk_25_12 : forall A B C D E U, rk(A::B::C::D::E::U)= rk(B::E::A::C::D:: U).
Proof.
Proof.
  intros; apply rk_compat; unfold equivlist; split; my_inA.
Qed.

Lemma rk_26_12 : forall A B C D E F U, rk(A::B::C::D::E::F::U)= rk(B::F::A::C::D::E::U).
Proof.
  intros; apply rk_compat; unfold equivlist; split; my_inA.
Qed.


Lemma rk_34_12 : forall A B C D U, rk(A::B::C::D::U)=rk(C::D::A::B::U).
Proof.
  intros; apply rk_compat; unfold equivlist; split; my_inA.
Qed.

Lemma rk_35_12 : forall A B C D E U, rk(A::B::C::D::E::U)=rk(C::E::A::B::D::U).
Proof.
  intros; apply rk_compat; unfold equivlist; split; my_inA.
Qed.

Lemma rk_36_12 : forall A B C D E F U, rk(A::B::C::D::E::F::U)=rk(C::F::A::B::D::E:: U).
Proof.
  intros; apply rk_compat; unfold equivlist; split; my_inA.
Qed.

Lemma rk_45_12 :forall A B C D E U, rk(A::B::C::D::E::U)=rk(D::E::A::B::C:: U).
Proof.
  intros; apply rk_compat; unfold equivlist; split; my_inA.
Qed.

Lemma rk_46_12 :forall A B C D E F U, rk(A::B::C::D::E::F::U)=rk(D::F::A::B::C::E:: U).
Proof.
  intros; apply rk_compat; unfold equivlist; split; my_inA.
Qed.

Lemma rk_56_12 :forall A B C D E F U, rk(A::B::C::D::E::F::U)=rk(E::F::A::B::C::D:: U).
Proof.
  intros; apply rk_compat; unfold equivlist; split; my_inA.
Qed.

Ltac my_rk_three_points_simplify_bis :=
match goal with
| H : _ |- exists R, rk (?P :: ?P :: _ :: nil) = 2 /\ _ /\ _ => solve_ex_p_1
(*1*)
| H : rk(?P::?Q::?T1::?T2::?T3::?T4::nil)=2 |- exists R, rk (?P :: ?Q :: R :: nil) = 2 /\ _ /\ _ =>
   solve [
       exists T1 ; apply (all_distinct_scheme _ _ _ _ _ _ H);
              solve [assumption | rk_couple_triple_bis_bis ] ]

| H : rk(?P::?T1::?Q::?T2::?T3::?T4::nil)=2 |- exists R, rk (?P :: ?Q :: R :: nil) = 2 /\ _ /\ _ =>
  rewrite rk_13_12 in H;
  solve [
      exists T1 ; apply (all_distinct_scheme _ _ _ _ _ _ H);
             solve [assumption | rk_couple_triple_bis_bis ] ]
        
| H : rk(?P::?T1::?T2::?Q::?T3::?T4::nil)=2 |- exists R, rk (?P :: ?Q :: R :: nil) = 2 /\ _ /\ _ =>
  rewrite rk_14_12 in H;
  solve [
      exists T2 ; apply (all_distinct_scheme _ _ _ _ _ _ H);
             solve [assumption | rk_couple_triple_bis_bis ] ]
        
| H : rk(?P::?T1::?T2::?T3::?Q::?T4::nil)=2 |- exists R, rk (?P :: ?Q :: R :: nil) = 2 /\ _ /\ _ =>
  rewrite rk_15_12 in H;
  solve [
      exists T2 ; apply (all_distinct_scheme _ _ _ _ _ _ H);
             solve [assumption | rk_couple_triple_bis_bis ] ]
        
| H : rk(?P::_::?T2::_::_::?Q::nil)=2 |- exists R, rk (?P :: ?Q :: R :: nil) = 2 /\ _ /\ _ =>
   rewrite rk_16_12 in H;
  solve [
      exists T2 ; apply (all_distinct_scheme _ _ _ _ _ _ H);
             solve [assumption | rk_couple_triple_bis_bis ] ]

(*2*)
| H : rk(?T1::?P::?Q::?T2::?T3::?T4::nil)=2 |- exists R, rk (?P :: ?Q :: R :: nil) = 2 /\ _ /\ _ =>
  rewrite rk_23_12 in H ; solve [
      exists T1 ; apply (all_distinct_scheme _ _ _ _ _ _ H);
             solve [assumption | rk_couple_triple_bis_bis ] ]

| H : rk(?T1::?P::?T2::?Q::?T3::?T4::nil)=2 |- exists R, rk (?P :: ?Q :: R :: nil) = 2 /\ _ /\ _ =>
    rewrite rk_24_12 in H; solve [
       exists T1 ; apply (all_distinct_scheme _ _ _ _ _ _ H);
              solve [assumption | rk_couple_triple_bis_bis ] ]

| H : rk(?T1::?P::?T2::?T3::?Q::?T4::nil)=2 |- exists R, rk (?P :: ?Q :: R :: nil) = 2 /\ _ /\ _ =>
   rewrite rk_25_12 in H; solve [
       exists T1 ; apply (all_distinct_scheme _ _ _ _ _ _ H);
              solve [assumption | rk_couple_triple_bis_bis ] ]

| H : rk(?T1::?P::?T2::?T3::?T4::?Q::nil)=2 |- exists R, rk (?P :: ?Q :: R :: nil) = 2 /\ _ /\ _ =>
   rewrite rk_26_12 in H; solve [
       exists T1 ; apply (all_distinct_scheme _ _ _ _ _ _ H);
              solve [assumption | rk_couple_triple_bis_bis ] ]
(*3*)
| H : rk(?T1::?T2::?P::?Q::?T3::?T4::nil)=2 |- exists R, rk (?P :: ?Q :: R :: nil) = 2 /\ _ /\ _ =>
   rewrite rk_34_12 in H; solve [
       exists T1 ; apply (all_distinct_scheme _ _ _ _ _ _ H);
              solve [assumption | rk_couple_triple_bis_bis ] ]

| H : rk(?T1::?T2::?P::?T3::?Q::?T4::nil)=2 |- exists R, rk (?P :: ?Q :: R :: nil) = 2 /\ _ /\ _ =>
   rewrite rk_35_12 in H; solve [
       exists T1 ; apply (all_distinct_scheme _ _ _ _ _ _ H);
              solve [assumption | rk_couple_triple_bis_bis ] ]

| H : rk(?T1::?T2::?P::?T3::?T4::?Q::nil)=2 |- exists R, rk (?P :: ?Q :: R :: nil) = 2 /\ _ /\ _ =>
   rewrite rk_36_12 in H; solve [
       exists T1 ; apply (all_distinct_scheme _ _ _ _ _ _ H);
              solve [assumption | rk_couple_triple_bis_bis ] ]


(*4*)
| H : rk(?T1::?T2::?T3::?P::?Q::?T4::nil)=2 |- exists R, rk (?P :: ?Q :: R :: nil) = 2 /\ _ /\ _ =>
   rewrite rk_45_12 in H; solve [
       exists T1 ; apply (all_distinct_scheme _ _ _ _ _ _ H);
              solve [assumption | rk_couple_triple_bis_bis ] ]

| H : rk(?T1::?T2::?T3::?P::?T4::?Q::nil)=2 |- exists R, rk (?P :: ?Q :: R :: nil) = 2 /\ _ /\ _ =>
  rewrite rk_46_12 in H; solve [
       exists T1 ; apply (all_distinct_scheme _ _ _ _ _ _ H);
              solve [assumption | rk_couple_triple_bis_bis ] ]
(*5*)
| H : rk(?T1::?T2::?T3::?T4::?P::?Q::nil)=2 |- exists R, rk (?P :: ?Q :: R :: nil) = 2 /\ _ /\ _ =>
  rewrite rk_56_12 in H; solve [
       exists T1 ; apply (all_distinct_scheme _ _ _ _ _ _ H);
              solve [assumption | rk_couple_triple_bis_bis ] ]
 (* reverse *)
(*1*)
| H : rk(?P::?Q::?T1::?T2::?T3::?T4::nil)=2 |- exists R, rk (?Q :: ?P :: R :: nil) = 2 /\ _ /\ _ =>
  idtac H ; rewrite rk_sym12 in H; my_rk_three_points_simplify_bis


| H : rk(?P::?T1::?Q::?T2::?T3::?T4::nil)=2 |- exists R, rk (?Q :: ?P :: R :: nil) = 2 /\ _ /\ _ =>
    idtac H ; rewrite rk_sym13 in H; my_rk_three_points_simplify_bis

| H : rk(?P::?T1::?T2::?Q::?T3::?T4::nil)=2 |- exists R, rk (?Q :: ?P :: R :: nil) = 2 /\ _ /\ _ =>
  idtac H ; rewrite rk_sym14 in H; my_rk_three_points_simplify_bis
| H : rk(?P::?T1::?T2::?T3::?Q::?T4::nil)=2 |- exists R, rk (?Q :: ?P :: R :: nil) = 2 /\ _ /\ _ =>
  idtac H; rewrite rk_sym15 in H; my_rk_three_points_simplify_bis
        
| H : rk(?P::?T1::?T2::?T3::?T4::?Q::nil)=2 |- exists R, rk (?Q :: ?P :: R :: nil) = 2 /\ _ /\ _ =>
  idtac H; rewrite rk_sym16 in H; my_rk_three_points_simplify_bis

(*2*)
| H : rk(?T1::?P::?Q::?T2::?T3::?T4::nil)=2 |- exists R, rk (?Q :: ?P :: R :: nil) = 2 /\ _ /\ _ =>
  idtac H; rewrite rk_sym23 in H; my_rk_three_points_simplify_bis

| H : rk(?T1::?P::?T2::?Q::?T3::?T4::nil)=2 |- exists R, rk (?Q :: ?P :: R :: nil) = 2 /\ _ /\ _ =>
  idtac H; rewrite rk_sym24 in H; my_rk_three_points_simplify_bis

| H : rk(?T1::?P::?T2::?T3::?Q::?T4::nil)=2 |- exists R, rk (?Q :: ?P :: R :: nil) = 2 /\ _ /\ _ =>
  idtac H; rewrite rk_sym25 in H; my_rk_three_points_simplify_bis

| H : rk(?T1::?P::?T2::?T3::?T4::?Q::nil)=2 |- exists R, rk (?Q :: ?P :: R :: nil) = 2 /\ _ /\ _ =>
  idtac H; rewrite rk_sym26 in H; my_rk_three_points_simplify_bis
(*3*)
| H : rk(?T1::?T2::?P::?Q::?T3::?T4::nil)=2 |- exists R, rk (?Q :: ?P :: R :: nil) = 2 /\ _ /\ _ =>
  idtac H; rewrite rk_sym34 in H; my_rk_three_points_simplify_bis

| H : rk(?T1::?T2::?P::?T3::?Q::?T4::nil)=2 |- exists R, rk (?Q :: ?P :: R :: nil) = 2 /\ _ /\ _ =>
  idtac H; rewrite rk_sym35 in H; my_rk_three_points_simplify_bis

| H : rk(?T1::?T2::?P::?T3::?T4::?Q::nil)=2 |- exists R, rk (?Q :: ?P :: R :: nil) = 2 /\ _ /\ _ =>
  idtac H; rewrite rk_sym36 in H; my_rk_three_points_simplify_bis

(*4*)
| H : rk(?T1::?T2::?T3::?P::?Q::?T4::nil)=2 |- exists R, rk (?Q :: ?P :: R :: nil) = 2 /\ _ /\ _ =>
  idtac H; rewrite rk_sym45 in H; my_rk_three_points_simplify_bis

| H : rk(?T1::?T2::?T3::?P::?T4::?Q::nil)=2 |- exists R, rk (?Q :: ?P :: R :: nil) = 2 /\ _ /\ _ =>
  idtac H; rewrite rk_sym46 in H; my_rk_three_points_simplify_bis
(*5*)
| H : rk(?T1::?T2::?T3::?T4::?P::?Q::nil)=2 |- exists R, rk (?Q :: ?P :: R :: nil) = 2 /\ _ /\ _ =>
  idtac H; rewrite rk_sym56 in H; my_rk_three_points_simplify_bis
        
end.

(** rk-three_point_on_lines : Each lines contains at least three points **)
Lemma rk_three_points_on_lines : forall P Q, exists R, 
rk (P :: Q :: R :: nil) = 2 /\ rk (Q :: R :: nil) = 2 /\ rk (P :: R :: nil) = 2.
Proof.
intros.
assert(HH := rk_distinct_points);assert(HH0 := rk_lines);use HH;use HH0.
time (case_clear_2 P;case_clear_2 Q ; my_rk_three_points_simplify_bis).
Time Qed.

(* proofs are completed up to here *)

Ltac rk_inter_simplify (*P Q R S*) X X' Y Y' :=
match goal with
| H : _ |- exists J, rk (_ :: Y :: _ :: nil) = 2 /\ rk (_ :: _ :: _ :: nil) = 2 => solve_ex_1 Y
| H : _ |- exists J, rk (Y :: _ :: _ :: nil) = 2 /\ rk (_ :: _ :: _ :: nil) = 2 => solve_ex_1 Y
| H : _ |- exists J, rk (_ :: Y' :: _ :: nil) = 2 /\ rk (_ :: _ :: _ :: nil) = 2 => solve_ex_1 Y'
| H : _ |- exists J, rk (Y' :: _ :: _ :: nil) = 2 /\ rk (_ :: _ :: _ :: nil) = 2 =>  solve_ex_1 Y'
| H : _ |- exists J, rk (_ :: _ :: _ :: nil) = 2 /\ rk (_ :: X :: _ :: nil) = 2 => solve_ex_1 X
| H : _ |- exists J, rk (_ :: _ :: _ :: nil) = 2 /\ rk (X :: _ :: _ :: nil) = 2 =>  solve_ex_1 X
| H : _ |- exists J, rk (_ :: _ :: _ :: nil) = 2 /\ rk (_ :: X' :: _ :: nil) = 2 => solve_ex_1 X'
| H : _ |- exists J, rk (_ :: _ :: _ :: nil) = 2 /\ rk (X' :: _ :: _ :: nil) = 2 => solve_ex_1 X'
| H : _ |- exists J, rk (_ :: _ :: _ :: nil) = 2 /\ rk (_ :: _ :: _ :: nil) = 2 => solve [solve_ex_1 X | solve_ex_1 X']
end.

Ltac rk_inter_simplify_bis P Q R S X X' :=
match goal with
| H : rk(R :: S :: ?Y :: ?Y' :: nil) = 2 |- _ => rk_inter_simplify (*P Q R S*) X X' Y Y'
| H : rk(R :: ?Y :: S :: ?Y' :: nil) = 2 |- _ => rk_inter_simplify (*P Q R S*) X X' Y Y'
| H : rk(R :: ?Y :: ?Y' :: S :: nil) = 2 |- _ => rk_inter_simplify (*P Q R S*) X X' Y Y'
| H : rk(S :: R :: ?Y :: ?Y' :: nil) = 2 |- _ => rk_inter_simplify (*P Q R S*) X X' Y Y'
| H : rk(S :: ?Y :: R :: ?Y' :: nil) = 2 |- _ => rk_inter_simplify (*P Q R S*) X X' Y Y'
| H : rk(S :: ?Y :: ?Y' :: R :: nil) = 2 |- _ => rk_inter_simplify (*P Q R S*) X X' Y Y'
| H : rk(?Y :: R :: S :: ?Y' :: nil) = 2 |- _ => rk_inter_simplify (*P Q R S*) X X' Y Y'
| H : rk(?Y :: R :: ?Y' :: S :: nil) = 2 |- _ => rk_inter_simplify (*P Q R S*) X X' Y Y'
| H : rk(?Y :: S :: R :: ?Y' :: nil) = 2 |- _ => rk_inter_simplify (*P Q R S*) X X' Y Y'
| H : rk(?Y :: S :: ?Y' :: R :: nil) = 2 |- _ => rk_inter_simplify (*P Q R S*) X X' Y Y'
| H : rk(?Y :: ?Y' :: R :: S :: nil) = 2 |- _ => rk_inter_simplify (*P Q R S*) X X' Y Y'
| H : rk(?Y :: ?Y' :: S :: R :: nil) = 2 |- _ => rk_inter_simplify (*P Q R S*) X X' Y Y'
end.


Ltac rk_inter_simplify_bis_bis_bis :=
match goal with
| H : _ |- exists J, rk (?P :: ?P :: _ :: nil) = 2 /\ rk (?P :: ?P :: _ :: nil) = 2 => solve_ex_p_1
| H : _ |- exists J, rk (?P :: ?P :: _ :: nil) = 2 /\ rk (?Q :: ?Q :: _ :: nil) = 2 => solve_ex_p_1

| H : _ |- exists J, rk (?P :: ?Q :: _ :: nil) = 2 /\ rk (?P :: ?P :: _ :: nil) = 2 => solve_ex_1 P
| H : _ |- exists J, rk (?Q :: ?P :: _ :: nil) = 2 /\ rk (?Q :: ?Q :: _ :: nil) = 2 => solve_ex_1 P
| H : _ |- exists J, rk (?Q :: ?Q :: _ :: nil) = 2 /\ rk (?P :: ?Q :: _ :: nil) = 2 => solve_ex_1 P
| H : _ |- exists J, rk (?Q :: ?Q :: _ :: nil) = 2 /\ rk (?Q :: ?P :: _ :: nil) = 2 => solve_ex_1 P

| H : _ |- exists J, rk (?P :: ?Q :: _ :: nil) = 2 /\ rk (?R :: ?R :: _ :: nil) = 2 => solve_ex_1 P
| H : _ |- exists J, rk (?R :: ?R :: _ :: nil) = 2 /\ rk (?P :: ?Q :: _ :: nil) = 2 => solve_ex_1 P

| H : _ |- exists J, rk (?P :: ?Q :: _ :: nil) = 2 /\ rk (?R :: ?P :: _ :: nil) = 2 => solve_ex_1 P
| H : _ |- exists J, rk (?P :: ?Q :: _ :: nil) = 2 /\ rk (?P :: ?R :: _ :: nil) = 2 => solve_ex_1 P
| H : _ |- exists J, rk (?Q :: ?P :: _ :: nil) = 2 /\ rk (?R :: ?P :: _ :: nil) = 2 => solve_ex_1 P
| H : _ |- exists J, rk (?Q :: ?P :: _ :: nil) = 2 /\ rk (?P :: ?R :: _ :: nil) = 2 => solve_ex_1 P

| H : rk(?P :: ?Q :: ?X :: ?X' :: nil) = 2 |- exists J, rk (?P :: ?Q :: _ :: nil) = 2 /\ rk (?R :: ?S :: _ :: nil) = 2 => rk_inter_simplify_bis P Q R S X X'
| H : rk(?P :: ?X :: ?Q :: ?X' :: nil) = 2 |- exists J, rk (?P :: ?Q :: _ :: nil) = 2 /\ rk (?R :: ?S :: _ :: nil) = 2 => rk_inter_simplify_bis P Q R S X X'
| H : rk(?P :: ?X :: ?X' :: ?Q :: nil) = 2 |- exists J, rk (?P :: ?Q :: _ :: nil) = 2 /\ rk (?R :: ?S :: _ :: nil) = 2 => rk_inter_simplify_bis P Q R S X X'
| H : rk(?Q :: ?P :: ?X :: ?X' :: nil) = 2 |- exists J, rk (?P :: ?Q :: _ :: nil) = 2 /\ rk (?R :: ?S :: _ :: nil) = 2 => rk_inter_simplify_bis P Q R S X X'
| H : rk(?Q :: ?X :: ?P :: ?X' :: nil) = 2 |- exists J, rk (?P :: ?Q :: _ :: nil) = 2 /\ rk (?R :: ?S :: _ :: nil) = 2 => rk_inter_simplify_bis P Q R S X X'
| H : rk(?Q :: ?X :: ?X' :: ?P :: nil) = 2 |- exists J, rk (?P :: ?Q :: _ :: nil) = 2 /\ rk (?R :: ?S :: _ :: nil) = 2 => rk_inter_simplify_bis P Q R S X X'
| H : rk(?X :: ?P :: ?Q :: ?X' :: nil) = 2 |- exists J, rk (?P :: ?Q :: _ :: nil) = 2 /\ rk (?R :: ?S :: _ :: nil) = 2 => rk_inter_simplify_bis P Q R S X X'
| H : rk(?X :: ?P :: ?X' :: ?Q :: nil) = 2 |- exists J, rk (?P :: ?Q :: _ :: nil) = 2 /\ rk (?R :: ?S :: _ :: nil) = 2 => rk_inter_simplify_bis P Q R S X X'
| H : rk(?X :: ?Q :: ?P :: ?X' :: nil) = 2 |- exists J, rk (?P :: ?Q :: _ :: nil) = 2 /\ rk (?R :: ?S :: _ :: nil) = 2 => rk_inter_simplify_bis P Q R S X X'
| H : rk(?X :: ?Q :: ?X' :: ?P :: nil) = 2 |- exists J, rk (?P :: ?Q :: _ :: nil) = 2 /\ rk (?R :: ?S :: _ :: nil) = 2 => rk_inter_simplify_bis P Q R S X X'
| H : rk(?X :: ?X' :: ?P :: ?Q :: nil) = 2 |- exists J, rk (?P :: ?Q :: _ :: nil) = 2 /\ rk (?R :: ?S :: _ :: nil) = 2 => rk_inter_simplify_bis P Q R S X X'
| H : rk(?X :: ?X' :: ?Q :: ?P :: nil) = 2 |- exists J, rk (?P :: ?Q :: _ :: nil) = 2 /\ rk (?R :: ?S :: _ :: nil) = 2 => rk_inter_simplify_bis P Q R S X X'
end.

(** rk-inter : Two lines always intersect in the plane **)
Lemma rk_inter : forall P Q R S, exists J, rk (P :: Q :: J :: nil) = 2 /\ rk (R :: S :: J :: nil) = 2.
Proof.
intros.
assert(HH := rk_distinct_points);assert(HH0 := rk_lines);use HH;use HH0.

 time (case_clear_2 P;case_clear_2 Q;
 abstract (case_clear_2 R;case_clear_2 S; rk_inter_simplify_bis_bis_bis)).

Qed.

(** rk-lower_dim : There exist three points which are not collinear **)
Lemma rk_lower_dim : exists P0 P1 P2, rk( P0 :: P1 :: P2 :: nil) >=3.
Proof.
intros.
assert(HH := rk_planes);use HH.
exists A;exists B;exists E;intuition.
Qed.

End s_fanoPlaneModelRkPG25.

(* Local Variables: *)
(* coq-prog-name: "/Users/magaud/.opam/4.06.0/bin/coqtop" *)
(* coq-load-path: (("/Users/magaud/containers/theories" "Containers") ("/Users/magaud/galapagos/dev/trunk/ProjectiveGeometry/Dev" "ProjectiveGeometry.Dev")) *)
(* suffixes: .v *)
(* End: *)

