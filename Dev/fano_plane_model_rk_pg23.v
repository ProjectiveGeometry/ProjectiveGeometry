Require Export ProjectiveGeometry.Dev.fano_matroid_tactics.

(** Fano's plane **)
(** also known as Pg(2,3). **)

(** To show that our axiom system is consistent we build a finite model. **)


(*****************************************************************************)


Section s_fanoPlaneModelRkPG23.

Parameter A B C D E F G H I J K L M : Point.

Parameter is_only_13_pts : forall P, {P=A}+{P=B}+{P=C}+{P=D}+{P=E}+{P=F}+{P=G}+{P=H}+{P=I}+{P=J}+{P=K}+{P=L}+{P=M}.

Parameter rk_points : rk(A :: nil) = 1 /\ rk(B :: nil) = 1 /\ rk(C :: nil) = 1 /\ rk(D :: nil) = 1 /\
rk(E :: nil) = 1 /\ rk(F :: nil) = 1 /\ rk(G :: nil) = 1 /\ rk(H :: nil) = 1 /\ rk(I :: nil) = 1 /\ 
rk(J :: nil) = 1 /\ rk(K :: nil) = 1 /\ rk(L :: nil) = 1 /\ rk(M :: nil) = 1.

Parameter rk_distinct_points : 
rk(A :: B :: nil) = 2 /\ rk(A :: C :: nil) = 2 /\ rk(A :: D :: nil) = 2 /\ rk(A :: E :: nil) = 2 /\ rk(A :: F :: nil) = 2 /\ rk(A :: G :: nil) = 2 /\
rk(A :: H :: nil) = 2 /\ rk(A :: I :: nil) = 2 /\ rk(A :: J :: nil) = 2 /\ rk(A :: K :: nil) = 2 /\ rk(A :: L :: nil) = 2 /\ rk(A :: M :: nil) = 2 /\
rk(B :: C :: nil) = 2 /\ rk(B :: D :: nil) = 2 /\ rk(B :: E :: nil) = 2 /\ rk(B :: F :: nil) = 2 /\ rk(B :: G :: nil) = 2 /\
rk(B :: H :: nil) = 2 /\ rk(B :: I :: nil) = 2 /\ rk(B :: J :: nil) = 2 /\ rk(B :: K :: nil) = 2 /\ rk(B :: L :: nil) = 2 /\ rk(B :: M :: nil) = 2 /\
rk(C :: D :: nil) = 2 /\ rk(C :: E :: nil) = 2 /\ rk(C :: F :: nil) = 2 /\ rk(C :: G :: nil) = 2 /\
rk(C :: H :: nil) = 2 /\ rk(C :: I :: nil) = 2 /\ rk(C :: J :: nil) = 2 /\ rk(C :: K :: nil) = 2 /\ rk(C :: L :: nil) = 2 /\ rk(C :: M :: nil) = 2 /\
rk(D :: E :: nil) = 2 /\ rk(D :: F :: nil) = 2 /\ rk(D :: G :: nil) = 2 /\
rk(D :: H :: nil) = 2 /\ rk(D :: I :: nil) = 2 /\ rk(D :: J :: nil) = 2 /\ rk(D :: K :: nil) = 2 /\ rk(D :: L :: nil) = 2 /\ rk(D :: M :: nil) = 2 /\
rk(E :: F :: nil) = 2 /\ rk(E :: G :: nil) = 2 /\
rk(E :: H :: nil) = 2 /\ rk(E :: I :: nil) = 2 /\ rk(E :: J :: nil) = 2 /\ rk(E :: K :: nil) = 2 /\ rk(E :: L :: nil) = 2 /\ rk(E :: M :: nil) = 2 /\
rk(F :: G :: nil) = 2 /\
rk(F :: H :: nil) = 2 /\ rk(F :: I :: nil) = 2 /\ rk(F :: J :: nil) = 2 /\ rk(F :: K :: nil) = 2 /\ rk(F :: L :: nil) = 2 /\ rk(F :: M :: nil) = 2 /\
rk(G :: H :: nil) = 2 /\ rk(G :: I :: nil) = 2 /\ rk(G :: J :: nil) = 2 /\ rk(G :: K :: nil) = 2 /\ rk(G :: L :: nil) = 2 /\ rk(G :: M :: nil) = 2 /\
rk(H :: I :: nil) = 2 /\ rk(H :: J :: nil) = 2 /\ rk(H :: K :: nil) = 2 /\ rk(H :: L :: nil) = 2 /\ rk(H :: M :: nil) = 2 /\
rk(I :: J :: nil) = 2 /\ rk(I :: K :: nil) = 2 /\ rk(I :: L :: nil) = 2 /\ rk(I :: M :: nil) = 2 /\
rk(J :: K :: nil) = 2 /\ rk(J :: L :: nil) = 2 /\ rk(J :: M :: nil) = 2 /\
rk(K :: L :: nil) = 2 /\ rk(K :: M :: nil) = 2 /\
rk(L :: M :: nil) = 2.

Parameter rk_lines :
rk (A :: B :: C :: D :: nil) = 2 /\ rk (A :: E :: F :: G :: nil) = 2 /\
rk (A :: I :: J :: M :: nil) = 2 /\ rk (A :: H :: K :: L :: nil) = 2 /\
rk (B :: E :: H :: I :: nil) = 2 /\ rk (B :: G :: J :: L :: nil) = 2 /\
rk (B :: F :: K :: M :: nil) = 2 /\ rk (D :: E :: J :: K :: nil) = 2 /\
rk (C :: E :: L :: M :: nil) = 2 /\ rk (C :: F :: H :: J :: nil) = 2 /\
rk (D :: G :: H :: M :: nil) = 2 /\ rk (D :: F :: I :: L :: nil) = 2 /\
rk (C :: G :: I :: K :: nil) = 2.

Parameter rk_planes :
rk (A :: B :: E :: nil) = 3 /\ rk (A :: B :: F :: nil) = 3 /\ rk (A :: B :: G :: nil) = 3 /\
rk (A :: B :: H :: nil) = 3 /\ rk (A :: B :: I :: nil) = 3 /\ rk (A :: B :: J :: nil) = 3 /\
rk (A :: B :: K :: nil) = 3 /\ rk (A :: B :: L :: nil) = 3 /\ rk (A :: B :: M :: nil) = 3 /\
rk (A :: C :: E :: nil) = 3 /\ rk (A :: C :: F :: nil) = 3 /\ rk (A :: C :: G :: nil) = 3 /\
rk (A :: C :: H :: nil) = 3 /\ rk (A :: C :: I :: nil) = 3 /\ rk (A :: C :: J :: nil) = 3 /\
rk (A :: C :: K :: nil) = 3 /\ rk (A :: C :: L :: nil) = 3 /\ rk (A :: C :: M :: nil) = 3 /\
rk (A :: D :: E :: nil) = 3 /\ rk (A :: D :: F :: nil) = 3 /\ rk (A :: D :: G :: nil) = 3 /\
rk (A :: D :: H :: nil) = 3 /\ rk (A :: D :: I :: nil) = 3 /\ rk (A :: D :: J :: nil) = 3 /\
rk (A :: D :: K :: nil) = 3 /\ rk (A :: D :: L :: nil) = 3 /\ rk (A :: D :: M :: nil) = 3 /\
rk (A :: E :: H :: nil) = 3 /\ rk (A :: E :: I :: nil) = 3 /\ rk (A :: E :: J :: nil) = 3 /\
rk (A :: E :: K :: nil) = 3 /\ rk (A :: E :: L :: nil) = 3 /\ rk (A :: E :: M :: nil) = 3 /\
rk (A :: F :: H :: nil) = 3 /\ rk (A :: F :: I :: nil) = 3 /\ rk (A :: F :: J :: nil) = 3 /\
rk (A :: F :: K :: nil) = 3 /\ rk (A :: F :: L :: nil) = 3 /\ rk (A :: F :: M :: nil) = 3 /\
rk (A :: G :: H :: nil) = 3 /\ rk (A :: G :: I :: nil) = 3 /\ rk (A :: G :: J :: nil) = 3 /\
rk (A :: G :: K :: nil) = 3 /\ rk (A :: G :: L :: nil) = 3 /\ rk (A :: G :: M :: nil) = 3 /\
rk (A :: H :: I :: nil) = 3 /\ rk (A :: H :: J :: nil) = 3 /\ rk (A :: H :: M :: nil) = 3 /\
rk (A :: I :: K :: nil) = 3 /\ rk (A :: I :: L :: nil) = 3 /\
rk (A :: J :: K :: nil) = 3 /\ rk (A :: J :: L :: nil) = 3 /\
rk (A :: K :: M :: nil) = 3 /\
rk (A :: L :: M :: nil) = 3 /\
rk (B :: C :: E :: nil) = 3 /\ rk (B :: C :: F :: nil) = 3 /\ rk (B :: C :: G :: nil) = 3 /\
rk (B :: C :: H :: nil) = 3 /\ rk (B :: C :: I :: nil) = 3 /\ rk (B :: C :: J :: nil) = 3 /\
rk (B :: C :: K :: nil) = 3 /\ rk (B :: C :: L :: nil) = 3 /\ rk (B :: C :: M :: nil) = 3 /\
rk (B :: D :: E :: nil) = 3 /\ rk (B :: D :: F :: nil) = 3 /\ rk (B :: D :: G :: nil) = 3 /\
rk (B :: D :: H :: nil) = 3 /\ rk (B :: D :: I :: nil) = 3 /\ rk (B :: D :: J :: nil) = 3 /\
rk (B :: D :: K :: nil) = 3 /\ rk (B :: D :: L :: nil) = 3 /\ rk (B :: D :: M :: nil) = 3 /\
rk (B :: E :: F :: nil) = 3 /\ rk (B :: E :: G :: nil) = 3 /\ rk (B :: E :: J :: nil) = 3 /\
rk (B :: E :: K :: nil) = 3 /\ rk (B :: E :: L :: nil) = 3 /\ rk (B :: E :: M :: nil) = 3 /\
rk (B :: F :: G :: nil) = 3 /\ rk (B :: F :: H :: nil) = 3 /\ rk (B :: F :: I :: nil) = 3 /\
rk (B :: F :: J :: nil) = 3 /\ rk (B :: F :: L :: nil) = 3 /\
rk (B :: G :: H :: nil) = 3 /\ rk (B :: G :: I :: nil) = 3 /\ rk (B :: G :: K :: nil) = 3 /\
rk (B :: G :: M :: nil) = 3 /\
rk (B :: H :: J :: nil) = 3 /\ rk (B :: H :: K :: nil) = 3 /\ rk (B :: H :: L :: nil) = 3 /\
rk (B :: H :: M :: nil) = 3 /\
rk (B :: I :: J :: nil) = 3 /\ rk (B :: I :: K :: nil) = 3 /\ rk (B :: I :: L :: nil) = 3 /\
rk (B :: I :: M :: nil) = 3 /\
rk (B :: J :: K :: nil) = 3 /\ rk (B :: J :: M :: nil) = 3 /\
rk (B :: K :: L :: nil) = 3 /\
rk (B :: L :: M :: nil) = 3 /\
rk (C :: D :: E :: nil) = 3 /\ rk (C :: D :: F :: nil) = 3 /\ rk (C :: D :: G :: nil) = 3 /\
rk (C :: D :: H :: nil) = 3 /\ rk (C :: D :: I :: nil) = 3 /\ rk (C :: D :: J :: nil) = 3 /\
rk (C :: D :: K :: nil) = 3 /\ rk (C :: D :: L :: nil) = 3 /\ rk (C :: D :: M :: nil) = 3 /\
rk (C :: E :: F :: nil) = 3 /\ rk (C :: E :: G :: nil) = 3 /\ rk (C :: E :: H :: nil) = 3 /\
rk (C :: E :: I :: nil) = 3 /\ rk (C :: E :: J :: nil) = 3 /\ rk (C :: E :: K :: nil) = 3 /\
rk (C :: F :: G :: nil) = 3 /\ rk (C :: F :: I :: nil) = 3 /\ rk (C :: F :: K :: nil) = 3 /\
rk (C :: F :: L :: nil) = 3 /\ rk (C :: F :: M :: nil) = 3 /\
rk (C :: G :: H :: nil) = 3 /\ rk (C :: G :: J :: nil) = 3 /\ rk (C :: G :: L :: nil) = 3 /\
rk (C :: G :: M :: nil) = 3 /\
rk (C :: H :: I :: nil) = 3 /\ rk (C :: H :: K :: nil) = 3 /\ rk (C :: H :: L :: nil) = 3 /\
rk (C :: H :: M :: nil) = 3 /\
rk (C :: I :: J :: nil) = 3 /\ rk (C :: I :: L :: nil) = 3 /\ rk (C :: I :: M :: nil) = 3 /\
rk (C :: J :: K :: nil) = 3 /\ rk (C :: J :: L :: nil) = 3 /\ rk (C :: J :: M :: nil) = 3 /\
rk (C :: K :: L :: nil) = 3 /\ rk (C :: K :: M :: nil) = 3 /\ rk (C :: K :: L :: nil) = 3 /\
rk (D :: E :: F :: nil) = 3 /\ rk (D :: E :: G :: nil) = 3 /\ rk (D :: E :: H :: nil) = 3 /\
rk (D :: E :: I :: nil) = 3 /\ rk (D :: E :: L :: nil) = 3 /\ rk (D :: E :: M :: nil) = 3 /\
rk (D :: F :: G :: nil) = 3 /\ rk (D :: F :: H :: nil) = 3 /\ rk (D :: F :: J :: nil) = 3 /\
rk (D :: F :: K :: nil) = 3 /\ rk (D :: F :: M :: nil) = 3 /\ 
rk (D :: G :: I :: nil) = 3 /\ rk (D :: G :: J :: nil) = 3 /\ rk (D :: G :: K :: nil) = 3 /\
rk (D :: G :: L :: nil) = 3 /\
rk (D :: H :: I :: nil) = 3 /\ rk (D :: H :: J :: nil) = 3 /\ rk (D :: H :: K :: nil) = 3 /\
rk (D :: H :: L :: nil) = 3 /\ 
rk (D :: I :: J :: nil) = 3 /\ rk (D :: I :: K :: nil) = 3 /\ rk (D :: I :: M :: nil) = 3 /\ 
rk (D :: J :: L :: nil) = 3 /\ rk (D :: J :: M :: nil) = 3 /\
rk (D :: K :: L :: nil) = 3 /\ rk (D :: K :: M :: nil) = 3 /\ 
rk (D :: L :: M :: nil) = 3 /\
rk (E :: F :: H :: nil) = 3 /\ rk (E :: F :: I :: nil) = 3 /\ rk (E :: F :: J :: nil) = 3 /\
rk (E :: F :: K :: nil) = 3 /\ rk (E :: F :: L :: nil) = 3 /\ rk (E :: F :: M :: nil) = 3 /\
rk (E :: G :: H :: nil) = 3 /\ rk (E :: G :: I :: nil) = 3 /\ rk (E :: G :: J :: nil) = 3 /\
rk (E :: G :: K :: nil) = 3 /\ rk (E :: G :: L :: nil) = 3 /\ rk (E :: G :: M :: nil) = 3 /\
rk (E :: H :: J :: nil) = 3 /\ rk (E :: H :: K :: nil) = 3 /\ rk (E :: H :: L :: nil) = 3 /\
rk (E :: H :: M :: nil) = 3 /\ 
rk (E :: I :: J :: nil) = 3 /\ rk (E :: I :: K :: nil) = 3 /\ rk (E :: I :: L :: nil) = 3 /\
rk (E :: I :: M :: nil) = 3 /\ 
rk (E :: J :: L :: nil) = 3 /\ rk (E :: J :: M :: nil) = 3 /\ 
rk (E :: K :: L :: nil) = 3 /\ rk (E :: K :: M :: nil) = 3 /\
rk (F :: G :: H :: nil) = 3 /\ rk (F :: G :: I :: nil) = 3 /\ rk (F :: G :: J :: nil) = 3 /\
rk (F :: G :: K :: nil) = 3 /\ rk (F :: G :: L :: nil) = 3 /\ rk (F :: G :: M :: nil) = 3 /\
rk (F :: H :: I :: nil) = 3 /\ rk (F :: H :: K :: nil) = 3 /\ rk (F :: H :: L :: nil) = 3 /\
rk (F :: H :: M :: nil) = 3 /\
rk (F :: I :: J :: nil) = 3 /\ rk (F :: I :: K :: nil) = 3 /\ rk (F :: I :: M :: nil) = 3 /\
rk (F :: J :: K :: nil) = 3 /\ rk (F :: J :: L :: nil) = 3 /\ rk (F :: J :: M :: nil) = 3 /\
rk (F :: K :: L :: nil) = 3 /\
rk (F :: L :: M :: nil) = 3 /\
rk (G :: H :: I :: nil) = 3 /\ rk (G :: H :: J :: nil) = 3 /\ rk (G :: H :: K :: nil) = 3 /\
rk (G :: H :: L :: nil) = 3 /\
rk (G :: I :: J :: nil) = 3 /\ rk (G :: I :: L :: nil) = 3 /\ rk (G :: I :: M :: nil) = 3 /\
rk (G :: J :: K :: nil) = 3 /\ rk (G :: J :: M :: nil) = 3 /\
rk (G :: K :: L :: nil) = 3 /\ rk (G :: K :: M :: nil) = 3 /\
rk (G :: L :: M :: nil) = 3 /\
rk (H :: I :: J :: nil) = 3 /\ rk (H :: I :: K :: nil) = 3 /\ rk (H :: I :: L :: nil) = 3 /\
rk (H :: I :: M :: nil) = 3 /\
rk (H :: J :: K :: nil) = 3 /\ rk (H :: J :: L :: nil) = 3 /\ rk (H :: J :: M :: nil) = 3 /\
rk (H :: K :: M :: nil) = 3 /\
rk (H :: L :: M :: nil) = 3 /\
rk (I :: J :: K :: nil) = 3 /\ rk (I :: J :: L :: nil) = 3 /\
rk (I :: K :: L :: nil) = 3 /\ rk (I :: K :: M :: nil) = 3 /\
rk (I :: L :: M :: nil) = 3 /\
rk (J :: K :: L :: nil) = 3 /\ rk (J :: K :: M :: nil) = 3 /\
rk (J :: L :: M :: nil) = 3 /\
rk (K :: L :: M :: nil) = 3.


(*****************************************************************************)

Ltac case_clear P := let HA:= fresh in let HB:=fresh in let HC:=fresh in let HD:=fresh in let HE:=fresh in let HF:=fresh in let HG:=fresh in let HH:=fresh in let HI:= fresh in let HL:=fresh in let HM:= fresh in 
destruct (is_only_13_pts P) as [[[[[[[[[[[[HA | HB] | HC] | HD] | HE ] | HF ] | HG] | HH] |  HI ] | HJ] | HK] | HL] | HM]; subst P.

(** rk-singleton : The rank of a point is always greater than one  **) 
Lemma rk_singleton_ge : forall P, rk (P :: nil) >= 1.
Proof.
intros.
assert(HH := rk_points);use HH.
case_clear P;intuition.
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
case_clear P;case_clear Q;try equal_degens;try assumption;rewrite couple_equal;assumption.
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
assert(HH0 := rk_couple_ge P Q H0).
omega.
Qed.

Lemma couple_rk1 : forall P Q, rk(P :: Q :: nil) = 2 -> ~ P = Q.
Proof.
intros.
intro.
rewrite H1 in H0.
assert(HH : equivlist (Q :: Q :: nil) (Q :: nil));[my_inO|].
rewrite HH in H0.
assert(HH0 := rk_singleton_1 Q).
omega.
Qed.

Lemma quadruple_rk2_to_triple_rk2 : forall P Q R S : Point,
rk (P :: Q :: nil) = 2 -> rk(P :: Q ::  R :: S :: nil) = 2 -> rk(P :: Q :: R :: nil) = 2.
Proof.
intros.
assert(HH : incl (P :: Q :: R :: nil) (P :: Q :: R :: S :: nil));[my_inO|].
assert(HH0 := matroid2 (P :: Q :: R :: nil) (P :: Q :: R :: S :: nil) HH).
assert(HH1bis := couple_rk1 P Q H0).
assert(HH1 := rk_couple P Q HH1bis).
assert(HH2 : incl (P :: Q :: nil) (P :: Q :: R :: nil));[my_inO|].
assert(HH3 := matroid2 (P :: Q :: nil) (P :: Q :: R :: nil) HH2).
omega.
Qed.

Ltac rk_triple_to_quadruple :=
match goal with
| H0 : rk(?A :: ?B :: ?C :: ?D :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple |assumption]);assumption
| H0 : rk(?A :: ?B :: ?D :: ?C :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_1 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple|assumption]);assumption
| H0 : rk(?A :: ?C :: ?B :: ?D :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_2 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple|assumption]);assumption
| H0 : rk(?A :: ?C :: ?D :: ?B :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_3 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple|assumption]);assumption
| H0 : rk(?A :: ?D :: ?B :: ?C :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_4 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple|assumption]);assumption
| H0 : rk(?A :: ?D :: ?C :: ?B :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_5 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple|assumption]);assumption
| H0 : rk(?B :: ?A :: ?C :: ?D :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_6 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple|assumption]);assumption
| H0 : rk(?B :: ?A :: ?D :: ?C :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_7 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple|assumption]);assumption
| H0 : rk(?B :: ?C :: ?A :: ?D :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_8 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple|assumption]);assumption
| H0 : rk(?B :: ?C :: ?D :: ?A :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_9 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple|assumption]);assumption
| H0 : rk(?B :: ?D :: ?A :: ?C :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_10 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple|assumption]);assumption
| H0 : rk(?B :: ?D :: ?C :: ?A :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_11 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple|assumption]);assumption
| H0 : rk(?C :: ?A :: ?B :: ?D :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_12 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple|assumption]);assumption
| H0 : rk(?C :: ?A :: ?D :: ?B :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_13 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple|assumption]);assumption
| H0 : rk(?C :: ?B :: ?A :: ?D :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_14 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple|assumption]);assumption
| H0 : rk(?C :: ?B :: ?D :: ?A :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_15 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple|assumption]);assumption
| H0 : rk(?C :: ?D :: ?A :: ?B :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_16 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple|assumption]);assumption
| H0 : rk(?C :: ?D :: ?B :: ?A :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_17 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple|assumption]);assumption
| H0 : rk(?D :: ?A :: ?B :: ?C :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_18 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple|assumption]);assumption
| H0 : rk(?D :: ?A :: ?C :: ?B :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_19 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple|assumption]);assumption
| H0 : rk(?D :: ?B :: ?A :: ?C :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_20 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple|assumption]);assumption
| H0 : rk(?D :: ?B :: ?C :: ?A :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_21 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple|assumption]);assumption
| H0 : rk(?D :: ?C :: ?A :: ?B :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_22 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple|assumption]);assumption
| H0 : rk(?D :: ?C :: ?B :: ?A :: nil) = 2 |- rk(?A :: ?B :: ?C :: nil) = 2 =>
  rewrite <-quadruple_equal_23 in H0;let HH := fresh in assert(HH : rk(A :: B :: C :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 A B C D);solve [rk_couple_triple|assumption]);assumption
end.

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

Ltac degens_rk2' :=
  solve[ first [apply triple_rk2_1 | apply triple_rk2_2 | apply triple_rk2_3];rk_couple_triple].

Ltac solve_ex_1 L := solve [exists L; repeat split;solve [ assumption |  degens_rk2' | rk_couple_triple | rk_triple_to_quadruple]].

Ltac solve_ex_p_1 := first [
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
 ].

Ltac rk_three_points_simplify P Q :=
match goal with
| H0 : rk(P :: Q :: ?R :: ?X :: nil) = 2 |- _ => let HH := fresh in assert(HH : rk(P :: Q :: R :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 P Q R X);try rk_couple_triple;assumption);solve_ex_1 R
| H0 : rk(P :: ?R :: Q :: ?X :: nil) = 2 |- _ => rewrite <-quadruple_equal_2 in H0;let HH := fresh in assert(HH : rk(P :: Q :: R :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 P Q R X);try rk_couple_triple;assumption);solve_ex_1 R
| H0 : rk(P :: ?R :: ?X :: Q :: nil) = 2 |- _ => rewrite <-quadruple_equal_3 in H0;let HH := fresh in assert(HH : rk(P :: Q :: R :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 P Q R X);try rk_couple_triple;assumption);solve_ex_1 R
| H0 : rk(Q :: P :: ?R :: ?X :: nil) = 2 |- _ => rewrite <-quadruple_equal_6 in H0;let HH := fresh in assert(HH : rk(P :: Q :: R :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 P Q R X);try rk_couple_triple;assumption);solve_ex_1 R
| H0 : rk(Q :: ?R :: P :: ?X :: nil) = 2 |- _ => rewrite <-quadruple_equal_8 in H0;let HH := fresh in assert(HH : rk(P :: Q :: R :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 P Q R X);try rk_couple_triple;assumption);solve_ex_1 R
| H0 : rk(Q :: ?R :: ?X :: P :: nil) = 2 |- _ => rewrite <-quadruple_equal_9 in H0;let HH := fresh in assert(HH : rk(P :: Q :: R :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 P Q R X);try rk_couple_triple;assumption);solve_ex_1 R
| H0 : rk(?R :: P :: Q :: ?X :: nil) = 2 |- _ => rewrite <-quadruple_equal_12 in H0;let HH := fresh in assert(HH : rk(P :: Q :: R :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 P Q R X);try rk_couple_triple;assumption);solve_ex_1 R
| H0 : rk(?R :: P :: ?X :: Q :: nil) = 2 |- _ => rewrite <-quadruple_equal_13 in H0;let HH := fresh in assert(HH : rk(P :: Q :: R :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 P Q R X);try rk_couple_triple;assumption);solve_ex_1 R
| H0 : rk(?R :: Q :: P :: ?X :: nil) = 2 |- _ => rewrite <-quadruple_equal_14 in H0;let HH := fresh in assert(HH : rk(P :: Q :: R :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 P Q R X);try rk_couple_triple;assumption);solve_ex_1 R
| H0 : rk(?R :: Q :: ?X :: P :: nil) = 2 |- _ => rewrite <-quadruple_equal_15 in H0;let HH := fresh in assert(HH : rk(P :: Q :: R :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 P Q R X);try rk_couple_triple;assumption);solve_ex_1 R
| H0 : rk(?R :: ?X :: P :: Q :: nil) = 2 |- _ => rewrite <-quadruple_equal_16 in H0;let HH := fresh in assert(HH : rk(P :: Q :: R :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 P Q R X);try rk_couple_triple;assumption);solve_ex_1 R
| H0 : rk(?R :: ?X :: Q :: P :: nil) = 2 |- _ => rewrite <-quadruple_equal_17 in H0;let HH := fresh in assert(HH : rk(P :: Q :: R :: nil) = 2) by (apply (quadruple_rk2_to_triple_rk2 P Q R X);try rk_couple_triple;assumption);solve_ex_1 R
end.

Ltac rk_three_points_simplify_bis :=
match goal with
| H : _ |- exists R, rk (?P :: ?P :: _ :: nil) = 2 /\ _ /\ _ => solve_ex_p_1
| H : _ |- exists R, rk (?P :: ?Q :: R :: nil) = 2 /\ _ /\ _ => rk_three_points_simplify P Q
end.

(** rk-three_point_on_lines : Each lines contains at least three points **)
Lemma rk_three_points_on_lines : forall P Q, exists R, 
rk (P :: Q :: R :: nil) = 2 /\ rk (Q :: R :: nil) = 2 /\ rk (P :: R :: nil) = 2.
Proof.
intros.
assert(HH := rk_distinct_points);assert(HH0 := rk_lines);use HH;use HH0.
case_clear P;case_clear Q;rk_three_points_simplify_bis.
Qed.

Ltac rk_inter_simplify P Q R S X X' Y Y' :=
match goal with
| H : _ |- exists J, rk (_ :: Y :: _ :: nil) = 2 /\ rk (_ :: _ :: _ :: nil) = 2 => try solve_ex_1 Y
| H : _ |- exists J, rk (Y :: _ :: _ :: nil) = 2 /\ rk (_ :: _ :: _ :: nil) = 2 => try solve_ex_1 Y
| H : _ |- exists J, rk (_ :: Y' :: _ :: nil) = 2 /\ rk (_ :: _ :: _ :: nil) = 2 => try solve_ex_1 Y'
| H : _ |- exists J, rk (Y' :: _ :: _ :: nil) = 2 /\ rk (_ :: _ :: _ :: nil) = 2 => try solve_ex_1 Y'
| H : _ |- exists J, rk (_ :: _ :: _ :: nil) = 2 /\ rk (_ :: X :: _ :: nil) = 2 => try solve_ex_1 X
| H : _ |- exists J, rk (_ :: _ :: _ :: nil) = 2 /\ rk (X :: _ :: _ :: nil) = 2 => try solve_ex_1 X
| H : _ |- exists J, rk (_ :: _ :: _ :: nil) = 2 /\ rk (_ :: X' :: _ :: nil) = 2 => try solve_ex_1 X'
| H : _ |- exists J, rk (_ :: _ :: _ :: nil) = 2 /\ rk (X' :: _ :: _ :: nil) = 2 => try solve_ex_1 X'
| H : _ |- exists J, rk (_ :: _ :: _ :: nil) = 2 /\ rk (_ :: _ :: _ :: nil) = 2 => try solve_ex_1 X;try solve_ex_1 X'
end.

Ltac rk_inter_simplify_bis P Q R S X X' :=
match goal with
| H : rk(R :: S :: ?Y :: ?Y' :: nil) = 2 |- _ => rk_inter_simplify P Q R S X X' Y Y'
| H : rk(R :: ?Y :: S :: ?Y' :: nil) = 2 |- _ => rk_inter_simplify P Q R S X X' Y Y'
| H : rk(R :: ?Y :: ?Y' :: S :: nil) = 2 |- _ => rk_inter_simplify P Q R S X X' Y Y'
| H : rk(S :: R :: ?Y :: ?Y' :: nil) = 2 |- _ => rk_inter_simplify P Q R S X X' Y Y'
| H : rk(S :: ?Y :: R :: ?Y' :: nil) = 2 |- _ => rk_inter_simplify P Q R S X X' Y Y'
| H : rk(S :: ?Y :: ?Y' :: R :: nil) = 2 |- _ => rk_inter_simplify P Q R S X X' Y Y'
| H : rk(?Y :: R :: S :: ?Y' :: nil) = 2 |- _ => rk_inter_simplify P Q R S X X' Y Y'
| H : rk(?Y :: R :: ?Y' :: S :: nil) = 2 |- _ => rk_inter_simplify P Q R S X X' Y Y'
| H : rk(?Y :: S :: R :: ?Y' :: nil) = 2 |- _ => rk_inter_simplify P Q R S X X' Y Y'
| H : rk(?Y :: S :: ?Y' :: R :: nil) = 2 |- _ => rk_inter_simplify P Q R S X X' Y Y'
| H : rk(?Y :: ?Y' :: R :: S :: nil) = 2 |- _ => rk_inter_simplify P Q R S X X' Y Y'
| H : rk(?Y :: ?Y' :: S :: R :: nil) = 2 |- _ => rk_inter_simplify P Q R S X X' Y Y'
end.

Ltac rk_inter_simplify_bis_bis :=
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
case_clear P;case_clear Q;
abstract(case_clear R;case_clear S;try rk_inter_simplify_bis_bis).
Qed.

(** rk-lower_dim : There exist three points which are not collinear **)
Lemma rk_lower_dim : exists P0 P1 P2, rk( P0 :: P1 :: P2 :: nil) >=3.
Proof.
intros.
assert(HH := rk_planes);use HH.
exists A;exists B;exists E;intuition.
Qed.

End s_fanoPlaneModelRkPG23.
