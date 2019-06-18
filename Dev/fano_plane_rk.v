Require Export ProjectiveGeometry.Dev.fano_rk_tactics.

(*****************************************************************************)
(** Fano plane rank **)

Module Type fano_plane_rank.

Parameter A B C D E F G : Point.

Parameter is_only_7_pts : forall P, {P=A}+{P=B}+{P=C}+{P=D}+{P=E}+{P=F}+{P=G}.

Parameter rk_points : rk(A :: nil) = 1 /\ rk(B :: nil) = 1 /\ rk(C :: nil) = 1 /\ rk(D :: nil) = 1 /\
rk(E :: nil) = 1 /\ rk(F :: nil) = 1 /\ rk(G :: nil) = 1.

Parameter rk_distinct_points : 
rk(A :: B :: nil) = 2 /\ rk(A :: C :: nil) = 2 /\ rk(A :: D :: nil) = 2 /\ rk(A :: E :: nil) = 2 /\ rk(A :: F :: nil) = 2 /\ rk(A :: G :: nil) = 2 /\
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

End fano_plane_rank.


(*****************************************************************************)


Module swapfr3 (M:fano_plane_rank) : fano_plane_rank
with Definition A:= M.B 
with Definition B:=M.E
with Definition C:=M.D
with Definition D:=M.F
with Definition E:=M.C
with Definition F:=M.G
with Definition G:=M.A.

Definition A:=M.B.
Definition B:=M.E.
Definition C:=M.D.
Definition D:=M.F.
Definition E:=M.C.
Definition F:=M.G.
Definition G:=M.A.

Lemma is_only_7_pts : forall P:Point, {P=A}+{P=B}+{P=C}+{P=D}+{P=E}+{P=F}+{P=G}.
Proof.
generalize (M.is_only_7_pts).
unfold A, B,C, D, E, F, G.
intros H P; elim (H P).
intuition.
intuition.
Qed.

Lemma rk_points : rk(A :: nil) = 1 /\ rk(B :: nil) = 1 /\ rk(C :: nil) = 1 /\ rk(D :: nil) = 1 /\
rk(E :: nil) = 1 /\ rk(F :: nil) = 1 /\ rk(G :: nil) = 1.
Proof.
generalize (M.rk_points).
unfold A, B, C, D, E, F, G.
intros;intuition.
Qed.

Lemma rk_distinct_points : rk(A :: B :: nil) = 2 /\ rk(A :: C :: nil) = 2 /\ rk(A :: D :: nil) = 2 /\ rk(A :: E :: nil) = 2 /\rk(A :: F :: nil) = 2 /\ rk(A :: G :: nil) = 2 /\
rk(B :: C :: nil) = 2 /\ rk(B :: D :: nil) = 2 /\ rk(B :: E :: nil) = 2 /\ rk(B :: F :: nil) = 2 /\ rk(B :: G :: nil) = 2 /\
rk(C :: D :: nil) = 2 /\ rk(C :: E :: nil) = 2 /\ rk(C :: F :: nil) = 2 /\ rk(C :: G :: nil) = 2 /\
rk(D :: E :: nil) = 2 /\ rk(D :: F :: nil) = 2 /\ rk(D :: G :: nil) = 2 /\
rk(E :: F :: nil) = 2 /\ rk(E :: G :: nil) = 2 /\
rk(F :: G :: nil) = 2.
Proof.
generalize (M.rk_distinct_points).
unfold A, B, C, D, E, F, G.
intros;intuition;solve[rk_couple_triple].
Qed.

Lemma rk_lines : rk (A :: B :: F :: nil) = 2 /\ rk (B :: C :: D :: nil) = 2 /\ 
rk (C :: A :: E :: nil) = 2 /\ rk (A :: D :: G :: nil) = 2 /\ rk (B :: E :: G :: nil) = 2 /\
rk (C :: F :: G :: nil) = 2 /\ rk (D :: E :: F :: nil) = 2.
Proof.
generalize (M.rk_lines).
unfold A, B, C, D, E, F, G.
intros.
my_split.
repeat split;solve[rk_couple_triple].
Qed.

Lemma rk_planes : rk(A :: B :: C :: nil) = 3 /\ rk(A :: B :: D :: nil) = 3 /\ rk(A :: B :: E :: nil) = 3 /\ rk(A :: B :: G :: nil) = 3 /\
rk(A :: C :: D :: nil) = 3 /\ rk(A :: C :: F :: nil) = 3 /\ rk(A :: C :: G :: nil) = 3 /\ rk(A :: D :: E :: nil) = 3 /\
rk(A :: D :: F :: nil) = 3 /\ rk(A :: E :: F :: nil) = 3 /\ rk(A :: E :: G :: nil) = 3 /\ rk(A :: F :: G :: nil) = 3 /\
rk(B :: C :: E :: nil) = 3 /\ rk(B :: C :: F :: nil) = 3 /\ rk(B :: C :: G :: nil) = 3 /\ rk(B :: D :: E :: nil) = 3 /\
rk(B :: D :: F :: nil) = 3 /\ rk(B :: D :: G :: nil) = 3 /\ rk(B :: E :: F :: nil) = 3 /\ rk(B :: F :: G :: nil) = 3 /\
rk(C :: D :: E :: nil) = 3 /\ rk(C :: D :: F :: nil) = 3 /\ rk(C :: D :: G :: nil) = 3 /\ rk(C :: E :: F :: nil) = 3 /\
rk(C :: E :: G :: nil) = 3 /\ rk(D :: E :: G :: nil) = 3 /\ rk(D :: F :: G :: nil) = 3 /\ rk(E :: F :: G :: nil) = 3.
Proof.
generalize (M.rk_planes).
unfold A, B, C, D, E, F, G.
intros.
my_split.
repeat split;solve[rk_couple_triple].
Qed.

End swapfr3.


(*****************************************************************************)


Module Desargues_from_A (M:fano_plane_rank).

Import M.

Ltac new_case P := 
match (type of P) with 
| Point => generalize (is_only_7_pts P) ; let Q := fresh in (intros Q; decompose [sumor sumbool] Q; clear Q)
end.

Ltac case_eq_s O := new_case O.

Ltac case_clear_1 P := case_eq_s P.

(*** Autres lemmes matroid ***)

Lemma rk_distinct :
rk(A :: B :: nil) = 2 /\ rk(A :: C :: nil) = 2 /\ rk(A :: D :: nil) = 2 /\ rk(A :: E :: nil) = 2 /\rk(A :: F :: nil) = 2 /\ rk(A :: G :: nil) = 2 /\
rk(B :: C :: nil) = 2 /\ rk(B :: D :: nil) = 2 /\ rk(B :: E :: nil) = 2 /\ rk(B :: F :: nil) = 2 /\ rk(B :: G :: nil) = 2 /\
rk(C :: D :: nil) = 2 /\ rk(C :: E :: nil) = 2 /\ rk(C :: F :: nil) = 2 /\ rk(C :: G :: nil) = 2 /\
rk(D :: E :: nil) = 2 /\ rk(D :: F :: nil) = 2 /\ rk(D :: G :: nil) = 2 /\
rk(E :: F :: nil) = 2 /\ rk(E :: G :: nil) = 2 /\
rk(F :: G :: nil) = 2 ->
~A = B /\ ~A = C /\ ~A = D /\ ~A = E /\ ~A = F /\ ~A = G /\
~B = C /\ ~B = D /\ ~B = E /\ ~B = F /\ ~B = G /\
~C = D /\ ~C = E /\ ~C = F /\ ~C = G /\
~D = E /\ ~D = F /\ ~D = G /\
~E = F /\ ~E = G /\
~F = G.
Proof.
intros.
my_split;repeat split;apply couple_rk1;assumption.
Qed.

Lemma triple_rk2rk3 : forall P Q R : Point,
~ P = Q -> ~ P = R -> ~ Q = R -> rk(P :: Q ::  R :: nil) = 2 \/ rk(P :: Q :: R :: nil) = 3.
Proof.
intros.
assert(HH0 := rk_couple_ge P Q H).
assert(HH1 := rk_triple_max_3 P Q R).
apply le_lt_or_eq in HH1.
destruct HH1.
assert(HH2 : incl (P :: Q :: nil) (P :: Q :: R :: nil));[my_inO|].
assert(HH3 := matroid2 (P :: Q :: nil) (P :: Q :: R :: nil) HH2).
omega.
omega.
Qed.

Lemma triple_distinct_rk3 : forall P Q R S : Point, 
~ P = Q -> ~ P = R -> ~ P = S -> 
~ Q = R -> ~ Q = S -> ~ R = S -> 
rk(P :: Q :: R :: nil) = 2 ->
rk(P :: Q :: S :: nil) = 3.
Proof.
intros P Q R S H H0 H1 H2 H3 H4 HH0.
generalize rk_planes;intro HH;use HH.
case_clear_1 P;subst;
case_clear_1 Q;subst;
try equal_degens;
case_clear_1 R;subst;
try equal_degens;
try solve[rk_triple_3_2_bis_bis];
case_clear_1 S;subst;
try equal_degens;
try solve[rk_triple_bis_bis].
Qed.

Lemma quadruple_distinct_rk3 : forall P Q R S : Point, 
~ P = Q -> ~ P = R -> ~ P = S -> 
~ Q = R -> ~ Q = S -> ~ R = S -> rk(P :: Q :: R :: S :: nil) = 3.
Proof.
intros.
assert(HH0 := triple_rk2rk3 P Q R H H0 H2).
destruct HH0.
assert(HH1 := triple_distinct_rk3 P Q R S H H0 H1 H2 H3 H4 H5).
assert(HH2 := rk_quadruple_max_3 P Q R S).
destruct HH1.
assert(HH3 : incl (P :: Q :: S :: nil) (P :: Q :: R :: S :: nil));[my_inO|].
assert(HH4 := matroid2 (P :: Q :: S :: nil) (P :: Q :: R :: S :: nil) HH3).
omega.
assert(HH0 : incl (P :: Q :: R :: nil) (P :: Q :: R :: S :: nil));[my_inO|].
assert(HH1 := matroid2 (P :: Q :: R :: nil) (P :: Q :: R :: S :: nil) HH0).
assert(HH2 := rk_quadruple_max_3 P Q R S).
omega.
Qed.


Lemma quadruple_distinct_rk3_to_false : forall P Q R S : Point,
~ P = Q -> ~ P = R -> ~ P = S -> 
~ Q = R -> ~ Q = S -> ~ R = S -> rk(P :: Q :: R :: S :: nil) = 2 -> False.
Proof.
intros.
assert(HH := quadruple_distinct_rk3 P Q R S H H0 H1 H2 H3 H4).
rewrite H5 in HH.
omega.
Qed.

Lemma not_all_rk_equal : forall P Q R : Point, ~(rk(P :: P :: nil) = 2  \/ rk(Q :: Q :: nil) = 2 \/ rk(R :: R :: nil) = 2).
Proof.
intros P Q R H0; intuition.
assert(HH := couple_rk1 P P H);intuition.
assert(HH := couple_rk1 Q Q H0);intuition.
assert(HH := couple_rk1 R R H0);intuition.
Qed.


(*
Lemma not_at_least_two_rk_equal_from_P : forall P Q R P' : Point, 
~(rk(P :: P' :: nil) = 2 /\ rk(Q :: Q :: nil) = 2 \/ 
rk(P :: P' :: nil) = 2 /\ rk(R :: R :: nil) = 2 \/ 
rk(Q :: Q :: nil) = 2 /\ rk(R :: R :: nil) = 2).
Proof.
intros P Q R R' H0; intuition.
assert(HH := couple_rk1 Q Q H1);my_inA.
assert(HH := couple_rk1 R R H1);my_inA.
assert(HH := couple_rk1 Q Q H);my_inA.
Qed.

Lemma not_at_least_two_rk_equal_from_Q : forall P Q R Q' : Point, 
~(rk(P :: P :: nil) = 2 /\ rk(Q :: Q' :: nil) = 2 \/ 
rk(P :: P :: nil) = 2 /\ rk(R :: R :: nil) = 2 \/ 
rk(Q :: Q' :: nil) = 2 /\ rk(R :: R :: nil) = 2).
Proof.
intros P Q R R' H0; intuition.
assert(HH := couple_rk1 P P H0);my_inA.
assert(HH := couple_rk1 P P H);my_inA.
assert(HH := couple_rk1 R R H1);my_inA.
Qed.

Lemma not_at_least_two_rk_equal_from_R : forall P Q R R' : Point, 
~(rk(P :: P :: nil) = 2 /\ rk(Q :: Q :: nil) = 2 \/ 
rk(P :: P :: nil) = 2 /\ rk(R :: R' :: nil) = 2 \/ 
rk(Q :: Q :: nil) = 2 /\ rk(R :: R' :: nil) = 2).
Proof.
intros P Q R R' H0; intuition.
assert(HH := couple_rk1 P P H0);my_inA.
assert(HH := couple_rk1 P P H);my_inA.
assert(HH := couple_rk1 Q Q H);my_inA.
Qed.
*)

Ltac degens_rk2 := 
try solve[apply triple_rk2_1;assumption];
try solve[apply triple_rk2_2;assumption];
try solve[apply triple_rk2_3;assumption].

Ltac degens_rk3 := 
match goal with
| H: rk(?P :: ?P :: nil) = 2  \/ rk(?Q :: ?Q :: nil) = 2 \/ rk(?R :: ?R :: nil) = 2 |- _ => elim (not_all_rk_equal P Q R H)
| H: rk(?P :: ?P :: ?R :: nil) = 3 |- _ => elim (col_degen_1 P R H)
| H: rk(?P :: ?R :: ?P :: nil) = 3 |- _ => elim (col_degen_2 P R H)
| H: rk(?R :: ?P :: ?P :: nil) = 3 |- _ => elim (col_degen_3 P R H)
end.

(*
Ltac degens_rk3_alt := 
match goal with
| H: rk(?P :: ?P' :: nil) = 2 /\ rk(?Q :: ?Q :: nil) = 2 \/ rk(?P :: ?P' :: nil) = 2 /\ rk(?R :: ?R :: nil) = 2 \/ rk(?Q :: ?Q :: nil) = 2 /\ rk(?R :: ?R :: nil) = 2 |- _ => elim (not_at_least_two_rk_equal_from_P P Q R P' H)
| H: rk(?P :: ?P :: nil) = 2 /\ rk(?Q :: ?Q' :: nil) = 2 \/ rk(?P :: ?P :: nil) = 2 /\ rk(?R :: ?R :: nil) = 2 \/ rk(?Q :: ?Q' :: nil) = 2 /\ rk(?R :: ?R :: nil) = 2 |- _ => elim (not_at_least_two_rk_equal_from_Q P Q R Q' H)
| H: rk(?P :: ?P :: nil) = 2 /\ rk(?Q :: ?Q :: nil) = 2 \/ rk(?P :: ?P :: nil) = 2 /\ rk(?R :: ?R' :: nil) = 2 \/ rk(?Q :: ?Q :: nil) = 2 /\ rk(?R :: ?R' :: nil) = 2 |- _ => elim (not_at_least_two_rk_equal_from_R P Q R R' H)
| H: rk(?P :: ?P :: ?R :: nil) = 3 |- _ => elim (col_degen_1 P R H)
| H: rk(?P :: ?R :: ?P :: nil) = 3 |- _ => elim (col_degen_2 P R H)
| H: rk(?R :: ?P :: ?P :: nil) = 3 |- _ => elim (col_degen_3 P R H)
end.
*)

Ltac rk_quadruple_simplification P:=
repeat match goal with
| H : rk(P :: ?X :: ?Y :: ?Z :: nil) = 2 |- _ => let HH := fresh in
assert(HH : rk(P :: X :: Y :: Z :: nil) = 3) by (apply (quadruple_distinct_rk3 P X Y Z);assumption);
rewrite H in HH;inversion HH
end.

Ltac case_clear_2 P :=
  case_clear_1 P;
  match goal with
| H : P = ?X |- _ => subst;clear H;try solve[degens_rk3];try solve[rk_quadruple_simplification X]
end.

Ltac case_clear_3 P := case_clear_1 P;subst;try solve[rk_triple_2_3_bis_bis].

Ltac clear_rk2 :=
repeat match goal with
| H : rk _ = 2 |- _ => clear H
end.

Ltac clear_rk3 :=
repeat match goal with
| H : rk _ = 3 |- _ => clear H
end.

Ltac clear_rk :=
repeat match goal with
| H : rk _ = _ |- _ => clear H
end.

Ltac clear_neq :=
repeat match goal with
| H : _ <> _ |- _ => clear H
end.

Ltac case_clear_P1 P Q R :=
case_clear_2 P;
case_clear_2 Q;
case_clear_2 R;
try solve[rk_triple_3_2_bis_bis].

Ltac case_clear_P2 P Q R :=
case_clear_2 P;
case_clear_2 Q;
case_clear_2 R;
try solve[rk_triple_3_2_bis_bis].

Ltac case_clear_P3 P Q R := 
case_clear_1 P;subst;try solve[rk_triple_2_3_bis_bis];
case_clear_1 Q;subst;try solve[rk_triple_2_3_bis_bis];
case_clear_1 R;subst;try solve[rk_triple_2_3_bis_bis];
clear_rk3;degens_rk2;clear_neq;rk_triple_bis_bis.

Ltac case_clear_P2_P3 P Q R P' Q' R' :=
case_clear_P2 P Q R;
case_clear_P3 P' Q' R'.

Lemma Desargues_from_A_spec :  forall P Q R P' Q' R' alpha beta gamma,
rk(P :: Q :: gamma :: nil) = 2 -> rk(P' :: Q' :: gamma :: nil) = 2 ->
rk(P :: R :: beta :: nil) = 2 -> rk(P' :: R' :: beta :: nil) = 2 ->
rk(Q :: R :: alpha :: nil) = 2 -> rk(Q' :: R' :: alpha :: nil) = 2 ->
rk(P :: A :: D :: G :: nil) = 2 -> rk(P' :: A :: D :: G :: nil) = 2 -> 
rk(Q :: A :: C :: E :: nil) = 2 -> rk(Q' :: A :: C :: E :: nil) = 2 -> 
rk(R :: A :: B :: F :: nil) = 2 -> rk(R' :: A :: B :: F :: nil) = 2 ->
rk(A :: P :: P' :: nil) = 2 -> rk(A :: Q :: Q' :: nil) = 2 -> rk(A :: R :: R' :: nil) = 2 ->
rk(A :: P :: Q :: nil) = 3 -> rk(A :: P :: R :: nil) = 3 -> rk(A :: Q :: R :: nil) = 3 ->
rk(P :: Q :: R :: nil) = 3 -> rk(P' :: Q' :: R' :: nil) = 3 -> 
(rk(P :: P' :: nil) = 2 \/ rk(Q :: Q' :: nil) = 2 \/ rk(R :: R' :: nil) = 2) ->
rk(alpha :: beta :: gamma :: nil) = 2.
Proof.
intros.
assert(HH0 := rk_distinct_points).
assert(HH := rk_distinct HH0);clear HH0;my_split;eq_duplicate;my_split.
generalize rk_lines;intro HH;use HH;
generalize rk_planes;intro HH;use HH.
case_clear_2 P;
case_clear_2 Q;
case_clear_2 R;try solve[rk_triple_2_3_bis_bis];
case_clear_2 P';
case_clear_2 Q';
case_clear_2 R';try solve[rk_triple_2_3_bis_bis];
case_clear_3 alpha;
case_clear_3 beta;
case_clear_3 gamma;
clear H H0;
clear_rk3;
degens_rk2;
clear_neq;
rk_couple_triple.
Qed.

Ltac case_clear_4 P := case_clear_1 P;subst;try solve[equal_degens];try solve[rk_triple_2_3_bis_bis].

Lemma degens_or : forall P P' Q Q' R R', rk(P :: P' :: nil) = 2 \/ rk(Q :: Q' :: nil) = 2 \/ rk(R :: R' :: nil) = 2 ->
(rk(P :: P' :: nil) = 2 \/ rk(R :: R' :: nil) = 2 \/ rk(Q :: Q' :: nil) = 2) /\
(rk(Q :: Q' :: nil) = 2 \/ rk(P :: P' :: nil) = 2 \/ rk(R :: R' :: nil) = 2) /\
(rk(Q :: Q' :: nil) = 2 \/ rk(R :: R' :: nil) = 2 \/ rk(P :: P' :: nil) = 2) /\
(rk(R :: R' :: nil) = 2 \/ rk(P :: P' :: nil) = 2 \/ rk(Q :: Q' :: nil) = 2) /\
(rk(R :: R' :: nil) = 2 \/ rk(Q :: Q' :: nil) = 2 \/ rk(P :: P' :: nil) = 2).
Proof.
intros;intuition.
Qed.

Ltac rk_quadruple_fixe :=
repeat match goal with
| H : rk(?P :: ?A :: ?B :: ?C :: nil) = _ |- rk(?P :: ?A :: ?B :: ?C :: nil) = _ => assumption
| H : rk(?P :: ?A :: ?B :: ?C :: nil) = _ |- rk(?P :: ?A :: ?C :: ?B :: nil) = _ => rewrite <-quadruple_permut_1;assumption
end.

Ltac solve_desargues_from_A_spec P Q R P' Q' R' alpha beta gamma HH HH0 HH1 HH2 HH3 HH4:=
match goal with
| H : rk(P :: A :: D :: G :: nil) = 2 |- _ => match goal with
                                  | H : rk(Q :: A :: C :: E :: nil) = 2 |- _ => try solve[apply Desargues_from_A_spec with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                                                try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quadruple_fixe]]
                                  | H : rk(Q :: A :: E :: C :: nil) = 2 |- _ => try solve[apply Desargues_from_A_spec with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                                                try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quadruple_fixe]]
                                  | H : rk(Q :: A :: B :: F :: nil) = 2 |- _ => try solve[rewrite HH;apply Desargues_from_A_spec with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                                                try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quadruple_fixe]]
                                  | H : rk(Q :: A :: F :: B :: nil) = 2 |- _ => try solve[rewrite HH;apply Desargues_from_A_spec with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                                                try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quadruple_fixe]]
                                  end
| H : rk(P :: A :: G :: D :: nil) = 2 |- _ => match goal with
                                  | H : rk(Q :: A :: C :: E :: nil) = 2 |- _ => try solve[apply Desargues_from_A_spec with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                                                try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quadruple_fixe]]
                                  | H : rk(Q :: A :: E :: C :: nil) = 2 |- _ => try solve[apply Desargues_from_A_spec with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                                                try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quadruple_fixe]]
                                  | H : rk(Q :: A :: B :: F :: nil) = 2 |- _ => try solve[rewrite HH;apply Desargues_from_A_spec with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                                                try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quadruple_fixe]]
                                  | H : rk(Q :: A :: F :: B :: nil) = 2 |- _ => try solve[rewrite HH;apply Desargues_from_A_spec with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                                                try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quadruple_fixe]]
                                  end
| H : rk(P :: A :: C :: E :: nil) = 2 |- _ => match goal with
                                  | H : rk(Q :: A :: D :: G :: nil) = 2 |- _ => try solve[rewrite HH0;apply Desargues_from_A_spec with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                                                try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quadruple_fixe]]
                                  | H : rk(Q :: A :: G :: D :: nil) = 2 |- _ => try solve[rewrite HH0;apply Desargues_from_A_spec with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                                                try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quadruple_fixe]]
                                  | H : rk(Q :: A :: B :: F :: nil) = 2 |- _ => try solve[rewrite HH2;apply Desargues_from_A_spec with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                                                try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quadruple_fixe]]
                                  | H : rk(Q :: A :: F :: B :: nil) = 2 |- _ => try solve[rewrite HH2;apply Desargues_from_A_spec with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                                                try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quadruple_fixe]]
                                  end
| H : rk(P :: A :: E :: C :: nil) = 2 |- _ => match goal with
                                  | H : rk(Q :: A :: D :: G :: nil) = 2 |- _ => try solve[rewrite HH0;apply Desargues_from_A_spec with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                                                try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quadruple_fixe]]
                                  | H : rk(Q :: A :: G :: D :: nil) = 2 |- _ => try solve[rewrite HH0;apply Desargues_from_A_spec with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                                                try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quadruple_fixe]]
                                  | H : rk(Q :: A :: B :: F :: nil) = 2 |- _ => try solve[rewrite HH2;apply Desargues_from_A_spec with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                                                try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quadruple_fixe]]
                                  | H : rk(Q :: A :: F :: B :: nil) = 2 |- _ => try solve[rewrite HH2;apply Desargues_from_A_spec with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                                                try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quadruple_fixe]]
                                  end
| H : rk(P :: A :: B :: F :: nil) = 2 |- _ => match goal with
                                  | H : rk(Q :: A :: D :: G :: nil) = 2 |- _ => try solve[rewrite HH1;apply Desargues_from_A_spec with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                                                try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quadruple_fixe]]
                                  | H : rk(Q :: A :: G :: D :: nil) = 2 |- _ => try solve[rewrite HH1;apply Desargues_from_A_spec with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                                                try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quadruple_fixe]]
                                  | H : rk(Q :: A :: C :: E :: nil) = 2 |- _ => try solve[rewrite HH3;apply Desargues_from_A_spec with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                                                try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quadruple_fixe]]
                                  | H : rk(Q :: A :: E :: C :: nil) = 2 |- _ => try solve[rewrite HH3;apply Desargues_from_A_spec with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                                                try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quadruple_fixe]]
                                  end
| H : rk(P :: A :: F :: B :: nil) = 2 |- _ => match goal with
                                  | H : rk(Q :: A :: D :: G :: nil) = 2 |- _ => try solve[rewrite HH1;apply Desargues_from_A_spec with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                                                try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quadruple_fixe]]
                                  | H : rk(Q :: A :: G :: D :: nil) = 2 |- _ => try solve[rewrite HH1;apply Desargues_from_A_spec with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                                                try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quadruple_fixe]]
                                  | H : rk(Q :: A :: C :: E :: nil) = 2 |- _ => try solve[rewrite HH3;apply Desargues_from_A_spec with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                                                try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quadruple_fixe]]
                                  | H : rk(Q :: A :: E :: C :: nil) = 2 |- _ => try solve[rewrite HH3;apply Desargues_from_A_spec with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                                                try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quadruple_fixe]]
                                  end
end.

Lemma Desargues_from_A :  forall X Y X' Y' X'' Y'' P Q R P' Q' R' alpha beta gamma,
~ A = X -> ~ A = Y -> ~ X = Y ->
~ A = X' -> ~ A = Y' -> ~ X' = Y' ->
~ A = X'' -> ~ A = Y'' -> ~X'' = Y'' ->
~ X = X' -> ~ X = X'' -> ~ X' = X'' ->
~ Y = Y' -> ~ Y = Y'' -> ~ Y' = Y'' ->
~ X = Y' -> ~ X = Y'' ->
~ X' = Y -> ~ X' = Y'' ->
~ X'' = Y -> ~ X'' = Y' ->
rk(A :: X :: Y :: nil) = 2 -> rk(A :: X' :: Y' :: nil) = 2 -> rk(A :: X'' :: Y'' :: nil) = 2 ->
rk(P :: Q :: gamma :: nil) = 2 -> rk(P' :: Q' :: gamma :: nil) = 2 ->
rk(P :: R :: beta :: nil) = 2 -> rk(P' :: R' :: beta :: nil) = 2 ->
rk(Q :: R :: alpha :: nil) = 2 -> rk(Q' :: R' :: alpha :: nil) = 2 ->
rk(P :: A :: X :: Y :: nil) = 2 -> rk(P' :: A :: X :: Y :: nil) = 2 ->
rk(Q :: A :: X' :: Y' :: nil) = 2 -> rk(Q' :: A :: X' :: Y' :: nil) = 2 ->
rk(R :: A :: X'' :: Y'' :: nil) = 2 -> rk(R' :: A :: X'' :: Y'' :: nil) = 2 ->
rk(A :: P :: P' :: nil) = 2 -> rk(A :: Q :: Q' :: nil) = 2 -> rk(A :: R :: R' :: nil) = 2 ->
rk(A :: P :: Q :: nil) = 3 -> rk(A :: P :: R :: nil) = 3 -> rk(A :: Q :: R :: nil) = 3 ->
rk(P :: Q :: R :: nil) = 3 -> rk(P' :: Q' :: R' :: nil) = 3 -> (rk(P :: P' :: nil) = 2 \/ rk(Q :: Q' :: nil) = 2 \/ rk(R :: R' :: nil) = 2) ->
rk(alpha :: beta :: gamma :: nil) = 2.
Proof.
intros X Y X' Y' X'' Y'' P Q R P' Q' R' alpha beta gamma.
assert(HH : equivlist (alpha :: beta :: gamma :: nil) (alpha :: gamma :: beta :: nil));[my_inO|].
assert(HH0 : equivlist (alpha :: beta :: gamma :: nil) (beta :: alpha :: gamma :: nil));[my_inO|].
assert(HH1 : equivlist (alpha :: beta :: gamma :: nil) (beta :: gamma :: alpha :: nil));[my_inO|].
assert(HH2 : equivlist (alpha :: beta :: gamma :: nil) (gamma :: alpha :: beta :: nil));[my_inO|].
assert(HH3 : equivlist (alpha :: beta :: gamma :: nil) (gamma :: beta :: alpha :: nil));[my_inO|].
intros.
generalize rk_planes;intro HH5;use HH5.
assert(HH4 := degens_or P P' Q Q' R R' H43);my_split.
case_clear_4 X;
case_clear_4 Y;
case_clear_4 X';
case_clear_4 Y';
case_clear_4 X'';
case_clear_4 Y'';
clear H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 
H44 H45 H46 H47 H48 H49 H50 H51 H52 H53 H54 H55 H56 H57 H58 H59 H60 H61 H62 H63
H64 H65 H66 H67 H68 H69 H70 H72;
solve_desargues_from_A_spec P Q R P' Q' R' alpha beta gamma HH HH0 HH1 HH2 HH3 HH4.
Qed.

End Desargues_from_A.


Module Desargues (M:fano_plane_rank).

Import M.

Module Import M2:= Desargues_from_A M.

Module swaped_B := swapfr3 M.
Module swaped_B' := Desargues_from_A swaped_B.
Module swaped_E := swapfr3 swaped_B.
Module swaped_E' := Desargues_from_A swaped_E.
Module swaped_C := swapfr3 swaped_E.
Module swaped_C' := Desargues_from_A swaped_C.
Module swaped_D := swapfr3 swaped_C.
Module swaped_D' := Desargues_from_A swaped_D.
Module swaped_F := swapfr3 swaped_D.
Module swaped_F' := Desargues_from_A swaped_F.
Module swaped_G := swapfr3 swaped_F.
Module swaped_G' := Desargues_from_A swaped_G.

Theorem Desargues : 
forall O X Y X' Y' X'' Y'' P Q R P' Q' R' alpha beta gamma,
~ O = X /\ ~ O = Y /\ ~ X = Y /\ 
~ O = X' /\ ~ O = Y' /\ ~ X' = Y' /\ 
~ O = X'' /\ ~ O = Y'' /\ ~X'' = Y'' /\ 
~ X = X' /\ ~ X = X'' /\ ~ X' = X'' /\
~ Y = Y' /\ ~ Y = Y'' /\ ~ Y' = Y'' /\
~ X = Y' /\ ~ X = Y'' /\
~ X' = Y /\ ~ X' = Y'' /\
~ X'' = Y /\ ~ X'' = Y' /\
rk(O :: X :: Y :: nil) = 2 /\ rk(O :: X' :: Y' :: nil) = 2 /\ rk(O :: X'' :: Y'' :: nil) = 2 /\ 
rk(P :: Q :: gamma :: nil) = 2 /\ rk(P' :: Q' :: gamma :: nil) = 2 /\
rk(P :: R :: beta :: nil) = 2 /\ rk(P' :: R' :: beta :: nil) = 2 /\
rk(Q :: R :: alpha :: nil) = 2 /\ rk(Q' :: R' :: alpha :: nil) = 2 /\
rk(O :: P :: P' :: nil) = 2 /\ rk(O :: Q :: Q' :: nil) = 2 /\ rk(O :: R :: R' :: nil) = 2 /\
rk(P :: O :: X :: Y :: nil) = 2 /\ rk(P' :: O :: X :: Y :: nil) = 2 /\ 
rk(Q :: O :: X' :: Y' :: nil) = 2 /\ rk(Q' :: O :: X' :: Y' :: nil) = 2 /\ 
rk(R :: O :: X'' :: Y'' :: nil) = 2 /\ rk(R' :: O :: X'' :: Y'' :: nil) = 2 /\
rk(O :: P :: Q :: nil) = 3 /\ rk(O :: P :: R :: nil) = 3 /\ rk(O :: Q :: R :: nil) = 3 /\
rk(P :: Q :: R :: nil) = 3 /\ rk(P' :: Q' :: R' :: nil) = 3 /\ (rk(P :: P' :: nil) = 2 \/ rk(Q :: Q' :: nil) = 2 \/ rk(R :: R' :: nil) = 2) ->
rk(alpha :: beta :: gamma :: nil) = 2.
Proof.
intros.
my_split.
case_clear_1 O.
rewrite a0 in *.
apply (Desargues_from_A X Y X' Y' X'' Y'' P Q R P' Q' R' alpha beta gamma);assumption.

rewrite b in *.
assert(T:=swaped_B'.Desargues_from_A ).
unfold swaped_B.A in *.
eapply (T X Y X' Y' X'' Y'' P Q R P' Q' R' alpha beta gamma);assumption.

rewrite b in *.
assert(T:=swaped_C'.Desargues_from_A ).
unfold swaped_C.A in *.
eapply (T X Y X' Y' X'' Y'' P Q R P' Q' R' alpha beta gamma);assumption.

rewrite b in *.
assert(T:=swaped_D'.Desargues_from_A ).
unfold swaped_D.A in *.
eapply (T X Y X' Y' X'' Y'' P Q R P' Q' R' alpha beta gamma);assumption.

rewrite b in *.
assert(T:=swaped_E'.Desargues_from_A ).
unfold swaped_E.A in *.
eapply (T X Y X' Y' X'' Y'' P Q R P' Q' R' alpha beta gamma);assumption.

rewrite b in *.
assert(T:=swaped_F'.Desargues_from_A ).
unfold swaped_F.A in *.
eapply (T X Y X' Y' X'' Y'' P Q R P' Q' R' alpha beta gamma);assumption.

rewrite b in *.
assert(T:=swaped_G'.Desargues_from_A ).
unfold swaped_G.A in *.
eapply (T X Y X' Y' X'' Y'' P Q R P' Q' R' alpha beta gamma);assumption.
Qed.

End Desargues.
