Require Export ProjectiveGeometry.Dev.basic_matroid_list.

Parameter rk_singleton_ge : forall P, rk (P :: nil)  >= 1.
Parameter rk_couple_ge : forall P Q, ~ P = Q -> rk(P :: Q :: nil) >= 2.
Parameter rk_three_points_on_lines : forall A B, exists C, rk (A :: B :: C :: nil) = 2 /\ rk (B :: C :: nil) = 2 /\ rk (A :: C :: nil) = 2.
Parameter rk_inter : forall A B C D, exists J, rk (A :: B :: J :: nil) = 2 /\ rk (C :: D :: J :: nil) = 2.
Parameter rk_lower_dim : exists P0 P1 P2, rk( P0 :: P1 :: P2 :: nil) >=3.

Lemma rk_singleton_1 : forall A, rk(A :: nil) <= 1.
Proof.
intros.
apply matroid1_b_useful.
intuition.
Qed.

Lemma rk_singleton : forall A, rk(A :: nil) = 1.
Proof.
intros.
assert(H := rk_singleton_ge A).
assert(HH := rk_singleton_1 A).
omega.
Qed.

Lemma rk_couple_2 : forall A B, rk(A :: B :: nil) <= 2.
Proof.
intros.
apply matroid1_b_useful.
intuition.
Qed.

Lemma rk_couple : forall A B : Point,~ A = B -> rk(A :: B :: nil) = 2.
Proof.
intros.
assert(HH := rk_couple_2 A B).
assert(HH0 := rk_couple_ge A B H).
omega.
Qed.

Lemma rk_triple_3 : forall A B C : Point, rk (A :: B :: C :: nil) <= 3.
Proof.
intros.
apply matroid1_b_useful.
intuition.
Qed.

Lemma couple_rk1 : forall A B, rk(A :: B :: nil) = 2 -> ~ A = B.
Proof.
intros.
intro.
rewrite H0 in H.
assert(HH : equivlist (B :: B :: nil) (B :: nil));[my_inA|].
rewrite HH in H.
assert(HH0 := rk_singleton_1 B).
omega.
Qed.

Lemma couple_rk2 : forall A B, rk(A :: B :: nil) = 1 -> A = B.
Proof.
intros.
case_eq(eq_dec A B).
intros.
assumption.
intros.
assert(HH := rk_couple A B n).
omega.
Qed.

Lemma rk_quadruple_inter_aux : forall A B C D E,
~ A = C ->
~ A = D ->
~ B = C ->
~ B = D -> 
rk(A :: B :: E :: nil) = 2 -> 
rk(C :: D :: E :: nil) = 2 ->
rk(A :: B :: C :: D :: nil) = 2 \/ rk(A :: B :: C :: D :: nil) = 3.
Proof.
intros.

assert (HH0 : rk((A :: B :: E :: nil) ++ (C :: D :: E :: nil)) + rk(list_inter (A :: B :: E :: nil) (C :: D :: E :: nil)) <=
       rk(A :: B :: E :: nil) + rk(C :: D :: E :: nil)).
apply matroid3_useful;my_inA.
assert(HH1 : equivlist (list_inter (A :: B :: E :: nil) (C :: D :: E :: nil))  (E :: nil)).
my_inA_inter.
assert(HH2 := rk_singleton E).
rewrite HH1 in HH0.
rewrite HH2 in HH0.
rewrite H3 in HH0.
rewrite H4 in HH0.

assert(HH3 : rk(A :: B :: E :: C :: D :: E :: nil) = 2 \/ rk(A :: B :: E :: C :: D :: E :: nil) = 3).
apply le_lt_or_eq in HH0;simpl in HH0.
destruct HH0.
assert(HH4 : rk(A :: B :: E :: C :: D :: E :: nil) < 3).
solve[intuition].
assert(HH5 : incl (A :: B :: E :: nil) (A :: B :: E :: C :: D :: E :: nil));[my_inA|].
assert(HH6 := matroid2 (A :: B :: E :: nil) (A :: B :: E :: C :: D :: E :: nil) HH5).
omega.
omega.

destruct HH3.

assert(HH3 := rk_couple A C H).
assert(HH4 : incl (A :: C :: nil) (A :: B :: C :: D :: nil));[my_inA|].
assert(HH5 : incl (A :: B :: C :: D :: nil) (A :: B :: E :: C :: D :: E :: nil));[my_inA|].
assert(HH6 := matroid2 (A :: C :: nil) (A :: B :: C :: D :: nil) HH4).
assert(HH7 := matroid2 (A :: B :: C :: D :: nil) (A :: B :: E :: C :: D :: E :: nil) HH5).
omega.

assert(HH3 : incl (A :: B :: C :: D :: nil) (A :: B :: E :: C :: D :: E :: nil));[my_inA|].
assert(HH4 := matroid2 (A :: B :: C :: D :: nil) (A :: B :: E :: C :: D :: E :: nil) HH3).
rewrite H5 in HH4.
apply le_lt_or_eq in HH4.
destruct HH4.
assert(HH5 := rk_couple A C H).
assert(HH6 : incl (A :: C :: nil) (A :: B :: C :: D :: nil));[my_inA|].
assert(HH7 := matroid2 (A :: C :: nil) (A :: B :: C :: D :: nil) HH6).
omega.
omega.
Qed.

Lemma rk_quadruple_inter_aux2 : forall B C D E,
~ B = C ->
~ B = D -> 
rk(D :: B :: E :: nil) = 2 -> 
rk(C :: D :: E :: nil) = 2 ->
rk(D :: B :: C :: D :: nil) = 2 \/ rk(D :: B :: C :: D :: nil) = 3.
Proof.
intros.

assert (HH0 : rk((D :: B :: E :: nil) ++ (C :: D :: E :: nil)) + rk(list_inter (D :: B :: E :: nil) (C :: D :: E :: nil)) <=
       rk(D :: B :: E :: nil) + rk(C :: D :: E :: nil)).
apply matroid3_useful;my_inA.
assert (HH1 : equivlist (list_inter (D :: B :: E :: nil) (C :: D :: E :: nil)) (D :: E :: nil));[my_inA_inter|].
rewrite HH1 in HH0.
case_eq(eq_dec D E).
intros;subst.
rewrite H1 in HH0;rewrite H2 in HH0.
assert(HH2 : equivlist (E :: E :: nil) (E :: nil));[my_inA|].
replace (rk (E :: E :: nil)) with (rk(E :: nil)) in HH0.
2:rewrite HH2;intuition.
assert(HH3 := rk_singleton E).
rewrite HH3 in HH0.

assert(HH4 : rk(E :: B :: E :: C :: E :: E :: nil) = 2 \/ rk((E :: B :: E :: C :: E :: E :: nil)) = 3).
apply le_lt_or_eq in HH0;simpl in HH0.
destruct HH0.
assert(HH5 : rk((E :: B :: E :: C :: E :: E :: nil)) < 3).
solve[intuition].
assert(HH4 : incl (E :: B :: E :: nil) (E :: B :: E :: C :: E :: E :: nil));[my_inA|].
assert(HH6 := matroid2 (E :: B :: E :: nil) (E :: B :: E :: C :: E :: E :: nil) HH4).
omega.
omega.

assert(HH5 : equivlist (E :: B :: E :: C :: E :: E :: nil) (E :: B :: C :: E :: nil));[my_inA|].
rewrite HH5 in HH4.
omega.

intros.
rewrite H1 in HH0;rewrite H2 in HH0.
assert(HH2 := rk_couple D E n).
rewrite HH2 in HH0.
assert(HH3 : rk((D :: B :: E :: nil) ++ (C :: D :: E :: nil)) = 2).
assert(HH4 : incl (D :: E :: nil) ((D :: B :: E :: nil) ++ (C :: D :: E :: nil)));[my_inA|].
assert(HH5 := matroid2 (D :: E :: nil) ((D :: B :: E :: nil) ++ (C :: D :: E :: nil)) HH4). 
omega.
assert(HH4 := rk_couple B C H).
assert(HH5 : incl (B :: C :: nil) (D :: B :: C :: D :: nil));[my_inA|].
assert(HH6 := matroid2 (B :: C :: nil) (D :: B :: C :: D :: nil) HH5).
assert(HH7 : incl (D :: B :: C :: D :: nil) ((D :: B :: E :: nil) ++ (C :: D :: E :: nil)));[my_inA|].
assert(HH8 := matroid2 (D :: B :: C :: D :: nil) ((D :: B :: E :: nil) ++ (C :: D :: E :: nil)) HH7).
omega.
Qed.

Lemma rk_quadruple_inter : forall A B C D E,
rk(A :: B :: E :: nil) = 2 -> 
rk(C :: D :: E :: nil) = 2 ->
rk(A :: B :: C :: D :: nil) = 1 \/ rk(A :: B :: C :: D :: nil) = 2 \/ rk(A :: B :: C :: D :: nil) = 3.
Proof.
intros.
case_eq(eq_dec A C);
case_eq(eq_dec A D);
case_eq(eq_dec B C);
case_eq(eq_dec B D).

intros.
rewrite e;rewrite e1.
case_eq(eq_dec C D).
intros;rewrite e3.
assert(HH0 : equivlist (D :: D :: D :: D :: nil) (D :: nil));[my_inA|].
rewrite HH0;assert(HH1 := rk_singleton D);omega.
intros.
assert(HH0 := rk_couple C D n);assert(HH : equivlist (D :: D :: C :: D :: nil) (C :: D :: nil));[my_inA|].
rewrite HH;omega.

intros.
rewrite e;rewrite e1.
case_eq(eq_dec C D).
intros;rewrite e2.
assert(HH0 : equivlist (D :: D :: D :: D :: nil) (D :: nil));[my_inA|].
rewrite HH0;assert(HH1 := rk_singleton D);omega.
intros.
assert(HH0 := rk_couple C D n0);assert(HH : equivlist (C :: C :: C :: D :: nil) (C :: D :: nil));[my_inA|].
rewrite HH;omega.

intros.
rewrite e;rewrite e1.
case_eq(eq_dec C D).
intros;rewrite e2.
assert(HH0 : equivlist (D :: D :: D :: D :: nil) (D :: nil));[my_inA|].
rewrite HH0;assert(HH1 := rk_singleton D);omega.
intros.
assert(HH0 := rk_couple C D n0);assert(HH : equivlist (C :: D :: C :: D :: nil) (C :: D :: nil));[my_inA|].
rewrite HH;omega.

intros.
rewrite e in *.
assert(HH0 := rk_quadruple_inter_aux2 B C D E n0 n H H0).
omega.

intros.
rewrite e0;rewrite e1.
case_eq(eq_dec C D).
intros;rewrite e2.
assert(HH0 : equivlist (D :: D :: D :: D :: nil) (D :: nil));[my_inA|].
rewrite HH0;assert(HH1 := rk_singleton D);omega.
intros.
assert(HH0 := rk_couple C D n0);assert(HH : equivlist (C :: C :: C :: D :: nil) (C :: D :: nil));[my_inA|].
rewrite HH;omega.

intros.
rewrite e;rewrite e0.
case_eq(eq_dec C D).
intros;rewrite e1.
assert(HH0 : equivlist (D :: D :: D :: D :: nil) (D :: nil));[my_inA|].
rewrite HH0;assert(HH1 := rk_singleton D);omega.
intros.
assert(HH0 := rk_couple C D n1);assert(HH : equivlist (C :: C :: C :: D :: nil) (C :: D :: nil));[my_inA|].
rewrite HH;omega.

intros.
rewrite e;rewrite e0.
case_eq(eq_dec C D).
intros;rewrite e1.
assert(HH0 : equivlist (D :: D :: D :: D :: nil) (D :: nil));[my_inA|].
rewrite HH0;assert(HH1 := rk_singleton D);omega.
intros.
assert(HH0 := rk_couple C D n1);assert(HH : equivlist (C :: D :: C :: D :: nil) (C :: D :: nil));[my_inA|].
rewrite HH;omega.

intros.
rewrite e in *.
assert(HH0 : equivlist (C :: D :: E :: nil) (D :: C :: E :: nil));[my_inA|].
rewrite HH0 in H0.
assert(HH1 := rk_quadruple_inter_aux2 B D C E n n0 H H0).
assert(HH2 : equivlist (C :: B :: C :: D :: nil) (C :: B :: D :: C :: nil));[my_inA|].
rewrite HH2.
omega.

intros.
rewrite e;rewrite e1.
case_eq(eq_dec C D).
intros;rewrite e2.
assert(HH0 : equivlist (D :: D :: D :: D :: nil) (D :: nil));[my_inA|].
rewrite HH0;assert(HH1 := rk_singleton D);omega.
intros.
assert(HH0 := rk_couple C D n0);assert(HH : equivlist (D :: D :: C :: D :: nil) (C :: D :: nil));[my_inA|].
rewrite HH;omega.

intros.
rewrite e;rewrite e0.
case_eq(eq_dec C D).
intros;rewrite e1.
assert(HH0 : equivlist (D :: D :: D :: D :: nil) (D :: nil));[my_inA|].
rewrite HH0;assert(HH1 := rk_singleton D);omega.
intros.
assert(HH0 := rk_couple C D n1);assert(HH : equivlist (D :: C :: C :: D :: nil) (C :: D :: nil));[my_inA|].
rewrite HH;omega.

intros.
rewrite e;rewrite e0.
case_eq(eq_dec C D).
intros;rewrite e1.
assert(HH0 : equivlist (D :: D :: D :: D :: nil) (D :: nil));[my_inA|].
rewrite HH0;assert(HH1 := rk_singleton D);omega.
intros.
assert(HH0 := rk_couple C D n1);assert(HH : equivlist (D :: D :: C :: D :: nil) (C :: D :: nil));[my_inA|].
rewrite HH;omega.

intros.
rewrite e in *.
assert(HH0 := rk_quadruple_inter_aux2 B C D E n0 n H H0).
omega.

intros.
rewrite e in  *.
assert(HH0 : equivlist (A :: D :: E :: nil) (D :: A :: E :: nil));[my_inA|].
rewrite HH0 in H.
assert(HH1 := rk_quadruple_inter_aux2 A C D E n0 n H H0).
assert(HH2 : equivlist (D :: A :: C :: D :: nil) (A :: D :: C :: D :: nil));[my_inA|].
rewrite HH2 in HH1.
omega.

intros.
rewrite e in  *.
assert(HH0 : equivlist (A :: C :: E :: nil) (C :: A :: E :: nil));[my_inA|].
rewrite HH0 in H.
assert(HH1 : equivlist (C :: D :: E :: nil) (D :: C :: E :: nil));[my_inA|].
rewrite HH1 in H0.
assert(HH2 := rk_quadruple_inter_aux2 A D C E n0 n1 H H0).
assert(HH3 : equivlist (C :: A :: D :: C :: nil) (A :: C :: C :: D :: nil));[my_inA|].
rewrite HH3 in HH2.
omega.

intros.
rewrite e in *.
assert(HH0 : equivlist (A :: D :: E :: nil) (D :: A :: E :: nil));[my_inA|].
rewrite HH0 in H.
assert(HH1 := rk_quadruple_inter_aux2 A C D E n1 n0 H H0).
assert(HH2 : equivlist (A :: D :: C :: D :: nil) (D :: A :: C :: D :: nil));[my_inA|].
rewrite HH2.
omega.

intros.
assert(HH0 := rk_quadruple_inter_aux A B C D E n2 n1 n0 n H H0).
omega.
Qed.

Lemma rk_quadruple_max_3 : forall X Y Z W: Point,rk(X :: Y :: Z :: W :: nil) <= 3.
intros.
assert(HH0 := rk_inter X Y Z W).
destruct HH0.
destruct H.
assert(HH1 := rk_quadruple_inter X Y Z W x H H0).
omega.
Qed.

Lemma rk_quintuple_inter_aux : forall A B C D E,
~ A = C ->
~ A = D ->
~ B = C ->
~ B = D -> 
rk(A :: B :: E :: nil) = 2 -> 
rk(C :: D :: E :: nil) = 2 ->
rk(A :: B :: C :: D :: E :: nil) = 2 \/ rk(A :: B :: C :: D :: E :: nil) = 3.
Proof.
intros.

assert (HH0 : rk((A :: B :: E :: nil) ++ (C :: D :: E :: nil)) + rk(list_inter (A :: B :: E :: nil) (C :: D :: E :: nil)) <=
       rk(A :: B :: E :: nil) + rk(C :: D :: E :: nil)).
apply matroid3_useful;my_inA.
assert(HH1 : equivlist (list_inter (A :: B :: E :: nil) (C :: D :: E :: nil))  (E :: nil)).
my_inA_inter.
assert(HH2 := rk_singleton E).
rewrite HH1 in HH0.
rewrite HH2 in HH0.
rewrite H3 in HH0.
rewrite H4 in HH0.

assert(HH3 : rk(A :: B :: E :: C :: D :: E :: nil) = 2 \/ rk(A :: B :: E :: C :: D :: E :: nil) = 3).
apply le_lt_or_eq in HH0;simpl in HH0.
destruct HH0.
assert(HH4 : rk(A :: B :: E :: C :: D :: E :: nil) < 3).
solve[intuition].
assert(HH5 : incl (A :: B :: E :: nil) (A :: B :: E :: C :: D :: E :: nil));[my_inA|].
assert(HH6 := matroid2 (A :: B :: E :: nil) (A :: B :: E :: C :: D :: E :: nil) HH5).
omega.
omega.

destruct HH3.

assert(HH3 := rk_couple A C H).
assert(HH4 : incl (A :: C :: nil) (A :: B :: C :: D :: E :: nil));[my_inA|].
assert(HH5 : incl (A :: B :: C :: D :: E :: nil) (A :: B :: E :: C :: D :: E :: nil));[my_inA|].
assert(HH6 := matroid2 (A :: C :: nil) (A :: B :: C :: D :: E :: nil) HH4).
assert(HH7 := matroid2 (A :: B :: C :: D :: E :: nil) (A :: B :: E :: C :: D :: E :: nil) HH5).
omega.

assert(HH3 : incl (A :: B :: C :: D :: E :: nil) (A :: B :: E :: C :: D :: E :: nil));[my_inA|].
assert(HH4 := matroid2 (A :: B :: C :: D :: E :: nil) (A :: B :: E :: C :: D :: E :: nil) HH3).
rewrite H5 in HH4.
apply le_lt_or_eq in HH4.
destruct HH4.
assert(HH5 := rk_couple A C H).
assert(HH6 : incl (A :: C :: nil) (A :: B :: C :: D :: E :: nil));[my_inA|].
assert(HH7 := matroid2 (A :: C :: nil) (A :: B :: C :: D :: E :: nil) HH6).
omega.
omega.
Qed.

Lemma rk_quintuple_inter_aux2 : forall B C D E,
~ B = C ->
~ B = D -> 
rk(D :: B :: E :: nil) = 2 -> 
rk(C :: D :: E :: nil) = 2 ->
rk(D :: B :: C :: D :: E :: nil) = 2 \/ rk(D :: B :: C :: D :: E :: nil) = 3.
Proof.
intros.

assert (HH0 : rk((D :: B :: E :: nil) ++ (C :: D :: E :: nil)) + rk(list_inter (D :: B :: E :: nil) (C :: D :: E :: nil)) <=
       rk(D :: B :: E :: nil) + rk(C :: D :: E :: nil)).
apply matroid3_useful;my_inA.
assert (HH1 : equivlist (list_inter (D :: B :: E :: nil) (C :: D :: E :: nil)) (D :: E :: nil));[my_inA_inter|].
rewrite HH1 in HH0.
case_eq(eq_dec D E).
intros;subst.
rewrite H1 in HH0;rewrite H2 in HH0.
assert(HH2 : equivlist (E :: E :: nil) (E :: nil));[my_inA|].
replace (rk (E :: E :: nil)) with (rk(E :: nil)) in HH0.
2:rewrite HH2;intuition.
assert(HH3 := rk_singleton E).
rewrite HH3 in HH0.

assert(HH4 : rk(E :: B :: E :: C :: E :: E :: nil) = 2 \/ rk((E :: B :: E :: C :: E :: E :: nil)) = 3).
apply le_lt_or_eq in HH0;simpl in HH0.
destruct HH0.
assert(HH5 : rk((E :: B :: E :: C :: E :: E :: nil)) < 3).
solve[intuition].
assert(HH4 : incl (E :: B :: E :: nil) (E :: B :: E :: C :: E :: E :: nil));[my_inA|].
assert(HH6 := matroid2 (E :: B :: E :: nil) (E :: B :: E :: C :: E :: E :: nil) HH4).
omega.
omega.

assert(HH5 : equivlist (E :: B :: E :: C :: E :: E :: nil) (E :: B :: C :: E :: E :: nil));[my_inA|].
rewrite HH5 in HH4.
omega.

intros.
rewrite H1 in HH0;rewrite H2 in HH0.
assert(HH2 := rk_couple D E n).
rewrite HH2 in HH0.
assert(HH3 : rk((D :: B :: E :: nil) ++ (C :: D :: E :: nil)) = 2).
assert(HH4 : incl (D :: E :: nil) ((D :: B :: E :: nil) ++ (C :: D :: E :: nil)));[my_inA|].
assert(HH5 := matroid2 (D :: E :: nil) ((D :: B :: E :: nil) ++ (C :: D :: E :: nil)) HH4). 
omega.
assert(HH4 := rk_couple B C H).
assert(HH5 : incl (B :: C :: nil) (D :: B :: C :: D :: E :: nil));[my_inA|].
assert(HH6 := matroid2 (B :: C :: nil) (D :: B :: C :: D :: E :: nil) HH5).
assert(HH7 : incl (D :: B :: C :: D :: E :: nil) ((D :: B :: E :: nil) ++ (C :: D :: E :: nil)));[my_inA|].
assert(HH8 := matroid2 (D :: B :: C :: D :: E :: nil) ((D :: B :: E :: nil) ++ (C :: D :: E :: nil)) HH7).
omega.
Qed.

Lemma rk_quintuple_inter : forall A B C D E,
rk(A :: B :: E :: nil) = 2 -> 
rk(C :: D :: E :: nil) = 2 ->
rk(A :: B :: C :: D :: E :: nil) = 1 \/ rk(A :: B :: C :: D :: E :: nil) = 2 \/ rk(A :: B :: C :: D :: E :: nil) = 3.
Proof.
intros.
case_eq(eq_dec A C);
case_eq(eq_dec A D);
case_eq(eq_dec B C);
case_eq(eq_dec B D).

intros;rewrite <-e2;rewrite e;rewrite e1.
case_eq(eq_dec D E).
intros;rewrite e3.
assert(HH0 : equivlist (E :: E :: E :: E :: E :: nil) (E :: nil));[my_inA|].
rewrite HH0;assert(HH1 := rk_singleton E);omega.
intros.
assert(HH0 := rk_couple D E n);assert(HH : equivlist (D :: D :: D :: D :: E :: nil) (D :: E :: nil));[my_inA|].
rewrite HH;omega.

intros;apply False_ind;apply n;rewrite e;rewrite <-e0;rewrite e1;reflexivity.

intros;apply False_ind;apply n;rewrite e;rewrite <-e0;rewrite e1;reflexivity.

intros;rewrite e in *.
assert(HH := rk_quintuple_inter_aux2 B C D E n0 n H H0);intuition.

intros;apply False_ind;apply n;rewrite <-e;rewrite e0;rewrite <-e1;reflexivity.

intros;rewrite e;rewrite e0.
assert(HH0 : equivlist (C :: C :: C :: D :: E :: nil) (C :: D :: E :: nil));[my_inA|].
rewrite HH0;right;left;assumption.

intros;rewrite e;rewrite e0.
assert(HH0 : equivlist (C :: D :: C :: D :: E :: nil) (C :: D :: E :: nil));[my_inA|].
rewrite HH0;right;left;assumption.

intros;rewrite e in *.
assert(HH : equivlist (C :: D :: E :: nil) (D :: C :: E :: nil));[my_inA|];rewrite HH in H0.
assert(HH0 := rk_quintuple_inter_aux2 B D C E n n0 H H0).
assert(HH1 : equivlist (C :: B :: D :: C :: E :: nil) (C :: B :: C :: D :: E :: nil));[my_inA|].
rewrite HH1 in HH0;intuition.

intros;apply False_ind;apply n;rewrite <-e0;rewrite e;rewrite e1;reflexivity.

intros;rewrite e;rewrite e0.
assert(HH0 : equivlist (D :: C :: C :: D :: E :: nil) (C :: D :: E :: nil));[my_inA|].
rewrite HH0;right;left;assumption.

intros;rewrite e;rewrite e0.
assert(HH0 : equivlist (D :: D :: C :: D :: E :: nil) (C :: D :: E :: nil));[my_inA|].
rewrite HH0;right;left;assumption.

intros;rewrite e in *.
assert(HH0 := rk_quintuple_inter_aux2 B C D E n0 n H H0);intuition.

intros;rewrite e in *.
assert(HH : equivlist (A :: D :: E :: nil) (D :: A :: E :: nil));[my_inA|];rewrite HH in H.
assert(HH0 := rk_quintuple_inter_aux2 A C D E n0 n H H0). 
assert(HH1 : equivlist (D :: A :: C :: D :: E :: nil) (A :: D :: C :: D :: E :: nil));[my_inA|].
rewrite HH1 in HH0;intuition.

intros;rewrite e in *.
assert(HH : equivlist (A :: C :: E :: nil) (C :: A :: E :: nil));[my_inA|];rewrite HH in H.
assert(HH0 : equivlist (C :: D :: E :: nil) (D :: C :: E :: nil));[my_inA|];rewrite HH0 in H0.
assert(HH1 := rk_quintuple_inter_aux2 A D C E n0 n1 H H0). 
assert(HH2 : equivlist (C :: A :: D :: C :: E :: nil) (A :: C :: C :: D :: E :: nil));[my_inA|].
rewrite HH2 in HH1;intuition.

intros;rewrite e in *.
assert(HH : equivlist (A :: D :: E :: nil) (D :: A :: E :: nil));[my_inA|];rewrite HH in H.
assert(HH0 := rk_quintuple_inter_aux2 A C D E n1 n0 H H0).
assert(HH1 : equivlist (D :: A :: C :: D :: E :: nil) (A :: D :: C :: D :: E :: nil));[my_inA|].
rewrite HH1 in HH0;intuition.

intros.
assert(HH := rk_quintuple_inter_aux A B C D E n2 n1 n0 n H H0);intuition.
Qed.

Lemma rk_quintuple_max_3 : forall X Y Z W V: Point, rk(X :: Y :: Z :: W :: V :: nil) <= 3.
intros.

assert(HH := rk_lower_dim).
destruct HH;destruct H;destruct H.
assert(HH := rk_triple_3 x x0 x1).
assert(HH0 : rk (x :: x0 :: x1 :: nil) = 3);[omega|].
assert(HH1 := rk_quadruple_max_3 x x0 x1 X).
assert(HH2 := rk_quadruple_max_3 x x0 x1 Y).
assert(HH3 := rk_quadruple_max_3 x x0 x1 Z).
assert(HH4 := rk_quadruple_max_3 x x0 x1 W).
assert(HH5 := rk_quadruple_max_3 x x0 x1 V).
assert(HH6 : incl (x :: x0 :: x1 :: nil) (x :: x0 :: x1 :: X :: nil));[my_inA|].
assert(HH7 : incl (x :: x0 :: x1 :: nil) (x :: x0 :: x1 :: Y :: nil));[my_inA|].
assert(HH8 : incl (x :: x0 :: x1 :: nil) (x :: x0 :: x1 :: Z :: nil));[my_inA|].
assert(HH9 : incl (x :: x0 :: x1 :: nil) (x :: x0 :: x1 :: W :: nil));[my_inA|].
assert(HH10 : incl (x :: x0 :: x1 :: nil) (x :: x0 :: x1 :: V :: nil));[my_inA|].
assert(HH11 := matroid2 (x :: x0 :: x1 :: nil) (x :: x0 :: x1 :: X :: nil) HH6).
assert(HH12 : rk (x :: x0 :: x1 :: X :: nil) = 3);[omega|].
assert(HH13 := matroid2 (x :: x0 :: x1 :: nil) (x :: x0 :: x1 :: Y :: nil) HH7).
assert(HH14 : rk (x :: x0 :: x1 :: Y :: nil) = 3);[omega|].
assert(HH15 := matroid2 (x :: x0 :: x1 :: nil) (x :: x0 :: x1 :: Z :: nil) HH8).
assert(HH16 : rk (x :: x0 :: x1 :: Z :: nil) = 3);[omega|].
assert(HH17 := matroid2 (x :: x0 :: x1 :: nil) (x :: x0 :: x1 :: W :: nil) HH9).
assert(HH18 : rk (x :: x0 :: x1 :: W :: nil) = 3);[omega|].
assert(HH19 := matroid2 (x :: x0 :: x1 :: nil) (x :: x0 :: x1 :: V :: nil) HH10).
assert(HH20 : rk (x :: x0 :: x1 :: V :: nil) = 3);[omega|].
clear H HH HH1 HH2 HH3 HH4 HH5 HH6 HH7 HH8 HH9 HH10 HH11 HH13 HH15 HH17 HH19.

case_eq(eq_dec X Y);intros.
rewrite e;assert(HH21 : equivlist (Y :: Y :: Z :: W :: V :: nil) (Y :: Z :: W :: V :: nil));[my_inA|];
rewrite HH21;assert(HH22 := rk_quadruple_max_3 Y Z W V);assumption.
case_eq(eq_dec X Z);intros.
rewrite e;assert(HH21 : equivlist (Z :: Y :: Z :: W :: V :: nil) (Y :: Z :: W :: V :: nil));[my_inA|];
rewrite HH21;assert(HH22 := rk_quadruple_max_3 Y Z W V);assumption.
case_eq(eq_dec X W);intros.
rewrite e;assert(HH21 : equivlist (W :: Y :: Z :: W :: V :: nil) (Y :: Z :: W :: V :: nil));[my_inA|];
rewrite HH21;assert(HH22 := rk_quadruple_max_3 Y Z W V);assumption.
case_eq(eq_dec X V);intros.
rewrite e;assert(HH21 : equivlist (V :: Y :: Z :: W :: V :: nil) (Y :: Z :: W :: V :: nil));[my_inA|];
rewrite HH21;assert(HH22 := rk_quadruple_max_3 Y Z W V);assumption.
case_eq(eq_dec Y Z);intros.
rewrite e;assert(HH21 : equivlist (X :: Z :: Z :: W :: V :: nil) (X :: Z :: W :: V :: nil));[my_inA|];
rewrite HH21;assert(HH22 := rk_quadruple_max_3 X Z W V);assumption.
case_eq(eq_dec Y W);intros.
rewrite e;assert(HH21 : equivlist (X :: W :: Z :: W :: V :: nil) (X :: Z :: W :: V :: nil));[my_inA|];
rewrite HH21;assert(HH22 := rk_quadruple_max_3 X Z W V);assumption.
case_eq(eq_dec Y V);intros.
rewrite e;assert(HH21 : equivlist (X :: V :: Z :: W :: V :: nil) (X :: Z :: W :: V :: nil));[my_inA|];
rewrite HH21;assert(HH22 := rk_quadruple_max_3 X Z W V);assumption.
case_eq(eq_dec Z W);intros.
rewrite e;assert(HH21 : equivlist (X :: Y :: W :: W :: V :: nil) (X :: Y :: W :: V :: nil));[my_inA|];
rewrite HH21;assert(HH22 := rk_quadruple_max_3 X Y W V);assumption.
case_eq(eq_dec Z V);intros.
rewrite e;assert(HH21 : equivlist (X :: Y :: V :: W :: V :: nil) (X :: Y :: W :: V :: nil));[my_inA|];
rewrite HH21;assert(HH22 := rk_quadruple_max_3 X Y W V);assumption.
case_eq(eq_dec W V);intros.
rewrite e;assert(HH21 : equivlist (X :: Y :: Z :: V :: V :: nil) (X :: Y :: Z :: V :: nil));[my_inA|];
rewrite HH21;assert(HH22 := rk_quadruple_max_3 X Y Z V);assumption.
clear H H0 H1 H2 H3 H4 H5 H6 H7 H8.

assert (HH23 : rk((x :: x0 :: x1 :: X :: nil) ++ (x :: x0 :: x1 :: Y :: nil)) + rk(list_inter (x :: x0 :: x1 :: X :: nil) (x :: x0 :: x1 :: Y :: nil)) <=
       rk(x :: x0 :: x1 :: X :: nil) + rk(x :: x0 :: x1 :: Y :: nil)).
apply matroid3_useful;my_inA.
assert(HH24 : equivlist (list_inter (x :: x0 :: x1 :: X :: nil) (x :: x0 :: x1 :: Y :: nil))  (x :: x0 :: x1 :: nil));[my_inA_inter|].
rewrite HH24 in HH23;clear HH24.
assert(HH25 : equivlist ((x :: x0 :: x1 :: X :: nil) ++ x :: x0 :: x1 :: Y :: nil) (x :: x0 :: x1 :: X :: Y :: nil));[my_inA_union|].
rewrite HH25 in HH23;clear HH25.
assert(HH26 : incl (x :: x0 :: x1 :: nil) (x :: x0 :: x1 :: X :: Y :: nil));[my_inA|].
assert(HH27 := matroid2 (x :: x0 :: x1 :: nil) (x :: x0 :: x1 :: X :: Y :: nil) HH26).
assert(HH28 : rk(x :: x0 :: x1 :: X :: Y :: nil) = 3);[omega|].
clear HH12 HH14 HH23 HH26 HH27.

assert (HH29 : rk((x :: x0 :: x1 :: X :: Y :: nil) ++ (x :: x0 :: x1 :: Z :: nil)) + rk(list_inter (x :: x0 :: x1 :: X :: Y :: nil) (x :: x0 :: x1 :: Z :: nil)) <=
       rk(x :: x0 :: x1 :: X :: Y :: nil) + rk(x :: x0 :: x1 :: Z :: nil)).
apply matroid3_useful;my_inA.
assert(HH30 : equivlist (list_inter (x :: x0 :: x1 :: X :: Y :: nil) (x :: x0 :: x1 :: Z :: nil))  (x :: x0 :: x1 :: nil));[my_inA_inter|].
rewrite HH30 in HH29;clear HH30.
assert(HH31 : equivlist ((x :: x0 :: x1 :: X :: Y :: nil) ++ x :: x0 :: x1 :: Z :: nil) (x :: x0 :: x1 :: X :: Y :: Z :: nil));[my_inA_union|].
rewrite HH31 in HH29;clear HH31.
assert(HH32 : incl (x :: x0 :: x1 :: nil) (x :: x0 :: x1 :: X :: Y :: Z :: nil));[my_inA|].
assert(HH33 := matroid2 (x :: x0 :: x1 :: nil) (x :: x0 :: x1 :: X :: Y ::  Z :: nil) HH32).
assert(HH34 : rk(x :: x0 :: x1 :: X :: Y :: Z :: nil) = 3);[omega|].
clear HH16 HH28 HH29 HH32 HH33.

assert (HH35 : rk((x :: x0 :: x1 :: X :: Y :: Z :: nil) ++ (x :: x0 :: x1 :: W :: nil)) + rk(list_inter (x :: x0 :: x1 :: X :: Y :: Z :: nil) (x :: x0 :: x1 :: W :: nil)) <=
       rk(x :: x0 :: x1 :: X :: Y :: Z :: nil) + rk(x :: x0 :: x1 :: W :: nil)).
apply matroid3_useful;my_inA.
assert(HH36 : equivlist (list_inter (x :: x0 :: x1 :: X :: Y :: Z :: nil) (x :: x0 :: x1 :: W :: nil))  (x :: x0 :: x1 :: nil));[my_inA_inter|].
rewrite HH36 in HH35;clear HH36.
assert(HH37 : equivlist ((x :: x0 :: x1 :: X :: Y :: Z :: nil) ++ x :: x0 :: x1 :: W :: nil) (x :: x0 :: x1 :: X :: Y :: Z :: W :: nil));[my_inA_union;left;my_inA_union|].
rewrite HH37 in HH35;clear HH37.
assert(HH38 : incl (x :: x0 :: x1 :: nil) (x :: x0 :: x1 :: X :: Y :: Z :: W :: nil));[my_inA|].
assert(HH39 := matroid2 (x :: x0 :: x1 :: nil) (x :: x0 :: x1 :: X :: Y ::  Z :: W :: nil) HH38).
assert(HH40 : rk(x :: x0 :: x1 :: X :: Y :: Z :: W ::nil) = 3);[omega|].
clear HH18 HH34 HH35 HH38 HH39.

assert (HH41 : rk((x :: x0 :: x1 :: X :: Y :: Z :: W :: nil) ++ (x :: x0 :: x1 :: V :: nil)) + rk(list_inter (x :: x0 :: x1 :: X :: Y :: Z :: W ::nil) (x :: x0 :: x1 :: V :: nil)) <=
       rk(x :: x0 :: x1 :: X :: Y :: Z :: W :: nil) + rk(x :: x0 :: x1 :: V :: nil)).
apply matroid3_useful;my_inA.
assert(HH42 : equivlist (list_inter (x :: x0 :: x1 :: X :: Y :: Z :: W :: nil) (x :: x0 :: x1 :: V :: nil))  (x :: x0 :: x1 :: nil));[my_inA_inter|].
rewrite HH42 in HH41;clear HH42.
assert(HH43 : equivlist ((x :: x0 :: x1 :: X :: Y :: Z :: W :: nil) ++ x :: x0 :: x1 :: V :: nil) (x :: x0 :: x1 :: X :: Y :: Z :: W :: V :: nil));[my_inA_union;left;my_inA_union|].
rewrite HH43 in HH41;clear HH43.
assert(HH44 : incl (x :: x0 :: x1 :: nil) (x :: x0 :: x1 :: X :: Y :: Z :: W :: V :: nil));[my_inA|].
assert(HH45 := matroid2 (x :: x0 :: x1 :: nil) (x :: x0 :: x1 :: X :: Y ::  Z :: W :: V :: nil) HH44).
assert(HH46 : rk(x :: x0 :: x1 :: X :: Y :: Z :: W ::V :: nil) = 3);[omega|].
clear HH20 HH40 HH41 HH44 HH45.
assert(HH47 : incl (X :: Y :: Z :: W :: V :: nil)(x :: x0 :: x1 :: X :: Y :: Z :: W :: V :: nil));[my_inA|].
assert(HH48 := matroid2 (X :: Y :: Z :: W :: V :: nil)(x :: x0 :: x1 :: X :: Y :: Z :: W :: V :: nil) HH47).
omega.
Qed.
