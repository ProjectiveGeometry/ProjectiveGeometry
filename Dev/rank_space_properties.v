Require Export ProjectiveGeometry.Dev.matroid_properties.
Require Export ProjectiveGeometry.Dev.projective_space_rank_axioms.

(*****************************************************************************)
(** Rank space or higher properties **)


Section s_rankProperties_1.

Context `{M : RankProjectiveSpace}.
Context `{EP : EqDecidability Point}.


Lemma rk_singleton : forall p : Point, rk (singleton p) = 1.
Proof.
intros.
assert (rk (singleton p)<= 1).
apply (rk_singleton_le);auto.
assert (rk (singleton p)>= 1).
apply (rk_singleton_ge);auto.
omega.
Qed.

Lemma rk_couple1 : forall p q : Point,~ p [==] q -> rk(couple p q)=2.
Proof.
intros.
assert (rk(couple p q)<=2).
apply (rk_couple_2).
assert (rk(couple p q)>=2).
apply (rk_couple_ge);auto.
omega.
Qed.

Lemma couple_rk1 : forall p q : Point, rk(couple p q) = 2 -> ~ p [==] q.
Proof.
intros.
unfold not;intro.
assert (rk (couple p q) = 1).
setoid_replace (couple p q) with (singleton p).
apply rk_singleton.
rewrite H1.
clear H0 H1.
fsetdecide.
rewrite H0 in H2.
inversion H2.
Qed.

Lemma couple_rk2 : forall p q : Point, rk (couple p q) = 1 -> p [==] q.
Proof.
intros.
case_eq(eq_dec p q).
intros.
assumption.
intro.
assert (rk(couple p q)=2).
apply rk_couple1;assumption.
rewrite H0 in H1.
assert False.
intuition.
intuition.
Qed.

Lemma rk_couple2 : forall p q : Point, p [==] q -> rk(couple p q) = 1.
Proof.
intros.
setoid_replace (couple p q) with (singleton p).
apply (rk_singleton).
rewrite H0.
fsetdecide.
Qed.

Lemma rk_couple_1 : forall p q, 1 <= rk (couple p q).
Proof.
intros.
case_eq(eq_dec p q).
intro.
rewrite rk_couple2.
omega.
assumption.
intro.
rewrite rk_couple1.
omega.
assumption.
Qed.

Lemma couple_rk_degen : forall p, rk (couple p p) = 2 -> False.
Proof.
intros.
assert (rk (couple p p) = 1).
setoid_replace (couple p p) with (singleton p).
apply rk_singleton.
fsetdecide.
intuition.
Qed.

Hint Resolve rk_singleton rk_couple1 rk_couple2 couple_rk1 couple_rk2 couple_rk_degen : rk.

Lemma base_points_distinct_1 : ~ P0 [==] P1.
Proof.
assert (T:= rk_lower_dim).
unfold not;intro.
rewrite H0 in T.
setoid_replace (quadruple P1 P1 P2 P3) with (triple P1 P2 P3) in T by fsetdecide.
assert (rk (triple P1 P2 P3) <= 3).
apply rk_triple_le.
omega.
Qed.

Lemma base_points_distinct_2 : ~ P2 [==] P3.
Proof.
assert (T:= rk_lower_dim).
unfold not;intro.
rewrite H0 in T.
setoid_replace (quadruple P0 P1 P3 P3) with (triple P0 P1 P3) in T by fsetdecide.
assert (rk (triple P0 P1 P3) <= 3).
apply rk_triple_le.
omega.
Qed.

Lemma rk_lemma_1 : forall A B P Q,
rk (couple A B) = 2 ->
rk (triple A B P) = 2 ->
rk (triple A B Q) = 2 ->
rk (quadruple A B P Q) = 2.
Proof.
intros.
assert (rk (union (triple A B P) (triple A B Q)) + rk (couple A B) <=
           rk (triple A B P) + rk (triple A B Q)).
apply (matroid3_useful (triple A B P) (triple A B Q) (couple A B)).
clear_all;fsetdecide.

assert (rk (union (triple A B P) (triple A B Q)) <= 2).
omega.
setoid_replace (union (triple A B P) (triple A B Q)) with (quadruple A B P Q) in H4.
apply le_antisym.
auto.
cut (rk (couple A B) <= rk (quadruple A B P Q)).
omega.
apply matroid2.
clear_all;fsetdecide.
clear_all;fsetdecide.
Qed.

Lemma rk_quadruple_max_4_wc : forall A B C D : Point, 
~ A[==]B -> ~ C[==]D -> rk(quadruple A B C D) <= 4.
Proof.
intros.
apply rk_quadruple_le.
Qed.

Lemma rk_quadruple_3_or_higher : forall A B C D,
~ A[==]B ->
~ C[==]D ->
rk(quadruple A B C D) <> 2 ->
rk(quadruple A B C D) > 2.
Proof.
intros.
assert(HH := rk_quadruple_max_4_wc A B C D H0 H1).
assert(HH0 : rk(quadruple A B C D) <> 1).
intro.
assert(HH1 := rk_couple1 A B H0).
assert(HH2 : (couple A B [<=] quadruple A B C D)%set).
fsetdecide.
assert(HH3 := matroid2 (couple A B) (quadruple A B C D) HH2).
omega.
assert(HH1 := rk_couple1 A B H0).
assert(HH2 : rk (couple A B) >= 2).
intuition.
assert(HH3 : (couple A B [<=] quadruple A B C D)%set).
fsetdecide.
assert(HH4 := matroid2 (couple A B) (quadruple A B C D) HH3).
assert(HH5 : rk(quadruple A B C D) >= 2).
omega.
omega.
Qed.

Lemma rk_line_unification : forall A B C,
rk(couple A B) = 2 -> rk(couple A C) = 2 -> 
rk(couple B C) = 2 -> rk(triple A B C) <= 2 -> rk(triple A B C) = 2.
Proof.
intros.
assert(HH : (couple A B [<=] triple A B C)%set).
fsetdecide.
assert(HH1 := matroid2 (couple A B) (triple A B C) HH).
omega.
Qed.

End s_rankProperties_1.


Section s_rankProperties_2.

Context `{M : RankProjectiveSpace}.
Context `{EP : EqDecidability Point}.

Lemma intersecting_lines_rank_3 : forall A B C D I,
rk (triple A B I) <= 2 ->
rk (triple C D I) <= 2 ->
rk (union (singleton I) (quadruple A B C D)) <= 3.
Proof.
intros.
assert (rk (union (triple A B I) (triple C D I)) +
       rk (singleton I) <=
       rk (triple A B I) + rk (triple C D I)).
apply (matroid3_useful (triple A B I) (triple C D I) (singleton I)).
fsetdecide.
rewrite rk_singleton in H2.
setoid_replace (union (triple A B I) (triple C D I)) 
with (union (singleton I) (quadruple A B C D)) in H2.
omega.
unfold Equal; split;clear_all;fsetdecide.
Qed.

End s_rankProperties_2.

Hint Resolve rk_singleton rk_couple1 rk_couple2 couple_rk1 couple_rk2 couple_rk_degen : rk_base.