Require Export ProjectiveGeometry.Dev.matroid_properties.
Require Export ProjectiveGeometry.Dev.projective_plane_rank_axioms.

(*****************************************************************************)
(** Rank plane properties **)

Section s_rankProperties.

Context `{RPP : RankProjectivePlane}.
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

Lemma rk_couple1 : forall p q : Point,~ p [==] q -> rk(couple p q) = 2.
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

Hint Resolve rk_singleton rk_couple1 rk_couple2 couple_rk1 couple_rk2 couple_rk_degen rk_couple_1 rk_couple_2 : rk_base.

Lemma base_points_distinct_1 : ~ P0 [==] P1.
Proof.
assert (T:= rk_lower_dim).
unfold not;intro.
rewrite H0 in T.
setoid_replace (triple P1 P1 P2) with (couple P1 P2) in T by fsetdecide.
assert (HH := rk_couple_2 P1 P2).
omega.
Qed.

Lemma base_points_distinct_2 : ~ P1 [==] P2.
Proof.
assert (T:= rk_lower_dim).
unfold not;intro.
rewrite H0 in T.
setoid_replace (triple P0 P2 P2) with (couple P0 P2) in T by fsetdecide.
assert (HH := rk_couple_2 P0 P2).
omega.
Qed.

Lemma rank_quadruple_inter_plane : forall A B C D E,
~A[==]C ->
~A[==]D ->
~B[==]C ->
~B[==]D -> 
rk(triple A B E) = 2 -> 
rk(triple C D E) = 2 ->
rk(quadruple A B C D) = 2 \/ rk(quadruple A B C D) = 3.
Proof.
intros.

assert (HH0 : rk(union(triple A B E) (triple C D E)) + rk(inter(triple A B E) (triple C D E)) <=
       rk(triple A B E) + rk(triple C D E)).
apply matroid3_useful.
clear_all;fsetdecide.
setoid_replace (inter (triple A B E) (triple C D E)) with (singleton E) in HH0.
2:clear_all;fsetdecide.
assert(HH1 := rk_singleton E).
rewrite HH1 in HH0.
rewrite H4 in HH0.
rewrite H5 in HH0.

assert(HH2 : rk(triple A B E ++ triple C D E) = 2 \/ rk(triple A B E ++ triple C D E) = 3).
apply le_lt_or_eq in HH0;simpl in HH0.
destruct HH0.
assert(HH3 : rk(triple A B E ++ triple C D E) < 3).
solve[intuition].
assert(HH4 : Subset (triple A B E) (triple A B E ++ triple C D E)).
clear_all;fsetdecide.
assert(HH5 := matroid2 (triple A B E) (triple A B E ++ triple C D E) HH4).
omega.
omega.

destruct HH2.

assert(HH2 := rk_couple1 A C H0).
assert(HH3 : Subset (couple A C) (quadruple A B C D)).
clear_all;fsetdecide.
assert(HH4 : Subset (quadruple A B C D) (triple A B E ++ triple C D E)).
clear_all;clear HH3;fsetdecide.
assert(HH5 := matroid2 (couple A C) (quadruple A B C D) HH3).
assert(HH6 := matroid2 (quadruple A B C D) (triple A B E ++ triple C D E) HH4).
omega.

assert(HH2 : Subset (quadruple A B C D) (triple A B E ++ triple C D E)).
clear_all;fsetdecide.
assert(HH3 := matroid2 (quadruple A B C D) (triple A B E ++ triple C D E) HH2).
rewrite H6 in HH3.
apply le_lt_or_eq in HH3.
destruct HH3.
assert(HH4 := rk_couple1 A C H0).
assert(HH5 : Subset (couple A C) (quadruple A B C D)).
clear_all;clear HH2 H7;fsetdecide.
assert(HH6 := matroid2 (couple A C) (quadruple A B C D) HH5).
omega.
omega.
Qed.

Lemma rank_quadruple_inter_plane2 : forall B C D E,
~B[==]C ->
~B[==]D -> 
rk(triple D B E) = 2 -> 
rk(triple C D E) = 2 ->
rk(quadruple D B C D) = 2 \/ rk(quadruple D B C D) = 3.
Proof.
intros.

assert (HH0 : rk(union(triple D B E) (triple C D E)) + rk(inter(triple D B E) (triple C D E)) <=
       rk(triple D B E) + rk(triple C D E)).
apply matroid3_useful.
clear_all;fsetdecide.
setoid_replace (inter (triple D B E) (triple C D E)) with (couple D E) in HH0.
2:clear_all;fsetdecide.

case_eq(eq_dec D E).
intros.
rewrite e in *.
rewrite H2 in HH0;rewrite H3 in HH0.
assert(HH1 : Equal (couple E E) (singleton E)).
clear_all;fsetdecide.
rewrite HH1 in HH0.
assert(HH2 := rk_singleton E).
rewrite HH2 in HH0.

assert(HH3 : rk(triple E B E ++ triple C E E) = 2 \/ rk(triple E B E ++ triple C E E) = 3).
apply le_lt_or_eq in HH0;simpl in HH0.
destruct HH0.
assert(HH3 : rk(triple E B E ++ triple C E E) < 3).
solve[intuition].
assert(HH4 : Subset (triple E B E) (triple E B E ++ triple C E E)).
clear_all;clear HH1 HH3;fsetdecide.
assert(HH5 := matroid2 (triple E B E) (triple E B E ++ triple C E E) HH4).
omega.
omega.

assert(HH4 : Equal (triple E B E ++ triple C E E) (quadruple E B C E)).
clear_all;clear HH1;fsetdecide.
rewrite HH4 in HH3.
omega.

intros.
clear H4.
rewrite H2 in HH0;rewrite H3 in HH0.
assert(HH1 := rk_couple1 D E n).
rewrite HH1 in HH0.
assert(HH3 : rk(triple D B E ++ triple C D E) = 2).
assert(HH4 : Subset (couple D E) (triple D B E ++ triple C D E)).
clear_all;fsetdecide.
assert(HH5 := matroid2 (couple D E) (triple D B E ++ triple C D E) HH4).
omega.
assert(HH4 := rk_couple1 B C H0).
assert(HH5 : Subset (couple B C) (quadruple D B C D)).
clear_all;fsetdecide.
assert(HH6 := matroid2 (couple B C) (quadruple D B C D) HH5).
assert(HH7 : Subset (quadruple D B C D) (triple D B E ++ triple C D E)).
clear_all;clear HH5;fsetdecide.
assert(HH8 := matroid2 (quadruple D B C D) (triple D B E ++ triple C D E) HH7).
omega.
Qed.

Lemma rank_quadruple_inter : forall A B C D E,
rk(triple A B E) = 2 -> 
rk(triple C D E) = 2 ->
rk(quadruple A B C D) = 1 \/ rk(quadruple A B C D) = 2 \/ rk(quadruple A B C D) = 3.
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
assert(HH0 : Equal (quadruple D D D D) (singleton D)).
clear_all;fsetdecide.
rewrite HH0;assert(HH1 := rk_singleton D);omega.
intros.
assert(HH0 := rk_couple1 C D n);assert(HH : Equal (quadruple D D C D) (couple C D)).
clear_all;fsetdecide.
rewrite HH;omega.

intros.
rewrite e;rewrite e1.
case_eq(eq_dec C D).
intros;rewrite e2.
assert(HH0 : Equal (quadruple D D D D) (singleton D)).
clear_all;fsetdecide.
rewrite HH0;assert(HH1 := rk_singleton D);omega.
intros.
assert(HH0 := rk_couple1 C D n0);assert(HH : Equal (quadruple C C C D) (couple C D)).
clear_all;fsetdecide.
rewrite HH;omega.

intros.
rewrite e;rewrite e1.
case_eq(eq_dec C D).
intros;rewrite e2.
assert(HH0 : Equal (quadruple D D D D) (singleton D)).
clear_all;fsetdecide.
rewrite HH0;assert(HH1 := rk_singleton D);omega.
intros.
assert(HH0 := rk_couple1 C D n0);assert(HH : Equal (quadruple C D C D) (couple C D)).
clear_all;fsetdecide.
rewrite HH;omega.

intros.
rewrite e in *.
assert(HH0 := rank_quadruple_inter_plane2 B C D E n0 n H0 H1).
omega.

intros.
rewrite e0;rewrite e1.
case_eq(eq_dec C D).
intros;rewrite e2.
assert(HH0 : Equal (quadruple D D D D) (singleton D)).
clear_all;fsetdecide.
rewrite HH0;assert(HH1 := rk_singleton D);omega.
intros.
assert(HH0 := rk_couple1 C D n0);assert(HH : Equal (quadruple C C C D) (couple C D)).
clear_all;fsetdecide.
rewrite HH;omega.

intros.
rewrite e;rewrite e0.
case_eq(eq_dec C D).
intros;rewrite e1.
assert(HH0 : Equal (quadruple D D D D) (singleton D)).
clear_all;fsetdecide.
rewrite HH0;assert(HH1 := rk_singleton D);omega.
intros.
assert(HH0 := rk_couple1 C D n1);assert(HH : Equal (quadruple C C C D) (couple C D)).
clear_all;fsetdecide.
rewrite HH;omega.

intros.
rewrite e;rewrite e0.
case_eq(eq_dec C D).
intros;rewrite e1.
assert(HH0 : Equal (quadruple D D D D) (singleton D)).
clear_all;fsetdecide.
rewrite HH0;assert(HH1 := rk_singleton D);omega.
intros.
assert(HH0 := rk_couple1 C D n1);assert(HH : Equal (quadruple C D C D) (couple C D)).
clear_all;fsetdecide.
rewrite HH;omega.

intros.
rewrite e in *.
assert(HH0 : Equal (triple C D E) (triple D C E)).
clear_all;fsetdecide.
rewrite HH0 in H1.
assert(HH1 := rank_quadruple_inter_plane2 B D C E n n0 H0 H1).
assert(HH2 : Equal (quadruple C B C D) (quadruple C B D C)).
clear_all;clear HH0;fsetdecide.
rewrite HH2.
omega.

intros.
rewrite e;rewrite e1.
case_eq(eq_dec C D).
intros;rewrite e2.
assert(HH0 : Equal (quadruple D D D D) (singleton D)).
clear_all;fsetdecide.
rewrite HH0;assert(HH1 := rk_singleton D);omega.
intros.
assert(HH0 := rk_couple1 C D n0);assert(HH : Equal (quadruple D D C D) (couple C D)).
clear_all;fsetdecide.
rewrite HH;omega.

intros.
rewrite e;rewrite e0.
case_eq(eq_dec C D).
intros;rewrite e1.
assert(HH0 : Equal (quadruple D D D D) (singleton D)).
clear_all;fsetdecide.
rewrite HH0;assert(HH1 := rk_singleton D);omega.
intros.
assert(HH0 := rk_couple1 C D n1);assert(HH : Equal (quadruple D C C D) (couple C D)).
clear_all;fsetdecide.
rewrite HH;omega.

intros.
rewrite e;rewrite e0.
case_eq(eq_dec C D).
intros;rewrite e1.
assert(HH0 : Equal (quadruple D D D D) (singleton D)).
clear_all;fsetdecide.
rewrite HH0;assert(HH1 := rk_singleton D);omega.
intros.
assert(HH0 := rk_couple1 C D n1);assert(HH : Equal (quadruple D D C D) (couple C D)).
clear_all;fsetdecide.
rewrite HH;omega.

intros.
rewrite e in *.
assert(HH0 := rank_quadruple_inter_plane2 B C D E n0 n H0 H1).
omega.

intros.
rewrite e in  *.
assert(HH0 : Equal (triple A D E) (triple D A E)).
clear_all;fsetdecide.
rewrite HH0 in H0.
assert(HH1 := rank_quadruple_inter_plane2 A C D E n0 n H0 H1).
assert(HH2 : Equal (quadruple D A C D) (quadruple A D C D)).
clear_all;clear HH0;fsetdecide.
rewrite HH2 in HH1.
omega.

intros.
rewrite e in  *.
assert(HH0 : Equal (triple A C E) (triple C A E)).
clear_all;fsetdecide.
rewrite HH0 in H0.
assert(HH1 : Equal (triple C D E) (triple D C E)).
clear_all;clear HH0;fsetdecide.
rewrite HH1 in H1.
assert(HH2 := rank_quadruple_inter_plane2 A D C E n0 n1 H0 H1).
assert(HH3 : Equal (quadruple C A D C) (quadruple A C C D)).
clear_all;clear HH0 HH1;fsetdecide.
rewrite HH3 in HH2.
omega.

intros.
rewrite e in *.
assert(HH0 : Equal (triple A D E) (triple D A E)).
clear_all;fsetdecide.
rewrite HH0 in H0.
assert(HH1 := rank_quadruple_inter_plane2 A C D E n1 n0 H0 H1).
assert(HH2 : Equal (quadruple A D C D) (quadruple D A C D)).
clear_all;clear HH0;fsetdecide.
rewrite HH2.
omega.

intros.
assert(HH := rank_quadruple_inter_plane A B C D E n2 n1 n0 n H0 H1).
omega.
Qed.

Lemma rank_triple_max_3 : forall X Y Z, rk (triple X Y Z) <= 3.
Proof.
intros.
case_eq(eq_dec X Y);
case_eq(eq_dec X Z);
case_eq(eq_dec Y Z).
intros.
rewrite e;rewrite e0.
assert(HH0 : Equal (triple Z Z Z) (singleton Z)).
clear_all;fsetdecide.
rewrite HH0;assert(HH1 := rk_singleton Z);omega.
intros.
rewrite e.
assert(HH0 := rk_couple1 Y Z n);assert(HH : Equal (triple Z Y Z) (couple Y Z)).
clear_all;fsetdecide.
rewrite HH;omega.
intros.
rewrite e.
assert(HH0 := rk_couple1 X Z n);assert(HH : Equal (triple X Z Z) (couple X Z)).
clear_all;fsetdecide.
rewrite HH;omega.
intros.
rewrite e.
assert(HH0 := rk_couple1 Y Z n);assert(HH : Equal (triple Y Y Z) (couple Y Z)).
clear_all;fsetdecide.
rewrite HH;omega.
intros.
rewrite e;rewrite e0.
assert(HH0 : Equal (triple Z Z Z) (singleton Z)).
clear_all;fsetdecide.
rewrite HH0;assert(HH1 := rk_singleton Z);omega.
intros.
rewrite e.
assert(HH0 := rk_couple1 Y Z n);assert(HH : Equal (triple Z Y Z) (couple Y Z)).
clear_all;fsetdecide.
rewrite HH;omega.
intros.
rewrite e.
assert(HH0 := rk_couple1 X Z n);assert(HH : Equal (triple X Z Z) (couple X Z)).
clear_all;fsetdecide.
rewrite HH;omega.
intros.
assert (HH0 : rk(union(couple X Y) (singleton Z)) + rk(inter(couple X Y) (singleton Z)) <=
       rk(couple X Y) + rk(singleton Z)).
apply matroid3_useful.
clear_all;fsetdecide.
setoid_replace (inter(couple X Y) (singleton Z)) with (empty) in HH0.
2:clear_all;clear H0 H1 H2;fsetdecide.
setoid_replace (union(couple X Y) (singleton Z)) with (triple X Y Z) in HH0.
2:clear_all;fsetdecide.
assert(HH1 :=  rk_couple1 X Y n1).
assert(HH2 := rk_singleton Z).
omega.
Qed.

Lemma rank_quadruple_max_3 : forall X Y Z W, rk (quadruple X Y Z W) <= 3.
Proof.
intros.
assert(HH0 := rk_inter X Y Z W).
destruct HH0.
destruct H0.
assert(HH1 := rank_quadruple_inter X Y Z W x H0 H1).
omega.
Qed.

End s_rankProperties.