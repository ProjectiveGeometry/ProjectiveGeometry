Require Export ProjectiveGeometry.Dev.psoh_equiv_rk_lemmas.

(*****************************************************************************)
(** Proof of projective space rank axioms **)


Section s_psEquivToRk.

Context `{PSR : ProjectiveSpaceRank}.
Context `{EP : EqDecidability Point}.
Context `{OP : OrderedType Point}.
Context `{EL : EqDecidabilityL Line}.
Context `{ELI : EqDecidabilityP Line Intersect}.

Lemma matroid1a : forall e, rkl e >= 0.
Proof.
my_rank.
Qed.

Lemma matroid1b : forall e, rkl e <= cardinal e.
Proof.
intros.
induction e.
simpl.
intuition.
unfold rkl.
case_eq e.
intros.
simpl.
intuition.
intros.
case_eq (contains_four_non_coplanar_points (a :: p :: l)).
intros.
assert( HH0 := matroid3_aux3_bis_bis (a :: p :: l) H0).
assert( HH1 := list_cardinal_aux4 (a :: p :: l) HH0).
intuition.
intros.
case_eq (contains_three_non_collinear_points (a :: p :: l)).
intros.
assert( HH0 := matroid3_aux2_cop (a :: p :: l) H1 H0).
assert( HH1 := list_cardinal_aux3 (a :: p :: l) HH0).
intuition.
intros.
case_eq (contains_two_distinct_points (a :: p :: l)).
intros.
assert( HH0 := matroid3_aux2_col (a :: p :: l) H2 H1).
assert( HH1 := list_cardinal_aux2 (a :: p :: l) HH0).
intuition.
intros.
assert( HH0 := matroid3_aux3 (a :: p :: l) H2).
destruct HH0.
rewrite <-H in H3.
assert( HH1 : (a :: e) <> nil).
intro.
inversion H4.
assert( HH2 := matroid3_aux3_bis (a :: e) HH1).
destruct HH2.
rewrite H4 in H3.
inversion H3.
destruct H4.
rewrite H4 in H3.
inversion H3.
destruct H4.
rewrite H4 in H3.
inversion H3.
rewrite H4 in H3.
inversion H3.
assert( HH1 := list_cardinal_aux1 (a :: p :: l) H3).
intuition.
Qed.

Lemma matroid2 : forall e e', inclA eq e e' -> rkl(e)<=rkl(e').
Proof.
intros;case_eq e;case_eq e';

try my_inAO;my_rank.

my_rank;subst;unfold inclA in *;assert( HH := H p);my_inAO.
unfold rkl;my_rank;subst.
assert( HH := contains_four_non_coplanar_points_sublist (p0 :: p1 :: l1) (p :: nil) H H3);simpl in HH;my_rank.
assert( HH := contains_four_non_coplanar_points_sublist (p0 :: p1 :: l1) (p :: p2 :: l2) H H3);rewrite HH in H5;my_rank.
assert( HH := contains_four_non_coplanar_points_sublist (p0 :: p1 :: l1) (p :: p2 :: l2) H H3);rewrite HH in H5;my_rank.
assert( HH := contains_four_non_coplanar_points_sublist (p0 :: p1 :: l1) (p :: p2 :: l2) H H3);rewrite HH in H5;my_rank.
assert( HH := contains_three_non_collinear_points_sublist (p0 :: p1 :: l1) (p :: nil) H H4);simpl in HH;my_rank.
assert( HH := contains_three_non_collinear_points_sublist (p0 :: p1 :: l1) (p :: p2 :: l2) H H4);rewrite H7 in HH;my_rank.
assert( HH := contains_three_non_collinear_points_sublist (p0 :: p1 :: l1) (p :: p2 :: l2) H H4);rewrite H7 in HH;my_rank.
assert( HH := contains_two_distinct_points_sublist (p0 :: p1 :: l1) (p :: nil) H H5);simpl in HH;my_rank.
assert( HH := contains_two_distinct_points_sublist (p0 :: p1 :: l1) (p :: p2 :: l2) H H5);rewrite H9 in HH;my_rank.
Qed.

Lemma matroid3:
forall e e',
 rkl(e ++ e') + rkl(list_inter e e') <= rkl(e) + rkl(e').
Proof.
my_rank.
assert(HH0 := all_rank e).
assert(HH1 := all_rank e').
progress intuition.
- assert(HH0 := rk_nil e H);assert(HH1 := rk_nil e' H0);
subst;my_rank.
- assert(HH0 := rk_nil e H);subst;simpl;my_rank.
- assert(HH0 := rk_nil e H);subst;simpl;my_rank.
- assert(HH0 := rk_nil e H);subst;simpl;my_rank.
- assert(HH0 := rk_nil e H);subst;simpl;my_rank.
- assert(HH0 := rk_nil e' H0);
  assert(HH1 := list_inter_reverse e nil);
  assert(HH2 := list_concat_reverse e nil);
  subst;rewrite HH1;rewrite HH2;simpl;my_rank.
- assert(HH0 := rk_nil e' H0);
  assert(HH1 := list_inter_reverse e nil);
  assert(HH2 := list_concat_reverse e nil);
  subst;rewrite HH1;rewrite HH2;simpl;my_rank.
- assert(HH0 := rk_nil e' H0);
  assert(HH1 := list_inter_reverse e nil);
  assert(HH2 := list_concat_reverse e nil);
  subst;rewrite HH1;rewrite HH2;simpl;my_rank.
- assert(HH0 := rk_nil e' H0);
  assert(HH1 := list_inter_reverse e nil);
  assert(HH2 := list_concat_reverse e nil);
  subst;rewrite HH1;rewrite HH2;simpl;my_rank.
- rewrite H;rewrite H1;apply matroid3_aux24;my_rank.
- rewrite H0;rewrite H1;apply matroid3_aux17;my_rank.
- rewrite H;rewrite H1;apply matroid3_aux29;my_rank.
- rewrite H;rewrite H1;apply matroid3_aux34;my_rank.
- rewrite H;rewrite H0;apply matroid3_aux24_bis;my_rank.
- rewrite H;rewrite H1;apply matroid3_aux24_bis_bis;my_rank.
- rewrite H;rewrite H1;apply matroid3_aux24_bis_bis_bis;my_rank.
- rewrite H0;rewrite H1;apply matroid3_aux17_bis;my_rank.
- rewrite H;rewrite H0;apply matroid3_aux29_bis;my_rank.
- rewrite H;rewrite H0;apply matroid3_aux34_bis;my_rank.
- rewrite H;rewrite H1;apply matroid3_aux17_bis_bis;my_rank.
- rewrite H;rewrite H1;apply matroid3_aux17_bis_bis_bis;my_rank.
- rewrite H;rewrite H0;apply matroid3_aux29_bis_bis;my_rank.
- rewrite H;rewrite H0;apply matroid3_aux34_bis_bis;my_rank.
- rewrite H;rewrite H0;apply matroid3_aux29_bis_bis_bis;my_rank.
- rewrite H;rewrite H0;apply matroid3_aux34_bis_bis_bis;my_rank.
Qed.

Lemma rk_singleton_ge : forall p:Point, rkl (p::nil) >=1.
Proof.
my_rank.
Qed.

Lemma rk_couple_ge : forall p q:Point,~(p[==]q)-> rkl(p::q::nil)>=2.
Proof.
my_rank;
case (eq_dec_u p q);
my_rank;simpl;my_rank.
Qed.

Lemma rk_pasch : forall a b c d, 
rkl (a :: b :: c :: d :: nil) <= 3 -> 
exists e, rkl (a :: b :: e :: nil) = 2 /\ rkl (c :: d :: e :: nil) = 2.
Proof.
intros.
unfold rkl in H.
generalize H.
case_eq(contains_four_non_coplanar_points (a :: b :: c :: d :: nil)).
intros.
inversion H1. inversion H3. inversion H5. inversion H7.
case_eq(contains_three_non_collinear_points (a :: b :: c :: d :: nil)).
intros.
rewrite contains_1 in H0.
rewrite contains_2_cop in H1.
destruct H0.
destruct H0.
destruct H0.
destruct H0.
destruct H3.
destruct H4.
assert(HH : InA eq a (a :: b :: c :: d :: nil));[my_inA|].
assert(HH0 : InA eq b (a :: b :: c :: d :: nil));[my_inA|].
assert(HH1 : InA eq c (a :: b :: c :: d :: nil));[my_inA|].
assert(HH2 : InA eq d (a :: b :: c :: d :: nil));[my_inA|].
inversion H0;subst.
inversion H3;subst.
assert(HH3 := col_1 a x1).
rewrite HH3 in H5;inversion H5.
inversion H7;subst.
inversion H4;subst.
assert(HH3 := col_1 a b).
rewrite <-col_exchange2 in HH3;rewrite HH3 in H5;inversion H5.
inversion H8;subst.
assert(HH3 := col_2 a b).
rewrite HH3 in H5;inversion H5.
inversion H9;subst.
generalize H5.
unfold collinear.
case_eq(eq_dec_u a b).
intros.
inversion H10.
intros.
assert(HH3 := H1 a b c d HH HH0 HH1 HH2).
assert(HH4 := rk_pasch_aux2 a b c d HH3 H5);my_rank.
inversion H10;subst.
assert(HH3 := H1 a b d c HH HH0 HH2 HH1).
assert(HH4 := rk_pasch_aux2 a b d c HH3 H5).
destruct HH4. exists x.
assert(HH5 : equivlistA eq (c :: d :: x :: nil) (d :: c :: x :: nil));[my_inA|];rewrite HH5;my_rank.
inversion H11.
inversion H8;subst.
inversion H4;subst.
assert(HH3 := col_1 a c).
rewrite <-col_exchange2 in HH3;rewrite HH3 in H5;inversion H5.
inversion H9;subst.
rewrite col_exchange2 in H5.
assert(HH3 := H1 a b c d HH HH0 HH1 HH2).
assert(HH4 := rk_pasch_aux2 a b c d HH3 H5);my_rank.
inversion H10;subst.
assert(HH3 := col_2 a c).
rewrite HH3 in H5;inversion H5.
inversion H11;subst.
rewrite col_exchange in H5;rewrite col_exchange2 in H5.
assert(HH3 := H1 c d a b HH1 HH2 HH HH0).
assert(HH4 := rk_pasch_aux2 c d a b HH3 H5).
destruct HH4. exists x.
my_rank.
inversion H12.
inversion H9;subst.
inversion H4;subst.
assert(HH3 := col_1 a d).
rewrite <-col_exchange2 in HH3;rewrite HH3 in H5;inversion H5.
inversion H10;subst.
rewrite col_exchange2 in H5.
assert(HH3 := H1 a b d c HH HH0 HH2 HH1).
assert(HH4 := rk_pasch_aux2 a b d c HH3 H5).
destruct HH4. exists x.
assert(HH5 : equivlistA eq (c :: d :: x :: nil) (d :: c :: x :: nil));[my_inA|];rewrite HH5;my_rank.
inversion H11;subst.
rewrite col_exchange in H5;rewrite col_exchange2 in H5.
assert(HH3 := H1 d c a b HH2 HH1 HH HH0).
assert(HH4 := rk_pasch_aux2 d c a b HH3 H5).
destruct HH4. exists x.
assert(HH5 : equivlistA eq (c :: d :: x :: nil) (d :: c :: x :: nil));[my_inA|];rewrite HH5;my_rank.
inversion H12;subst.
assert(HH3 := col_2 a d).
rewrite HH3 in H5;inversion H5.
inversion H13.
inversion H10.
inversion H7;subst.
inversion H3;subst.
inversion H4;subst.
assert(HH3 := col_2 b a).
rewrite HH3 in H5;inversion H5.
inversion H8;subst.
assert(HH3 := col_1 b a).
rewrite col_exchange2 in HH3;rewrite HH3 in H5;inversion H5.
inversion H9;subst.
assert(HH3 := H1 b a c d HH0 HH HH1 HH2).
assert(HH4 := rk_pasch_aux2 b a c d HH3 H5);my_rank.
destruct HH4. exists x.
assert(HH5 : equivlistA eq (a :: b :: x :: nil) (b :: a :: x :: nil));[my_inA|];rewrite HH5;my_rank.
inversion H10;subst.
assert(HH3 := H1 b a d c HH0 HH HH2 HH1).
assert(HH4 := rk_pasch_aux2 b a d c HH3 H5);my_rank.
destruct HH4. exists x.
assert(HH5 : equivlistA eq (a :: b :: x :: nil) (b :: a :: x :: nil));[my_inA|];rewrite HH5;
assert(HH6 : equivlistA eq (c :: d :: x :: nil) (d :: c :: x :: nil));[my_inA|];rewrite HH6;my_rank.
inversion H11.
inversion H8;subst.
assert(HH3 := col_1 b x1).
rewrite HH3 in H5;inversion H5.
inversion H9;subst.
inversion H4;subst.
rewrite col_exchange2 in H5.
assert(HH3 := H1 b a c d HH0 HH HH1 HH2).
assert(HH4 := rk_pasch_aux2 b a c d HH3 H5);my_rank.
destruct HH4. exists x.
assert(HH5 : equivlistA eq (a :: b :: x :: nil) (b :: a :: x :: nil));[my_inA|];rewrite HH5;my_rank.
inversion H10;subst.
assert(HH3 := col_1 b c).
rewrite col_exchange2 in HH3;rewrite HH3 in H5;inversion H5.
inversion H11;subst.
assert(HH3 := col_2 b c).
rewrite HH3 in H5;inversion H5.
inversion H12;subst.
rewrite col_exchange in H5;rewrite col_exchange2 in H5.
assert(HH3 := H1 c d b a HH1 HH2 HH0 HH).
assert(HH4 := rk_pasch_aux2 c d b a HH3 H5).
destruct HH4. exists x.
assert(HH5 : equivlistA eq (a :: b :: x :: nil) (b :: a :: x :: nil));[my_inA|];rewrite HH5;my_rank.
inversion H13.
inversion H10;subst.
inversion H4;subst.
rewrite col_exchange2 in H5.
assert(HH3 := H1 b a d c HH0 HH HH2 HH1).
assert(HH4 := rk_pasch_aux2 b a d c HH3 H5).
destruct HH4. exists x.
assert(HH5 : equivlistA eq (a :: b :: x :: nil) (b :: a :: x :: nil));[my_inA|];rewrite HH5;
assert(HH6 : equivlistA eq (c :: d :: x :: nil) (d :: c :: x :: nil));[my_inA|];rewrite HH6;my_rank.
inversion H11;subst.
assert(HH3 := col_1 b d).
rewrite col_exchange2 in HH3;rewrite HH3 in H5;inversion H5.
inversion H12;subst.
rewrite col_exchange in H5;rewrite col_exchange2 in H5.
assert(HH3 := H1 d c b a HH2 HH1 HH0 HH).
assert(HH4 := rk_pasch_aux2 d c b a HH3 H5).
destruct HH4. exists x.
assert(HH5 : equivlistA eq (a :: b :: x :: nil) (b :: a :: x :: nil));[my_inA|];rewrite HH5;
assert(HH6 : equivlistA eq (c :: d :: x :: nil) (d :: c :: x :: nil));[my_inA|];rewrite HH6;my_rank.
inversion H13;subst.
assert(HH3 := col_2 b d).
rewrite HH3 in H5;inversion H5.
inversion H14.
inversion H11.
inversion H8;subst.
inversion H3;subst.
inversion H4;subst.
assert(HH3 := col_2 c a).
rewrite HH3 in H5;inversion H5.
inversion H9;subst.
rewrite col_exchange in H5;rewrite col_exchange2 in H5.
assert(HH3 := H1 a b c d HH HH0 HH1 HH2).
assert(HH4 := rk_pasch_aux2 a b c d HH3 H5);my_rank.
inversion H10;subst.
assert(HH3 := col_1 c a).
rewrite col_exchange2 in HH3;rewrite HH3 in H5;inversion H5.
inversion H11;subst.
rewrite col_exchange2 in H5.
assert(HH3 := H1 c d a b HH1 HH2 HH HH0).
assert(HH4 := rk_pasch_aux2 c d a b HH3 H5).
destruct HH4. exists x.
my_rank.
inversion H12.
inversion H9;subst.
inversion H4;subst.
rewrite col_exchange in H5;rewrite col_exchange2 in H5.
assert(HH3 := H1 b a c d HH0 HH HH1 HH2).
assert(HH4 := rk_pasch_aux2 b a c d HH3 H5).
destruct HH4. exists x.
assert(HH5 : equivlistA eq (a :: b :: x :: nil) (b :: a :: x :: nil));[my_inA|];rewrite HH5;my_rank.
inversion H10;subst.
assert(HH3 := col_2 c b).
rewrite HH3 in H5;inversion H5.
inversion H11;subst.
assert(HH3 := col_1 c b).
rewrite col_exchange2 in HH3;rewrite HH3 in H5;inversion H5.
inversion H12;subst.
rewrite col_exchange2 in H5.
assert(HH3 := H1 c d b a HH1 HH2 HH0 HH).
assert(HH4 := rk_pasch_aux2 c d b a HH3 H5).
destruct HH4. exists x.
assert(HH5 : equivlistA eq (a :: b :: x :: nil) (b :: a :: x :: nil));[my_inA|];rewrite HH5;my_rank.
inversion H13.
inversion H10;subst.
assert(HH3 := col_1 c x1).
rewrite HH3 in H5;inversion H5.
inversion H11;subst.
inversion H4;subst.
assert(HH3 := H1 c d a b HH1 HH2 HH HH0).
assert(HH4 := rk_pasch_aux2 c d a b HH3 H5).
destruct HH4. exists x.
my_rank.
inversion H12;subst.
assert(HH3 := H1 c d b a HH1 HH2 HH0 HH).
assert(HH4 := rk_pasch_aux2 c d b a HH3 H5).
destruct HH4. exists x.
assert(HH5 : equivlistA eq (a :: b :: x :: nil) (b :: a :: x :: nil));[my_inA|];rewrite HH5;my_rank.
inversion H13;subst.
assert(HH3 := col_1 c d).
rewrite col_exchange2 in HH3;rewrite HH3 in H5;inversion H5.
inversion H14;subst.
assert(HH3 := col_2 c d).
rewrite HH3 in H5;inversion H5.
inversion H15.
inversion H12.
inversion H9;subst.
inversion H3;subst.
inversion H4;subst.
assert(HH3 := col_2 d a).
rewrite HH3 in H5;inversion H5.
inversion H10;subst.
rewrite col_exchange in H5;rewrite col_exchange2 in H5.
assert(HH3 := H1 a b d c HH HH0 HH2 HH1).
assert(HH4 := rk_pasch_aux2 a b d c HH3 H5).
destruct HH4. exists x.
assert(HH5 : equivlistA eq (c :: d :: x :: nil) (d :: c :: x :: nil));[my_inA|];rewrite HH5;my_rank.
inversion H11;subst.
rewrite col_exchange2 in H5.
assert(HH3 := H1 d c a b HH2 HH1 HH HH0).
assert(HH4 := rk_pasch_aux2 d c a b HH3 H5).
destruct HH4. exists x.
assert(HH5 : equivlistA eq (c :: d :: x :: nil) (d :: c :: x :: nil));[my_inA|];rewrite HH5;my_rank.
inversion H12;subst.
assert(HH3 := col_1 d a).
rewrite col_exchange2 in HH3;rewrite HH3 in H5;inversion H5.
inversion H13.
inversion H10;subst.
inversion H4;subst.
rewrite col_exchange in H5;rewrite col_exchange2 in H5.
assert(HH3 := H1 b a d c HH0 HH HH2 HH1).
assert(HH4 := rk_pasch_aux2 b a d c HH3 H5).
destruct HH4. exists x.
assert(HH5 : equivlistA eq (a :: b :: x :: nil) (b :: a :: x :: nil));[my_inA|];rewrite HH5;
assert(HH6 : equivlistA eq (c :: d :: x :: nil) (d :: c :: x :: nil));[my_inA|];rewrite HH6;my_rank.
inversion H11;subst.
assert(HH3 := col_2 d b).
rewrite HH3 in H5;inversion H5.
inversion H12;subst.
rewrite col_exchange2 in H5.
assert(HH3 := H1 d c b a HH2 HH1 HH0 HH).
assert(HH4 := rk_pasch_aux2 d c b a HH3 H5).
destruct HH4. exists x.
assert(HH5 : equivlistA eq (a :: b :: x :: nil) (b :: a :: x :: nil));[my_inA|];rewrite HH5;
assert(HH6 : equivlistA eq (c :: d :: x :: nil) (d :: c :: x :: nil));[my_inA|];rewrite HH6;my_rank.
inversion H13;subst.
assert(HH3 := col_1 d b).
rewrite col_exchange2 in HH3.
rewrite HH3 in H5;inversion H5.
inversion H14.
inversion H11;subst.
inversion H4;subst.
assert(HH3 := H1 d c a b HH2 HH1 HH HH0).
assert(HH4 := rk_pasch_aux2 d c a b HH3 H5).
destruct HH4. exists x.
assert(HH5 : equivlistA eq (c :: d :: x :: nil) (d :: c :: x :: nil));[my_inA|];rewrite HH5;my_rank.
inversion H12;subst.
assert(HH3 := H1 d c b a HH2 HH1 HH0 HH).
assert(HH4 := rk_pasch_aux2 d c b a HH3 H5).
destruct HH4. exists x.
assert(HH5 : equivlistA eq (a :: b :: x :: nil) (b :: a :: x :: nil));[my_inA|];rewrite HH5;
assert(HH6 : equivlistA eq (c :: d :: x :: nil) (d :: c :: x :: nil));[my_inA|];rewrite HH6;my_rank.
inversion H13;subst.
assert(HH3 := col_2 d c).
rewrite HH3 in H5;inversion H5.
inversion H14;subst.
assert(HH3 := col_1 d c).
rewrite col_exchange2 in HH3;rewrite HH3 in H5;inversion H5.
inversion H15.
inversion H12;subst.
assert(HH3 := col_1 d x1).
rewrite HH3 in H5;inversion H5.
inversion H13.
inversion H10.
case_eq(contains_two_distinct_points (a :: b :: c :: d :: nil)).
intros.
assert(HH := matroid3_aux17_bis_aux1 (a :: b :: c :: d :: nil) H0).
rewrite contains_2 in H1.
assert(HH0 : InA eq a (a :: b :: c :: d :: nil));[my_inA|].
assert(HH1 : InA eq b (a :: b :: c :: d :: nil));[my_inA|].
assert(HH2 : InA eq c (a :: b :: c :: d :: nil));[my_inA|].
assert(HH3 : InA eq d (a :: b :: c :: d :: nil));[my_inA|].
destruct HH.
destruct H4.
my_rank.
case_eq(eq_dec_u a b);case_eq(eq_dec_u c d).
assert(HH4 := a1_exist a b).
destruct HH4.
assert(HH4 := a3_1 x1).
destruct HH4.
destruct s.
destruct s.
destruct a1.
destruct H8.
destruct H9.
destruct H10.
destruct H11.
intros.
rewrite e.
rewrite e0.
case_eq(eq_dec_u b x2);case_eq(eq_dec_u b x3);
case_eq(eq_dec_u d x2);case_eq(eq_dec_u d x3).
intros;clear H15;rewrite e2 in e1;contradiction.
intros;clear H17;rewrite e3 in e2;contradiction.
intros;clear H17;rewrite e3 in e2;contradiction.
intros;clear H17;rewrite e2 in e1;contradiction.
intros;clear H15;rewrite e2 in e1;contradiction.
intros;rewrite e1;rewrite e2;exists x3;
split;apply rk_pasch_aux0;my_rank.
intros;rewrite e1;rewrite e2;exists x4;
split;apply rk_pasch_aux0;my_rank.
intros;rewrite e1;exists x3;
split;apply rk_pasch_aux0;my_rank.
intros;rewrite e1;rewrite e3;exists x4;
split;apply rk_pasch_aux0;my_rank.
intros;rewrite e1;rewrite e2;exists x4;
split;apply rk_pasch_aux0;my_rank.
intros;rewrite e1;rewrite e2;exists x2;
split;apply rk_pasch_aux0;my_rank.
intros;rewrite e1;exists x2;
split;apply rk_pasch_aux0;my_rank.
intros;clear H15;rewrite e2 in e1;contradiction.
intros;rewrite e1;exists x3;
split;apply rk_pasch_aux0;my_rank.
intros;rewrite e1;exists x2;
split;apply rk_pasch_aux0;my_rank.
intros;exists x3;
split;apply rk_pasch_aux0;my_rank.
intros.
case_eq(eq_dec_u a c).
intros.
exists d.
rewrite <-e;rewrite e0.
split;apply rk_pasch_aux0;my_rank.
intros.
exists c.
assert(HH4 : equivlistA eq (a :: b :: c :: nil) (a :: c :: b :: nil));[my_inA|].
split.
rewrite HH4;apply rk_pasch_aux3;my_rank.
apply rk_pasch_aux0;my_rank.
intros.
case_eq(eq_dec_u a c).
intros.
exists b.
rewrite <-e;rewrite <-e0.
split;apply rk_pasch_aux0;my_rank.
intros.
exists a.
split.
apply rk_pasch_aux0;my_rank.
rewrite <-e.
apply rk_pasch_aux0;my_rank.
intros.
exists a.
split.
apply rk_pasch_aux0;my_rank.
assert(HH4 := H1 c d a HH2 HH3 HH0).
apply rk_pasch_aux3;my_rank.

intros.
assert(HH4 := a1_exist a b).
destruct HH4.
assert(HH4 := a3_1 x).
destruct HH4;destruct s;destruct s;destruct a1.
destruct H5;destruct H6;destruct H7;destruct H8.
simpl in H0.
generalize H0.
case_eq(eq_dec_u a b);case_eq(eq_dec_u b c);case_eq(eq_dec_u c d).
intros.
rewrite e1;rewrite e0;rewrite e.
case_eq(eq_dec_u d x0);case_eq(eq_dec_u d x1).
intros;clear H14;rewrite e3 in e2;my_rank.
intros;exists x1;split;apply rk_pasch_aux0;my_rank.
intros;exists x0;split;apply rk_pasch_aux0;my_rank.
intros;exists x1;split;apply rk_pasch_aux0;my_rank.
intros;inversion H13.
intros;inversion H13.
intros;inversion H13.
intros;inversion H13.
intros;inversion H13.
intros;inversion H13.
intros;inversion H13.
Qed.

Lemma rk_three_points : forall a b, exists c, 
rkl(a :: b :: c :: nil) = 2 /\ rkl(b :: c :: nil) = 2 /\ rkl(a :: c :: nil) = 2.
Proof.
intros.
assert( HH0 := a1_exist a b).
destruct HH0.
destruct a0.
assert( HH0 := a3_1 x).
destruct HH0.
destruct s.
destruct s.
destruct a0.
destruct H2.
destruct H3.
destruct H4.
destruct H5.
case_eq (eq_dec_u a x0).
case_eq (eq_dec_u b x1).
exists x2.
intros.
rewrite e.
rewrite e0.
simpl.
case_eq (coplanar x0 x1 x2 x2).
intros.
case_eq (collinear x0 x1 x2).
intros.
case_eq (eq_dec_u x0 x1).
intros.
contradiction.
intros.
case_eq (eq_dec_u x1 x2).
intros.
contradiction.
intros.
case_eq (eq_dec_u x0 x2).
intros.
contradiction.
intros.
split.
reflexivity.
split.
reflexivity.
reflexivity.
unfold collinear.
case_eq (eq_dec_u x0 x1).
intros.
inversion H11.
destruct (a1_exist x0 x1).
simpl.
case_eq (incid_dec x2 x3).
intros.
inversion H12.
intros.
destruct a0.
assert( HH0 := uniqueness x0 x1 x x3 H4 H5 H13 H14).
destruct HH0.
contradiction.
clear H10.
rewrite <-H15 in *.
contradiction.
unfold coplanar.
case_eq (eq_dec_u x0 x1).
intros.
inversion H10.
case_eq (eq_dec_u x2 x2).
intros.
inversion H11.
intros.
apply False_ind.
apply n.
reflexivity.
intros.
exists x1.
simpl.
split.
case_eq (coplanar a b x1 x1).
case_eq (collinear a b x1).
case_eq (eq_dec_u a b).
case_eq (eq_dec_u b x1).
intros.
clear H7 H8 H9 H10.
rewrite e in e1.
rewrite e0 in e1.
contradiction.
intros.
reflexivity.
intros.
reflexivity.
unfold collinear.
case_eq (eq_dec_u a b).
intros.
inversion H10.
destruct (a1_exist a b).
simpl.
case_eq (incid_dec x1 x3).
intros.
inversion H11.
intros.
destruct a0.
assert( HH0 := uniqueness a b x x3 H H0 H13 H14).
destruct HH0.
contradiction.
clear H9.
rewrite H15 in *.
contradiction.
intros.
assert(HH := cop_3 a b x1).
rewrite HH in H9.
inversion H9.
case_eq (eq_dec_u b x1).
intros.
contradiction.
intros.
split.
reflexivity.
case_eq (eq_dec_u a x1).
intros.
clear H10.
rewrite e in e0.
contradiction.
intros.
reflexivity.
intros.
case_eq (eq_dec_u b x1).
intros.
exists x0.
simpl.
split.
case_eq (coplanar a b x0 x0).
intros.
case_eq (collinear a b x0).
intros.
case_eq (eq_dec_u a b).
case_eq (eq_dec_u b x0).
intros.
clear H8.
rewrite e0 in e.
contradiction.
intros.
reflexivity.
intros.
reflexivity.
unfold collinear.
case_eq (eq_dec_u a b).
intros.
inversion H11.
destruct (a1_exist a b).
simpl.
case_eq (incid_dec x0 x3).
intros.
inversion H12.
intros.
destruct a0.
assert( HH0 := uniqueness a b x x3 H H0 H13 H14).
destruct HH0.
contradiction.
clear H10.
rewrite <-H15 in n0.
contradiction.
intros.
assert(HH := cop_3 a b x0).
rewrite HH in H9.
inversion H9.
case_eq (eq_dec_u b x0).
intros.
clear H8.
rewrite e0 in e.
contradiction.
intros.
split.
reflexivity.
case_eq (eq_dec_u a x0).
intros.
contradiction.
reflexivity.
intros.
case_eq (eq_dec_u b x0).
case_eq (eq_dec_u a x1).
intros.
exists x2.
simpl.
split.
case_eq (coplanar a b x2 x2).
case_eq (collinear a b x2).
case_eq (eq_dec_u a b).
case_eq (eq_dec_u b x2).
intros.
clear H11.
rewrite e0 in e1.
contradiction.
intros.
reflexivity.
intros.
reflexivity.
unfold collinear.
case_eq (eq_dec_u a b).
intros.
inversion H12.
destruct (a1_exist a b).
simpl.
case_eq (incid_dec x2 x3).
intros.
inversion H13.
intros.
destruct a0.
assert( HH0 := uniqueness a b x x3 H H0 H15 H16).
destruct HH0.
contradiction.
clear H11.
rewrite H17 in *.
contradiction.
intros.
assert(HH := cop_3 a b x2).
rewrite HH in H11.
inversion H11.
case_eq (eq_dec_u b x2).
intros.
clear H11.
rewrite e0 in e1.
contradiction.
intros.
split.
reflexivity.
case_eq (eq_dec_u a x2).
intros.
clear H12.
rewrite e in e1.
contradiction.
intros.
reflexivity.
intros.
exists x1.
split.
simpl.
case_eq (coplanar a b x1 x1).
intros.
case_eq (collinear a b x1).
intros.
case_eq (eq_dec_u a b).
intros.
case_eq (eq_dec_u b x1).
intros.
contradiction.
intros.
reflexivity.
intros.
reflexivity.
intros.
generalize H12.
unfold collinear.
case_eq (eq_dec_u a b).
intros.
inversion H14.
destruct (a1_exist a b).
simpl.
case_eq( incid_dec x1 x3).
intros.
inversion H15.
intros.
destruct a0.
assert( HH0 := uniqueness a b x x3 H H0 H16 H17).
destruct HH0.
contradiction.
clear H13.
rewrite <-H18 in n2.
contradiction.
intros.
assert(HH0 := cop_3 a b x1).
rewrite HH0 in H11.
inversion H11.
split.
simpl.
case_eq (eq_dec_u b x1).
intros.
contradiction.
intros.
reflexivity.
simpl.
case_eq (eq_dec_u a x1).
intros.
contradiction.
intros.
reflexivity.
intros.
exists x0.
split.
simpl.
case_eq (coplanar a b x0 x0).
intros.
case_eq (collinear a b x0).
intros.
case_eq (eq_dec_u a b).
intros.
case_eq (eq_dec_u b x0).
intros.
contradiction.
intros.
reflexivity.
intros.
reflexivity.
intros.
generalize H11.
unfold collinear.
case_eq (eq_dec_u a b).
intros.
inversion H13.
intro.
destruct (a1_exist a b).
simpl.
case_eq(incid_dec x0 x3).
intros.
inversion H14.
intros.
destruct a0.
assert( HH0 := uniqueness a b x x3 H H0 H15 H16).
destruct HH0.
contradiction.
clear H12.
rewrite <-H17 in n3.
contradiction.
intros.
assert(HH := cop_3 a b x0).
rewrite HH in H10.
inversion H10.
split.
simpl.
case_eq (eq_dec_u b x0).
intros.
contradiction.
intros.
reflexivity.
simpl.
case_eq (eq_dec_u a x0).
intros.
contradiction.
intros.
reflexivity.
Qed.

Lemma rk_lower_dim : exists a b c d, rkl(a :: b :: c :: d :: nil) = 4.
Proof.
intros.
assert( HH0 := a3_2).
destruct HH0.
destruct s.
case_eq(eq_dec_p x x0).
intros.
clear H.
unfold Intersect in i.
destruct i.
my_rank.
assert(HH := n x1).
apply False_ind.
apply HH.
my_rank.
intros.
assert(HH := a3_1 x).
assert(HH0 := a3_1 x0).
destruct HH. destruct s. destruct s. destruct a.
destruct HH0. destruct s. destruct s. destruct a.
my_rank.
exists x1. exists x2. exists x4. exists x5.
simpl.
case_eq(coplanar x1 x2 x4 x4).
case_eq(coplanar x1 x2 x5 x4).
case_eq(coplanar x1 x2 x4 x5).
case_eq(coplanar x1 x2 x5 x5).
case_eq(coplanar x1 x4 x5 x5).
case_eq(coplanar x2 x4 x5 x5).
intros.
generalize H13.
unfold coplanar.
case_eq(eq_dec_u x2 x4).
intros.
rewrite e in *.
assert(Intersect x x0).
unfold Intersect.
exists x4.
solve[intuition].
contradiction.
case_eq(eq_dec_u x5 x5).
intros.
case_eq(collinear x1 x2 x4).
unfold collinear.
case_eq(eq_dec_u x1 x2).
intros.
contradiction.
destruct (a1_exist x1 x2).
simpl.
case_eq(incid_dec x4 x7).
intros.
destruct a.
assert(HH0 := uniqueness x1 x2 x x7 H9 H10 H24 H25).
destruct HH0.
contradiction.
clear H21.
rewrite <-H26 in *.
assert(HH : Intersect x x0).
unfold Intersect.
exists x4.
solve[intuition].
contradiction.
intros.
inversion H23.
intros.
generalize H13.
unfold coplanar.
case_eq(eq_dec_u x1 x4).
intros.
rewrite e0 in *.
assert(Intersect x x0).
unfold Intersect.
exists x4.
solve[intuition].
contradiction.
case_eq(eq_dec_u x5 x5).
intros.
generalize H14.
unfold coplanar.
case_eq(eq_dec_u x1 x2).
intros.
contradiction.
case_eq(eq_dec_u x5 x5).
intros.
generalize H15.
unfold coplanar.
case_eq(eq_dec_u x1 x2).
intros.
contradiction.
case_eq(eq_dec_u x4 x5).
intros.
contradiction.
destruct(a1_exist x1 x2).
destruct(a1_exist x4 x5).
simpl.
case_eq(eq_dec_l x7 x8).
intros.
rewrite e2 in *.
destruct a.
assert(HH := uniqueness x1 x2 x x8 H9 H10 H32 H33).
destruct HH.
contradiction.
rewrite <-H34 in *.
assert(Intersect x x0).
unfold Intersect.
exists x4.
solve[intuition].
contradiction.
case_eq(eq_dec_p x7 x8).
intros.
destruct a.
destruct a0.
assert(HH := uniqueness x1 x2 x x7 H9 H10 H33 H34).
destruct HH.
contradiction.
assert(HH := uniqueness x4 x5 x0 x8 H5 H6 H35 H36).
destruct HH.
contradiction.
clear H28.
rewrite <-H37 in *.
rewrite <-H38 in *.
contradiction.
intros.
inversion H32.
intros.
contradiction.
intros.
contradiction.
intros.
apply False_ind.
apply n1.
reflexivity.
solve[intuition].
solve[intuition].
solve[intuition].
solve[intuition].
solve[intuition].
solve[intuition].
Qed.

Lemma rk_upper_dim : forall a b c d e f,
rkl(a :: b :: nil) = 2 /\ rkl(c :: d :: nil) = 2 /\ rkl(e :: f :: nil) = 2 /\
rkl(a :: b :: c :: d :: nil) >= 3 /\ rkl(a :: b :: e :: f :: nil) >= 3 /\ rkl(c :: d :: e :: f :: nil) >= 3 ->
exists j1 : Point, exists j2 : Point, exists j3 : Point, 
rkl (a :: b :: j1 :: nil) = 2 /\ rkl (c :: d :: j2 :: nil) = 2 /\ rkl (e :: f :: j3 :: nil) = 2 /\ rkl (j1 :: j2 :: j3 :: nil) <= 2.
Proof.
intros.
destruct H.
destruct H0.
destruct H1.
destruct H2.
destruct H3.
assert(H00 := H);clear H.
assert(H01 := H0);clear H0.
assert(H02 := H1);clear H1.
assert(H := H2);clear H2.
assert(H0 := H3);clear H3.
assert(H1 := H4);clear H4.
assert(HH := a3_3).
assert(HH0 := a1_exist a b).
destruct HH0.
assert(HH1 := a1_exist c d).
destruct HH1.
assert(HH2 := a1_exist e f).
destruct HH2.
assert(HH3 := HH x x0 x1);clear HH.
destruct a0.
destruct a1.
destruct a2.


case_eq(eq_dec_l x x0).
intros.
rewrite e0 in *;clear e0;clear H8.

generalize H.
unfold rkl.
case_eq(contains_four_non_coplanar_points (a :: b :: c :: d :: nil)).
intros.
clear H9.
assert(H9 := contains_four_to_three_aux' (a :: b :: c :: d :: nil) H8).
assert(HH4 := rk_upper_dim_aux a b c d H9).
destruct HH4.
assert(HH5 := rk_upper_dim_aux2 a b c x0 H2 H3 H4 H10).
inversion HH5.
destruct H10.
assert(HH5 := rk_upper_dim_aux2 a b d x0 H2 H3 H5 H10).
inversion HH5.
destruct H10.
assert(HH5 := rk_upper_dim_aux2 a c d x0 H2 H4 H5 H10).
inversion HH5.
assert(HH5 := rk_upper_dim_aux2 b c d x0 H3 H4 H5 H10).
inversion HH5.
intro.
case_eq(contains_three_non_collinear_points (a :: b :: c :: d :: nil)).
intros.
assert(HH4 := rk_upper_dim_aux a b c d H9).
destruct HH4.
assert(HH5 := rk_upper_dim_aux2 a b c x0 H2 H3 H4 H11).
inversion HH5.
destruct H11.
assert(HH5 := rk_upper_dim_aux2 a b d x0 H2 H3 H5 H11).
inversion HH5.
destruct H11.
assert(HH5 := rk_upper_dim_aux2 a c d x0 H2 H4 H5 H11).
inversion HH5.
assert(HH5 := rk_upper_dim_aux2 b c d x0 H3 H4 H5 H11).
inversion HH5.
intro.
case_eq(contains_two_distinct_points (a :: b :: c :: d :: nil)).
intros.
inversion H11.
inversion H13.
inversion H15.
intros.
inversion H11.
inversion H13.
intros.

case_eq(eq_dec_l x x1).
intros.
rewrite e0 in *;clear e0;clear H9.

generalize H0.
unfold rkl.
case_eq(contains_four_non_coplanar_points (a :: b :: e :: f :: nil)).
intros.
clear H10.
assert(H10 := contains_four_to_three_aux' (a :: b :: e :: f :: nil) H9).
assert(HH4 := rk_upper_dim_aux a b e f H10).
destruct HH4.
assert(HH5 := rk_upper_dim_aux2 a b e x1 H2 H3 H6 H11).
inversion HH5.
destruct H11.
assert(HH5 := rk_upper_dim_aux2 a b f x1 H2 H3 H7 H11).
inversion HH5.
destruct H11.
assert(HH5 := rk_upper_dim_aux2 a e f x1 H2 H6 H7 H11).
inversion HH5.
assert(HH5 := rk_upper_dim_aux2 b e f x1 H3 H6 H7 H11).
inversion HH5.
intro.
case_eq(contains_three_non_collinear_points (a :: b :: e :: f :: nil)).
intros.
assert(HH4 := rk_upper_dim_aux a b e f H10).
destruct HH4.
assert(HH5 := rk_upper_dim_aux2 a b e x1 H2 H3 H6 H12).
inversion HH5.
destruct H12.
assert(HH5 := rk_upper_dim_aux2 a b f x1 H2 H3 H7 H12).
inversion HH5.
destruct H12.
assert(HH5 := rk_upper_dim_aux2 a e f x1 H2 H6 H7 H12).
inversion HH5.
assert(HH5 := rk_upper_dim_aux2 b e f x1 H3 H6 H7 H12).
inversion HH5.
intro.
case_eq(contains_two_distinct_points (a :: b :: e :: f :: nil)).
intros.
inversion H12.
inversion H14.
inversion H16.
intros.
inversion H12.
inversion H14.
intros.

case_eq(eq_dec_l x0 x1).
intros.
rewrite e0 in *;clear e0;clear H10.

generalize H1.
unfold rkl.
case_eq(contains_four_non_coplanar_points (c :: d :: e :: f :: nil)).
intros.
clear H11.
assert(H11 := contains_four_to_three_aux' (c :: d :: e :: f :: nil) H10).
assert(HH4 := rk_upper_dim_aux c d e f H11).
destruct HH4.
assert(HH5 := rk_upper_dim_aux2 c d e x1 H4 H5 H6 H12).
inversion HH5.
destruct H12.
assert(HH5 := rk_upper_dim_aux2 c d f x1 H4 H5 H7 H12).
inversion HH5.
destruct H12.
assert(HH5 := rk_upper_dim_aux2 c e f x1 H4 H6 H7 H12).
inversion HH5.
assert(HH5 := rk_upper_dim_aux2 d e f x1 H5 H6 H7 H12).
inversion HH5.
intro.
case_eq(contains_three_non_collinear_points (c :: d :: e :: f :: nil)).
intros.
assert(HH4 := rk_upper_dim_aux c d e f H11).
destruct HH4.
assert(HH5 := rk_upper_dim_aux2 c d e x1 H4 H5 H6 H13).
inversion HH5.
destruct H13.
assert(HH5 := rk_upper_dim_aux2 c d f x1 H4 H5 H7 H13).
inversion HH5.
destruct H13.
assert(HH5 := rk_upper_dim_aux2 c e f x1 H4 H6 H7 H13).
inversion HH5.
assert(HH5 := rk_upper_dim_aux2 d e f x1 H5 H6 H7 H13).
inversion HH5.
intro.
case_eq(contains_two_distinct_points (c :: d :: e :: f :: nil)).
intros.
inversion H13.
inversion H15.
inversion H17.
intros.
inversion H13.
inversion H15.
intros.

clear H8 H9 H10.
assert(HH4 : x <> x0 /\ x <> x1 /\ x0 <> x1).
intuition.
assert(HH5 := HH3 HH4).
destruct HH5.
destruct H8.
destruct H8.
destruct H8.
destruct H8.
destruct H9.
exists x3.
exists x4.
exists x5.
unfold Intersect_In in *.
destruct H8.
destruct H9.
destruct H10.
split.

unfold rkl.
case_eq(contains_four_non_coplanar_points (a :: b :: x3 :: nil)).
intros.
assert(H15 := contains_four_to_three_aux' (a :: b :: x3 :: nil) H14).
assert(H16 := rk_upper_dim_aux3 a b x3 H15).
assert(HH5 := rk_upper_dim_aux2 a b x3 x H2 H3 H8 H16).
inversion HH5.
intro.
case_eq(contains_three_non_collinear_points (a :: b :: x3 :: nil)).
intros.
assert(H16 := rk_upper_dim_aux3 a b x3 H15).
assert(HH5 := rk_upper_dim_aux2 a b x3 x H2 H3 H8 H16).
inversion HH5.
intros.
case_eq(contains_two_distinct_points (a :: b :: x3 :: nil)).
reflexivity.
intros.
assert(HH5 : contains_two_distinct_points (a :: b :: nil) = false).
unfold contains_two_distinct_points.
case_eq(eq_dec_u a b).
reflexivity.
intros.
generalize H16.
unfold contains_two_distinct_points.
case_eq(eq_dec_u a b).
case_eq(eq_dec_u b x3).
intros.
contradiction.
intros;assumption.
intros;assumption.
assert(HH6 := matroid3_aux9_bis_bis_reverse (a :: b :: nil) H00).
rewrite HH5 in HH6;inversion HH6.

split.
unfold rkl.
case_eq(contains_four_non_coplanar_points (c :: d :: x4 :: nil)).
intros.
assert(H15 := contains_four_to_three_aux' (c :: d :: x4 :: nil) H14).
assert(H16 := rk_upper_dim_aux3 c d x4 H15).
assert(HH5 := rk_upper_dim_aux2 c d x4 x0 H4 H5 H9 H16).
inversion HH5.
intro.
case_eq(contains_three_non_collinear_points (c :: d :: x4 :: nil)).
intros.
assert(H16 := rk_upper_dim_aux3 c d x4 H15).
assert(HH5 := rk_upper_dim_aux2 c d x4 x0 H4 H5 H9 H16).
inversion HH5.
intros.
case_eq(contains_two_distinct_points (c :: d :: x4 :: nil)).
reflexivity.
intros.
assert(HH5 : contains_two_distinct_points (c :: d :: nil) = false).
unfold contains_two_distinct_points.
case_eq(eq_dec_u c d).
reflexivity.
intros.
generalize H16.
unfold contains_two_distinct_points.
case_eq(eq_dec_u c d).
case_eq(eq_dec_u d x4).
intros.
contradiction.
intros;assumption.
intros;assumption.
assert(HH6 := matroid3_aux9_bis_bis_reverse (c :: d :: nil) H01).
rewrite HH5 in HH6;inversion HH6.

split.
unfold rkl.
case_eq(contains_four_non_coplanar_points (e :: f :: x5 :: nil)).
intros.
assert(H15 := contains_four_to_three_aux' (e :: f :: x5 :: nil) H14).
assert(H16 := rk_upper_dim_aux3 e f x5 H15).
assert(HH5 := rk_upper_dim_aux2 e f x5 x1 H6 H7 H10 H16).
inversion HH5.
intro.
case_eq(contains_three_non_collinear_points (e :: f :: x5 :: nil)).
intros.
assert(H16 := rk_upper_dim_aux3 e f x5 H15).
assert(HH5 := rk_upper_dim_aux2 e f x5 x1 H6 H7 H10 H16).
inversion HH5.
intros.
case_eq(contains_two_distinct_points (e :: f :: x5 :: nil)).
reflexivity.
intros.
assert(HH5 : contains_two_distinct_points (e :: f :: nil) = false).
unfold contains_two_distinct_points.
case_eq(eq_dec_u e f).
reflexivity.
intros.
generalize H16.
unfold contains_two_distinct_points.
case_eq(eq_dec_u e f).
case_eq(eq_dec_u f x5).
intros.
contradiction.
intros;assumption.
intros;assumption.
assert(HH6 := matroid3_aux9_bis_bis_reverse (e :: f :: nil) H02).
rewrite HH5 in HH6;inversion HH6.

unfold rkl.
case_eq(contains_four_non_coplanar_points (x3 :: x4 :: x5 :: nil)).
intros.
assert(H15 := contains_four_to_three_aux' (x3 :: x4 :: x5 :: nil) H14).
assert(H16 := rk_upper_dim_aux3 x3 x4 x5 H15).
assert(HH5 := rk_upper_dim_aux2 x3 x4 x5 x2 H11 H12 H13 H16).
inversion HH5.
intro.
case_eq(contains_three_non_collinear_points (x3 :: x4 :: x5 :: nil)).
intros.
assert(H16 := rk_upper_dim_aux3 x3 x4 x5 H15).
assert(HH5 := rk_upper_dim_aux2 x3 x4 x5 x2 H11 H12 H13 H16).
inversion HH5.
intros.
case_eq(contains_two_distinct_points (x3 :: x4 :: x5 :: nil)).
reflexivity.
intros.
intuition.
Qed.

Class MatroidRkEquiv `(Op : ObjectPoint) `(S : FSetSpecs Point) := {
rk : set Point -> nat
}.

End s_psEquivToRk.
