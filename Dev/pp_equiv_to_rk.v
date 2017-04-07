Require Export ProjectiveGeometry.Dev.projective_plane_axioms.
Require Export ProjectiveGeometry.Dev.projective_plane_rank_axioms.
Require Export ProjectiveGeometry.Dev.pp_equiv_rk_lemmas.

(*****************************************************************************)
(** Proof of projective plane rank axioms **)

Section s_ppEquivToRk.

Context `{PPR : ProjectivePlaneRank}.
Context `{EP : EqDecidability Point}.
Context `{OP : OrderedType Point}.

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
case_eq (contains_three_non_collinear_points (a :: p :: l)).
intros.
assert( HH0 := matroid3_aux9 (a :: p :: l) H0).
assert( HH1 := list_cardinal_aux3 (a :: p :: l) HH0).
intuition.
intros.
case_eq (contains_two_distinct_points (a :: p :: l)).
intros.
assert( HH0 := matroid3_aux2 (a :: p :: l) H1 H0).
assert( HH1 := list_cardinal_aux2 (a :: p :: l) HH0).
intuition.
intros.
assert( HH0 := matroid3_aux3 (a :: p :: l) H1).
destruct HH0.
rewrite <-H in H2.
assert( HH1 : (a :: e) <> nil).
intro.
inversion H3.
assert( HH2 := matroid3_aux3_bis (a :: e) HH1).
destruct HH2.
rewrite H3 in H2.
inversion H2.
destruct H3.
rewrite H3 in H2.
inversion H2.
rewrite H3 in H2.
inversion H2.
assert( HH1 := list_cardinal_aux1 (a :: p :: l) H2).
intuition.
Qed.

Lemma matroid2 : forall e e',  inclA eq e e' -> rkl(e)<=rkl(e').
Proof.
my_rank;unfold rkl;case_eq e;case_eq e';my_rank.
rewrite H1 in H;rewrite H0 in H;my_inA;assert( HH := H p);my_inA.
my_inA;assert( HH := H p);my_inA.
my_inA;assert( HH := H p);my_inA.
my_inA;assert( HH := H p);my_inA.
subst;assert( HH := contains_three_non_collinear_points_sublist (p0 :: p1 :: l1) (p :: nil) H H3);simpl in HH;my_rank.
subst;assert( HH := contains_three_non_collinear_points_sublist (p0 :: p1 :: l1) (p :: p2 :: l2) H H3);rewrite HH in H5;my_rank.
subst;assert( HH := contains_three_non_collinear_points_sublist (p0 :: p1 :: l1) (p :: p2 :: l2) H H3);rewrite HH in H5;my_rank.
subst;assert( HH := contains_two_distinct_points_sublist (p0 :: p1 :: l1) (p :: nil) H H4);simpl in HH;my_rank.
subst;assert( HH := contains_two_distinct_points_sublist (p0 :: p1 :: l1) (p :: p2 :: l2) H H4);rewrite H7 in HH;my_rank.
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
- rewrite H;rewrite H1;apply matroid3_aux20;my_rank.
- rewrite H0;rewrite H1;apply matroid3_aux14;my_rank.
- rewrite H0;rewrite H1;apply matroid3_aux26;my_rank.
- rewrite H;rewrite H0;apply matroid3_aux20_bis;my_rank.
- rewrite H;rewrite H0;apply matroid3_aux20_bis_bis;my_rank.
- rewrite H0;rewrite H1;apply matroid3_aux14_bis;my_rank.
- rewrite H0;rewrite H1;apply matroid3_aux26_bis;my_rank.
- rewrite H0;rewrite H1;apply matroid3_aux14_bis_bis;my_rank.
- rewrite H0;rewrite H1;apply matroid3_aux26_bis_bis;my_rank.
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

Lemma rk_inter : forall a b c d, exists j, rkl(a :: b :: j :: nil) = 2 /\ rkl(c :: d :: j :: nil) = 2.
Proof.
intros.
assert(HH0 := a1_exist a b).
destruct HH0.
assert(HH1 := a1_exist c d).
destruct HH1.
assert(HH2 := a3_1 x).
destruct HH2.
destruct s.
destruct s.
destruct a2.
destruct H0.
destruct H1.
destruct H2.
destruct H3.
assert(HH3 := a3_1 x0).
destruct HH3.
destruct s.
destruct s.
destruct a2.
destruct H6.
destruct H7.
destruct H8.
destruct H9.

case_eq (eq_dec_u a b).
case_eq (eq_dec_u c d).
case_eq (eq_dec_u a c).
intros.
clear H11 H12 H13.
case_eq (eq_dec_u a x1).
intros.
exists x2.
rewrite <-e1.
rewrite e0.
split.
apply rk_inter_aux0.
rewrite e2.
assumption.
apply rk_inter_aux0.
rewrite <-e0.
rewrite <-e.
rewrite e2.
assumption.
intros.
exists x1.
rewrite <-e1.
rewrite <-e0.
rewrite <-e.
split.
apply rk_inter_aux0.
assumption.
apply rk_inter_aux0.
assumption.
intros.
assert( HH0 := a1_exist a c).
destruct HH0.
destruct a2.
assert( HH1 := a3_1 x7).
destruct HH1.
destruct s.
destruct s.
destruct a2.
destruct H17.
destruct H18.
destruct H19.
destruct H20.
assert (HH : ~ x8[==]x9 /\ ~ x8[==]x10 /\ ~ x9[==]x10).
my_rank.
assert (HH0 := rk_inter_aux1 a c x8 x9 x10 n HH).
destruct HH0.
destruct H22.
exists x8.
rewrite <-e.
rewrite <-e0.
split.
apply rk_inter_aux0.
intro.
rewrite H24 in H22.
apply H22.
reflexivity.
apply rk_inter_aux0.
intro.
rewrite H24 in H23.
apply H23.
reflexivity.
destruct H22.
destruct H22.
exists x9.
rewrite <-e.
rewrite <-e0.
split.
apply rk_inter_aux0.
intro.
rewrite H24 in H22.
apply H22.
reflexivity.
apply rk_inter_aux0.
intro.
rewrite H24 in H23.
apply H23.
reflexivity.
destruct H22.
exists x10.
rewrite <-e.
rewrite <-e0.
split.
apply rk_inter_aux0.
intro.
rewrite H24 in H22.
apply H22.
reflexivity.
apply rk_inter_aux0.
intro.
rewrite H24 in H23.
apply H23.
reflexivity.
intros.
case_eq (eq_dec_u a c).
case_eq (eq_dec_u a d).
intros.
clear H11.
rewrite <-e0 in n.
rewrite <-e1 in n.
apply False_ind.
apply n.
reflexivity.
intros.
exists d.
rewrite <-e.
split.
apply rk_inter_aux0.
assumption.
apply rk_inter_aux0.
intro.
clear H11.
rewrite H15 in n.
apply n.
reflexivity.
intros.
exists c.
rewrite <-e.
split.
apply rk_inter_aux0.
assumption.
apply rk_inter_aux0.
assumption.
intros.
case_eq (eq_dec_u c d).
intros.
case_eq (eq_dec_u c a).
case_eq (eq_dec_u c b).
intros.
clear H11.
rewrite <-e0 in n.
rewrite <-e1 in n.
apply False_ind.
apply n.
reflexivity.
intros.
exists b.
rewrite <-e.
split.
apply rk_inter_aux0.
intro.
clear H11.
rewrite H15 in n.
apply n.
reflexivity.
apply rk_inter_aux0.
assumption.
intros.
exists a.
rewrite <-e.
split.
apply rk_inter_aux0.
assumption.
apply rk_inter_aux0.
assumption.
intros.
assert( HH0 := a2_exist x x0).
destruct HH0.
exists x7.
destruct a2.
simpl.
case_eq (collinear a b x7).
intros.
case_eq (eq_dec_u a b).
contradiction.
intros.
case_eq (collinear c d x7).
intros.
case_eq (eq_dec_u c d).
contradiction.
intros.
split.
reflexivity.
reflexivity.
intros.
generalize H17.
unfold collinear.
case_eq (eq_dec_u c d).
contradiction.
destruct (a1_exist c d).
simpl.
case_eq (incid_dec x7 x8).
intros.
inversion H20.
intros.
destruct a1.
destruct a2.
assert( HH0 := uniqueness c d x0 x8 H21 H22 H23 H24).
destruct HH0.
contradiction.
clear H18.
rewrite <-H25 in *.
contradiction.
intros.
generalize H15.
unfold collinear.
case_eq (eq_dec_u a b).
contradiction.
destruct (a1_exist a b).
simpl.
case_eq (incid_dec x7 x8).
intros.
inversion H18.
intros.
destruct a0.
destruct a2.
assert( HH0 := uniqueness a b x x8 H19 H20 H21 H22).
destruct HH0.
contradiction.
clear H16.
rewrite <-H23 in *.
contradiction.
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
inversion H10.
destruct (a1_exist x0 x1).
simpl.
case_eq (incid_dec x2 x3).
intros.
inversion H11.
intros.
destruct a0.
assert( HH0 := uniqueness x0 x1 x x3 H4 H5 H12 H13).
destruct HH0.
contradiction.
clear H9.
rewrite <-H14 in *.
contradiction.
intros.
exists x1.
simpl.
split.
case_eq (collinear a b x1).
case_eq (eq_dec_u a b).
case_eq (eq_dec_u b x1).
intros.
clear H8 H9 H10.
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
assert( HH0 := uniqueness a b x x3 H H0 H12 H13).
destruct HH0.
contradiction.
clear H9.
rewrite H14 in *.
contradiction.
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
inversion H10.
destruct (a1_exist a b).
simpl.
case_eq (incid_dec x0 x3).
intros.
inversion H11.
intros.
destruct a0.
assert( HH0 := uniqueness a b x x3 H H0 H12 H13).
destruct HH0.
contradiction.
clear H9.
rewrite <-H14 in n0.
contradiction.
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
assert( HH0 := uniqueness a b x x3 H H0 H14 H15).
destruct HH0.
contradiction.
clear H11.
rewrite H16 in *.
contradiction.
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
generalize H11.
unfold collinear.
case_eq (eq_dec_u a b).
intros.
inversion H13.
destruct (a1_exist a b).
simpl.
case_eq( incid_dec x1 x3).
intros.
inversion H14.
intros.
destruct a0.
assert( HH0 := uniqueness a b x x3 H H0 H15 H16).
destruct HH0.
contradiction.
clear H12.
rewrite <-H17 in n2.
contradiction.
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
generalize H10.
unfold collinear.
case_eq (eq_dec_u a b).
intros.
inversion H12.
intro.
destruct (a1_exist a b).
simpl.
case_eq(incid_dec x0 x3).
intros.
inversion H13.
intros.
destruct a0.
assert( HH0 := uniqueness a b x x3 H H0 H14 H15).
destruct HH0.
contradiction.
clear H11.
rewrite <-H16 in n3.
contradiction.
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

Lemma rank_min_3 : exists a b c, rkl(a :: b :: c :: nil) >= 3.
Proof.
intros.
assert( HH0 := a3_2).
destruct HH0.
destruct s.
assert( HH0 := a2_exist x x0). 
destruct HH0.
assert( HH1 := a3_1 x).
destruct HH1.
destruct s.
destruct s.
destruct a0.
assert(H1 := H0).
destruct H1.
destruct H2.
destruct H3.
destruct H4.
assert( HH2 := a3_1 x0).
destruct HH2.
destruct s.
destruct s.
destruct a0.
destruct H7.
destruct H8.
destruct H9.
destruct H10.
case_eq (eq_dec_u x2 x1).
case_eq (eq_dec_u x5 x1).
intros.
exists x3.
exists x6.
exists x1.
simpl.
case_eq (collinear x3 x6 x1).
intro.
generalize H9.
unfold collinear.
case_eq (eq_dec_u x3 x6).
intros.
rewrite <-e1 in *.
destruct a.
assert( HH0 := uniqueness x1 x3 x x0 H17 H4 H18 H10).
destruct HH0.
rewrite <-e0 in H19.
contradiction.
contradiction.
intro.
destruct (a1_exist x3 x6).
simpl.
case_eq (incid_dec x1 x8).
intros.
destruct a.
destruct a0.
assert( HH0 := uniqueness x1 x3 x x8 H18 H4 i H20).
destruct HH0.
clear H13.
rewrite H22 in e0.
contradiction.
assert( HH0 := uniqueness x1 x6 x0 x8 H19 H10 i H21).
destruct HH0.
clear H12.
rewrite H23 in e.
contradiction.
rewrite <-H23 in H22.
contradiction.
intros.
simplgen H14. unfold collinear.
case_eq(eq_dec_u x3 x6).
intros.
contradiction.
destruct (a1_exist x3 x6).
simpl.
case_eq(incid_dec x1 x9).
intros.
destruct a0.
destruct a1.
assert(HH0 := uniqueness x3 x6 x8 x9 H21 H22 H23 H24).
destruct HH0.
contradiction.
clear H15.
rewrite H25 in *.
contradiction.
intros.
inversion H20.
intros.
intuition.
intros.
exists x3.
exists x5.
exists x1.
simpl.
case_eq (collinear x3 x5 x1).
unfold collinear.
case_eq (eq_dec_u x3 x5).
intros.
rewrite e0 in H4.
destruct a.
assert( HH0 := uniqueness x1 x5 x x0 H16 H4 H17 H9).
destruct HH0.
clear H12.
rewrite H18 in n0.
apply False_ind.
apply n0.
reflexivity.
contradiction.
destruct (a1_exist x3 x5).
simpl.
case_eq (incid_dec x1 x8).
intros.
destruct a.
destruct a0.
assert( HH0 := uniqueness x1 x3 x x8 H17 H4 i H19).
destruct HH0.
clear H13.
rewrite H21 in e.
contradiction.
assert( HH0 := uniqueness x1 x5 x0 x8 H18 H9 i H20).
destruct HH0.
clear H12.
rewrite H22 in n0.
apply False_ind.
apply n0.
reflexivity.
rewrite <-H22 in H21.
contradiction.
intros.
inversion H16.
intros.
intuition.
intros.
case_eq (eq_dec_u x5 x1).
intros.
exists x2.
exists x6.
exists x1.
simpl.
case_eq (collinear x2 x6 x1).
unfold collinear.
case_eq (eq_dec_u x2 x6).
intros.
rewrite <-e0 in H10.
destruct a.
assert( HH0 := uniqueness x1 x2 x x0 H16 H3 H17 H10).
destruct HH0.
clear H12.
rewrite H18 in n0.
apply False_ind.
apply n0.
reflexivity.
contradiction.
destruct (a1_exist x2 x6).
simpl.
case_eq (incid_dec x1 x8).
intros.
destruct a.
destruct a0.
assert( HH0 := uniqueness x1 x2 x x8 H17 H3 i H19).
destruct HH0.
clear H12.
rewrite H21 in n0.
apply False_ind.
apply n0.
reflexivity.
assert( HH0 := uniqueness x1 x6 x0 x8 H18 H10 i H20).
destruct HH0.
clear H13.
rewrite H22 in e.
contradiction.
rewrite <-H22 in H21.
contradiction.
intros.
inversion H16.
intros.
intuition.
intros.
exists x2.
exists x5.
exists x1.
simpl.
case_eq (collinear x2 x5 x1).
unfold collinear.
case_eq (eq_dec_u x2 x5).
intros.
rewrite e in H3.
destruct a.
assert( HH0 := uniqueness x1 x5 x x0 H16 H3 H17 H9).
destruct HH0.
clear H13.
rewrite H18 in n1.
apply False_ind.
apply n1.
reflexivity.
contradiction.
destruct (a1_exist x2 x5).
simpl.
case_eq (incid_dec x1 x8).
intros.
destruct a.
destruct a0.
assert( HH0 := uniqueness x1 x2 x x8 H17 H3 i H19).
destruct HH0.
clear H12.
rewrite H21 in n0.
apply False_ind.
apply n0.
reflexivity.
assert( HH0 := uniqueness x1 x5 x0 x8 H18 H9 i H20).
destruct HH0.
clear H13.
rewrite H22 in n1.
apply False_ind.
apply n1.
reflexivity.
rewrite <-H22 in H21.
contradiction.
intros.
inversion H16.
intros.
intuition.
Qed.

End s_ppEquivToRk.
