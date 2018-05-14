Require Export ProjectiveGeometry.Dev.projective_space_axioms.
Require Export ProjectiveGeometry.Dev.p_equiv_c3p.

(*****************************************************************************)
(** Coplanar **)


Section s_psohEquivCop.

Context `{PPS : PreProjectiveSpace}.
Context `{EP : EqDecidability Point}.
Context `{OP : OrderedType Point}.
Context `{EL : EqDecidabilityL Line}.

(*** Definition dist4 ***)
Definition dist4 (a b c d : Point) := 
 ~ a [==] b /\ ~ a [==] c /\ ~ a [==] d /\ 
 ~ b [==] c /\ ~ b [==] d /\ ~ c [==] d.

Context `{ELI : EqDecidabilityP Line Intersect}.

(*** Definition coplanar ***)
Definition coplanar (a b c d : Point) : bool := 
if (eq_dec_u a b) 
   then true 
   else if (eq_dec_u c d) 
        then true
        else let l1 := (proj1_sig (a1_exist a b)) in
             let l2 := (proj1_sig (a1_exist c d)) in
             if (eq_dec_l l1 l2) then true
             else if (eq_dec_p l1 l2) then true 
             else false.

Lemma cop_1 : forall a b c, coplanar a a b c = true.
Proof.
intros.
unfold coplanar.
case_eq (eq_dec_u a a).
intros.
reflexivity.
intros.
apply False_ind.
apply n.
reflexivity.
Qed.

Lemma cop_2 : forall a b c, coplanar a b b c = true.
Proof.
intros.
unfold coplanar.
case_eq (eq_dec_u a b).
intros.
reflexivity.
intros.
case_eq (eq_dec_u b c).
intros.
reflexivity.
intros.
destruct (a1_exist a b).
intros.
simpl.
destruct (a1_exist b c).
simpl.
case_eq (eq_dec_l x x0).
intros.
reflexivity.
intros.
case_eq (eq_dec_p x x0).
intros.
reflexivity.
intros.
destruct a0.
destruct a1.
assert( Intersect x x0).
unfold Intersect.
exists b.
split.
assumption.
assumption.
contradiction.
Qed.

Lemma cop_3 : forall a b c, coplanar a b c c = true.
Proof.
intros.
unfold coplanar.
case_eq (eq_dec_u a b).
intros.
reflexivity.
intros.
case_eq (eq_dec_u c c).
intros.
reflexivity.
intros.
apply False_ind.
apply n0.
reflexivity.
Qed.

Lemma cop_exchange1 : forall a b c d, coplanar a b c d = coplanar b a c d.
Proof.
intros.
unfold coplanar.
case_eq (eq_dec_u a b).
intros.
case_eq (eq_dec_u b a).
intros.
reflexivity.
intros.
assert(HH := eq_reverse a b e).
contradiction.
intros.
case_eq (eq_dec_u c d).
intros.
case_eq (eq_dec_u b a).
intros.
reflexivity.
intros.
reflexivity.
intros.
destruct (a1_exist a b).
simpl.
destruct (a1_exist c d).
simpl.
case_eq (eq_dec_l x x0).
intros.
case_eq (eq_dec_u b a).
intros.
reflexivity.
intros.
destruct (a1_exist b a).
simpl.
case_eq (eq_dec_l x1 x0).
intros.
reflexivity.
intros.
case_eq (eq_dec_p x1 x0).
intros.
reflexivity.
intros.
clear H1 H2 H3 H4.
rewrite <-e in *.
destruct a0.
destruct a2.
assert( HH0 : Intersect x1 x).
unfold Intersect.
exists b.
split.
assumption.
assumption.
contradiction.
intros.
case_eq (eq_dec_p x x0).
intros.
case_eq (eq_dec_u b a).
intros.
reflexivity.
intros.
destruct (a1_exist b a).
simpl.
case_eq (eq_dec_l x1 x0).
intros.
reflexivity.
intros.
case_eq (eq_dec_p x1 x0).
intros.
reflexivity.
intros.
clear H1 H2 H3 H4.
destruct a0.
destruct a2.
assert( HH0 := uniqueness a b x x1 H1 H2 H4 H3).
destruct HH0.
contradiction.
rewrite H6 in i.
contradiction.
intros.
case_eq (eq_dec_u b a).
intros.
assert( HH0 := eq_reverse b a e).
contradiction.
intros.
destruct (a1_exist b a).
simpl.
case_eq (eq_dec_l x1 x0).
intros.
clear H1 H2 H3 H4.
destruct a0.
destruct a2.
assert( HH0 := uniqueness a b x x1 H1 H2 H4 H3).
destruct HH0.
contradiction.
rewrite H5 in n1.
rewrite e in n1.
apply False_ind.
apply n1.
reflexivity.
intros.
case_eq (eq_dec_p x1 x0).
intros.
clear H1 H2 H3 H4.
destruct a0.
destruct a2.
assert( HH0 := uniqueness a b x x1 H1 H2 H4 H3).
destruct HH0.
contradiction.
rewrite H6 in n2.
contradiction.
intros.
reflexivity.
Qed.

Lemma cop_exchange2 : forall a b c d, coplanar a b c d = coplanar a b d c.
Proof.
intros.
unfold coplanar.
case_eq (eq_dec_u a b).
intros.
reflexivity.
intros.
case_eq (eq_dec_u c d).
intros.
case_eq (eq_dec_u d c).
intros.
reflexivity.
intros.
assert( HH0 := eq_reverse c d e).
contradiction.
intros.
destruct (a1_exist c d).
simpl.
destruct (a1_exist a b).
simpl.
case_eq (eq_dec_l x0 x).
intros.
case_eq (eq_dec_u d c).
intros.
reflexivity.
intros.
destruct (a1_exist d c).
simpl.
case_eq (eq_dec_l x0 x1).
intros.
reflexivity.
intros.
case_eq (eq_dec_p x0 x1).
intros.
reflexivity.
intros.
clear H0 H1 H2 H3 H4.
assert( HH0 : Intersect x x1).
unfold Intersect.
exists c.
destruct a0.
destruct a2.
split.
assumption.
assumption.
rewrite e in *.
contradiction.
intros.
case_eq (eq_dec_p x0 x).
intros.
case_eq (eq_dec_u d c).
intros.
reflexivity.
intros.
destruct (a1_exist d c).
simpl.
case_eq (eq_dec_l x0 x1).
intros.
reflexivity.
intros.
case_eq (eq_dec_p x0 x1).
intros.
reflexivity.
intros.
clear H1 H2 H3 H4.
destruct a0.
destruct a2.
assert( HH0 := uniqueness c d x x1 H1 H2 H4 H3).
destruct HH0.
contradiction.
rewrite H6 in *.
contradiction.
intros.
case_eq (eq_dec_u d c).
intros.
assert( HH0 := eq_reverse d c e).
contradiction.
intros.
case_eq (a1_exist d c).
simpl.
intros.
case_eq (eq_dec_l x0 x1).
intros.
clear H1 H2 H3 H4.
destruct a0.
destruct a2.
assert( HH0 := uniqueness c d x x1 H1 H2 H4 H3).
destruct HH0.
contradiction.
rewrite H6 in *.
rewrite e in *.
apply False_ind.
apply n1.
reflexivity.
intros.
case_eq (eq_dec_p x0 x1).
intros.
clear H1 H2 H3 H4.
destruct a0.
destruct a2.
assert( HH0 := uniqueness c d x x1 H1 H2 H4 H3).
destruct HH0.
contradiction.
rewrite H7 in *.
contradiction.
intros.
reflexivity.
Qed.

Lemma cop_exchange3 : forall a b c d, coplanar a b c d = coplanar a c b d.
Proof.
intros.
unfold coplanar.
case_eq (eq_dec_u a b).
intros.
case_eq (eq_dec_u a c).
intros.
reflexivity.
intros.
case_eq (eq_dec_u b d).
intros.
reflexivity.
intros.
destruct (a1_exist a c).
simpl.
destruct (a1_exist b d).
simpl.
case_eq (eq_dec_l x x0).
intros.
reflexivity.
intros.
case_eq (eq_dec_p x x0).
intros.
reflexivity.
intros.
rewrite e in *.
assert( HH0 : Intersect x x0).
unfold Intersect.
exists b.
destruct a0; destruct a1.
split.
assumption. assumption. contradiction.
case_eq (eq_dec_u c d).
intros.
case_eq (eq_dec_u a c).
intros.
reflexivity.
intros.
case_eq (eq_dec_u b d).
intros.
reflexivity.
destruct (a1_exist a c).
intros.
destruct (a1_exist b d).
simpl.
case_eq (eq_dec_l x x0).
intros.
reflexivity.
intros.
case_eq (eq_dec_p x x0).
intros.
reflexivity.
intros.
rewrite e in *.
assert( HH0 : Intersect x x0).
unfold Intersect.
exists d.
destruct a0; destruct a1.
split.
assumption. assumption. contradiction.
intros.
destruct (a1_exist a b).
simpl.
destruct (a1_exist c d).
simpl.
case_eq (eq_dec_l x x0).
intros.
case_eq (eq_dec_u a c).
intros.
reflexivity.
case_eq (eq_dec_u b d).
intros.
reflexivity.
intros.
destruct (a1_exist a c).
simpl.
destruct (a1_exist b d).
simpl.
case_eq (eq_dec_l x1 x2).
intros.
reflexivity.
intros.
destruct (eq_dec_p x1 x2).
reflexivity.
rewrite e in *.
destruct a0; destruct a1; destruct a2; destruct a3.
assert( HH0 := uniqueness a c x0 x1 H5 H7 H9 H10).
destruct HH0.
contradiction.
assert( HH0 := uniqueness b d x0 x2 H6 H8 H11 H12).
destruct HH0.
contradiction.
rewrite H13 in H14.
contradiction.
intros.
case_eq (eq_dec_p x x0).
intros.
case_eq (eq_dec_u a c).
intros.
reflexivity.
intros.
case_eq (eq_dec_u b d).
intros.
reflexivity.
intros.
destruct (a1_exist a c).
simpl.
destruct (a1_exist b d).
simpl.
destruct (eq_dec_l x1 x2).
reflexivity.
case_eq (eq_dec_p x1 x2).
intros.
reflexivity.
intros.
destruct a0; destruct a1 ; destruct a2; destruct a3.
case_eq (eq_dec_u b c).
intros.
rewrite e in *.
assert( HH0 : Intersect x1 x2); unfold Intersect.
exists c.
split.
assumption. assumption. contradiction.
case_eq (eq_dec_u a d).
intros.
rewrite e in *.
assert( HH0 : Intersect x1 x2); unfold Intersect.
exists d.
split.
assumption. assumption. contradiction.
intros.
assert( HH0 : dist4 a b c d).
unfold dist4.
split. assumption. split. assumption. split. assumption. split. assumption. split. assumption. assumption. 
assert( HH1 : Incid a x /\ Incid b x).
split. assumption. assumption.
assert( HH2 : Incid c x0 /\ Incid d x0).
split. assumption. assumption.
assert( HH3 : Incid a x1 /\ Incid c x1).
split. assumption. assumption.
assert( HH4 : Incid b x2 /\ Incid d x2).
split. assumption. assumption.
unfold Intersect in i.
destruct i.
assert( HH5 : exists I : Point, Incid I x /\ Incid I x0).
exists x3.
destruct a0.
split. assumption. assumption.
assert( HH6 := a2 a b c d x x0 x1 x2 HH0 HH1 HH2 HH3 HH4 HH5).
destruct HH6.
destruct H16.
assert( HH6 : Intersect x1 x2); unfold Intersect.
exists x4.
split. assumption. assumption.
contradiction.
case_eq (eq_dec_u a c).
intros.
rewrite e in *.
assert( HH0 : Intersect x x0); unfold Intersect.
destruct a0; destruct a1.
exists c.
split. assumption. assumption.
contradiction.
intros.
case_eq (eq_dec_u b d).
intros.
rewrite e in *.
assert( HH0 : Intersect x x0); unfold Intersect.
destruct a0; destruct a1.
exists d.
split. assumption. assumption.
contradiction.
intros.
destruct (a1_exist a c).
simpl.
destruct (a1_exist b d).
simpl.
case_eq (eq_dec_l x1 x2).
intros.
rewrite e in *.
destruct a0; destruct a1; destruct a2; destruct a3.
assert( HH0 := uniqueness a b x x2 H6 H7 H10 H12).
destruct HH0.
contradiction.
assert( HH0 := uniqueness c d x0 x2 H8 H9 H11 H13).
destruct HH0.
contradiction.
rewrite <-H15 in H14.
contradiction.
intros.
case_eq (eq_dec_p x1 x2).
intros.
case_eq (eq_dec_u b c).
intros.
rewrite e in *.
assert( HH0 : Intersect x x0); unfold Intersect.
exists c.
destruct a0; destruct a1; split.
assumption. assumption. contradiction.
intros.
case_eq (eq_dec_u a d).
intros.
rewrite e in *.
assert( HH0 : Intersect x x0); unfold Intersect.
exists d.
destruct a0; destruct a1; split.
assumption. assumption. contradiction.
intros.
assert( HH0 : dist4 a c b d).
unfold dist4.
split. assumption. split. assumption. split. assumption. split. 
intro; clear H7; rewrite H9 in *. apply n6; reflexivity.
split. assumption. assumption.
destruct a0; destruct a1; destruct a2; destruct a3.
assert( HH1 : Incid a x1 /\ Incid c x1).
split. assumption. assumption.
assert( HH2 : Incid b x2 /\ Incid d x2).
split. assumption. assumption.
assert( HH3 : Incid a x /\ Incid b x).
split. assumption. assumption.
assert( HH4 : Incid c x0 /\ Incid d x0).
split. assumption. assumption.
assert( HH5 : exists I : Point, Incid I x1 /\ Incid I x2).
unfold Intersect in i.
destruct i.
exists x3.
destruct a0.
split.
assumption. assumption.
assert( HH6 := a2 a c b d x1 x2 x x0 HH0 HH1 HH2 HH3 HH4 HH5).
destruct HH6.
destruct H17.
assert( HH6 : Intersect x x0); unfold Intersect.
exists x3.
split. assumption. assumption.
contradiction.
intros.
reflexivity.
Qed.

Lemma cop_shift_aux : forall x x0, Intersect x x0 -> Intersect x0 x.
Proof.
intros.
unfold Intersect in *.
destruct H.
exists x1.
destruct H.
simpl.
split.
assumption.
assumption.
Qed.

Lemma cop_shift : forall a b c d, coplanar a b c d = coplanar c d a b.
Proof.
intros.
unfold coplanar.
case_eq (eq_dec_u a b).
intros.
case_eq (eq_dec_u c d).
intros.
reflexivity.
intros.
reflexivity.
intros.
case_eq (eq_dec_u c d).
intros.
reflexivity.
intros.
destruct (a1_exist c d).
simpl.
destruct (a1_exist a b).
simpl.
case_eq (eq_dec_l x0 x).
intros.
case_eq (eq_dec_l x x0).
intros.
reflexivity.
intros.
clear H2.
rewrite e in n1.
apply False_ind.
apply n1.
reflexivity.
intros.
case_eq (eq_dec_p x0 x).
intros.
case_eq (eq_dec_l x x0).
intros.
reflexivity.
intros.
case_eq (eq_dec_p x x0).
intros.
reflexivity.
intros.
assert( HH0 := cop_shift_aux x0 x i).
contradiction.
intros.
case_eq (eq_dec_l x x0).
intros.
clear H1.
rewrite e in n1.
apply False_ind.
apply n1.
reflexivity.
intros.
case_eq (eq_dec_p x x0).
intros.
assert( HH0 := cop_shift_aux x x0 i).
contradiction.
intros.
reflexivity.
Qed.

Lemma cop_trans : forall a b c d e, collinear a b c = false -> coplanar a b c d = true -> coplanar a b c e = true -> coplanar a b d e = true.
Proof. 
unfold coplanar.
intros a b c d e H.
case_eq (eq_dec_u a b).
intros.
reflexivity.
case_eq (eq_dec_u c d).
case_eq (eq_dec_u c e).
case_eq (eq_dec_u d e).
intros.
reflexivity.
destruct (a1_exist a b).
simpl.
destruct (a1_exist d e).
simpl.
case_eq (eq_dec_l x x0).
intros.
reflexivity.
intros.
case_eq (eq_dec_p x x0).
intros.
reflexivity.
intros.
clear H0 H1 H2 H3 H4 H5 H6 H7.
rewrite e0 in *.
rewrite e1 in *.
apply False_ind.
apply n0.
reflexivity.
destruct (a1_exist a b).
simpl.
destruct (a1_exist c e).
simpl.
case_eq (eq_dec_l x x0).
case_eq (eq_dec_u d e).
intros.
reflexivity.
destruct (a1_exist d e).
simpl.
case_eq (eq_dec_l x x1).
intros.
reflexivity.
case_eq (eq_dec_p x x1).
intros.
reflexivity.
intros.
clear H0 H1 H2 H3 H4 H5 H6 H7 H8.
rewrite e0 in *.
rewrite e1 in *.
destruct a1.
destruct a2.
assert( HH0 := uniqueness d e x0 x1 H0 H1 H2 H3).
destruct HH0.
contradiction.
rewrite H4 in *.
apply False_ind.
apply n0.
reflexivity.
case_eq (eq_dec_p x x0).
case_eq (eq_dec_u d e).
intros.
reflexivity.
destruct (a1_exist d e).
simpl.
case_eq (eq_dec_l x x1).
intros.
reflexivity.
case_eq (eq_dec_p x x1).
intros.
reflexivity.
intros.
clear H0 H1 H2 H3 H4 H5 H6 H7 H8 H9.
rewrite e0 in *.
destruct a1.
destruct a2.
assert( HH0 := uniqueness d e x0 x1 H0 H1 H2 H3).
destruct HH0.
contradiction.
rewrite H4 in *.
contradiction.
intros.
inversion H6.
destruct (a1_exist a b).
simpl.
destruct (a1_exist c d).
simpl.
case_eq (eq_dec_l x x0).
case_eq (eq_dec_u c e).
case_eq (eq_dec_u d e).
intros.
reflexivity.
destruct (a1_exist d e).
simpl.
case_eq (eq_dec_l x x1).
intros.
reflexivity.
case_eq (eq_dec_p x x1).
intros.
reflexivity.
intros.
clear H0 H1 H2 H3 H4 H5 H6 H7 H8.
rewrite e0 in *.
rewrite e1 in *.
destruct a1.
destruct a2.
assert( HH0 := uniqueness d e x0 x1 H1 H0 H2 H3).
destruct HH0.
contradiction.
rewrite H4 in *.
apply False_ind.
apply n0.
reflexivity.
destruct (a1_exist c e).
simpl.
case_eq (eq_dec_l x x1).
case_eq (eq_dec_u d e).
intros.
reflexivity.
destruct (a1_exist d e).
simpl.
case_eq (eq_dec_l x x2).
intros.
reflexivity.
case_eq (eq_dec_p x x2).
intros.
reflexivity.
intros.
clear H0 H1 H2 H3 H4 H5 H6 H7 H8 H9.
rewrite e0 in *.
rewrite e1 in *.
destruct a1.
destruct a2.
destruct a3.
assert( HH0 := uniqueness d e x0 x2 H1 H3 H4 H5).
destruct HH0.
contradiction.
rewrite H6 in *.
apply False_ind.
apply n0.
reflexivity.
case_eq (eq_dec_p x x1).
case_eq (eq_dec_u d e).
intros.
reflexivity.
destruct (a1_exist d e).
simpl.
case_eq (eq_dec_l x x2).
intros.
reflexivity.
case_eq (eq_dec_p x x2).
intros.
reflexivity.
intros.
clear H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
rewrite e0 in *.
assert( HH0 : Intersect x0 x2).
unfold Intersect.
exists d.
destruct a1.
destruct a3.
split.
assumption.
assumption.
contradiction.
case_eq (eq_dec_u d e).
intros.
reflexivity.
destruct (a1_exist d e).
simpl.
case_eq (eq_dec_l x x2).
intros.
reflexivity.
case_eq (eq_dec_p x x2).
intros.
reflexivity.
intros.
inversion H10.
case_eq (eq_dec_p x x0).
case_eq (eq_dec_u c e).
case_eq (eq_dec_u d e).
intros.
reflexivity.
destruct (a1_exist d e).
simpl.
case_eq (eq_dec_l x x1).
intros.
reflexivity.
case_eq (eq_dec_p x x1).
intros.
reflexivity.
intros.
clear H0 H1 H2 H3 H4 H5 H6 H7 H8 H9.
rewrite e0 in *.
destruct a1.
destruct a2.
assert( HH0 := uniqueness d e x0 x1 H1 H0 H2 H3).
destruct HH0.
contradiction.
rewrite H4 in *.
contradiction.
destruct (a1_exist c e).
simpl.
case_eq(eq_dec_l x x1).
case_eq( eq_dec_u d e).
intros.
reflexivity.
destruct (a1_exist d e).
simpl.
case_eq (eq_dec_l x x2).
intros.
reflexivity.
case_eq (eq_dec_p x x2).
reflexivity.
intros.
clear H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
rewrite e0 in *.
assert( HH0 : Intersect x1 x2).
unfold Intersect.
exists e.
destruct a2.
destruct a3.
split.
assumption.
assumption.
contradiction.
case_eq (eq_dec_p x x1).
case_eq (eq_dec_u d e).
intros.
reflexivity.
destruct( a1_exist d e).
simpl.
case_eq( eq_dec_l x x2).
intros.
reflexivity.
case_eq( eq_dec_p x x2).
intros.
reflexivity.
intros.
clear H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.

unfold Intersect in i.
destruct i.
unfold Intersect in i0.
destruct i0.
case_eq (eq_dec_u x4 x3).
intros.
rewrite e0 in *.
destruct a1.
destruct a2.
destruct H0.
destruct H1.
assert( HH0 := uniqueness x3 c x0 x1 H8 H3 H7 H5).
destruct HH0.
rewrite H9 in *.
assert( HH0 : collinear a b c = true).
unfold collinear.
case_eq (eq_dec_u a b).
intros.
reflexivity.
intros.
destruct (a1_exist a b).
simpl.
case_eq (incid_dec c x5).
intros.
reflexivity.
intros.
destruct a0.
destruct a1.
assert( HH0 := uniqueness a b x x5 H12 H13 H14 H15).
destruct HH0.
contradiction.
rewrite H16 in *.
contradiction.
rewrite HH0 in H.
inversion H.
rewrite H9 in *.
destruct a3.
assert( HH0 := uniqueness d e x1 x2 H4 H6 H10 H11).
destruct HH0.
contradiction.
rewrite H12 in *.
assert( HH0 : Intersect x x2).
unfold Intersect.
exists x3.
split.
assumption.
assumption.
contradiction.
intros.
case_eq(eq_dec_u x3 d).
intros.
rewrite e0 in *.
assert( HH0 : Intersect x x2).
unfold Intersect.
exists d.
destruct a3.
destruct H0.
split.
assumption.
assumption.
contradiction.
intros.
case_eq(eq_dec_u x3 e).
intros.
rewrite e0 in *.
assert( HH0 : Intersect x x2).
unfold Intersect.
exists e.
destruct a3.
destruct H0.
split.
assumption.
assumption.
contradiction.
intros.
case_eq(eq_dec_u x4 d).
intros.
rewrite e0 in *.
assert( HH0 : Intersect x x2).
unfold Intersect.
exists d.
destruct a3.
destruct H1.
split.
assumption.
assumption.
contradiction.
intros.
case_eq(eq_dec_u x4 e).
intros.
rewrite e0 in *.
assert( HH0 : Intersect x x2).
unfold Intersect.
exists e.
destruct a3.
destruct H1.
split.
assumption.
assumption.
contradiction.
intros.
assert( HH0 : dist4 x4 d x3 e).
unfold dist4.
split.
assumption.
split.
assumption.
split.
assumption.
split.
intro.
clear H3.
rewrite H7 in *.
apply n8.
reflexivity.
split.
assumption.
assumption.
destruct a0.
destruct a1.
destruct a2.
destruct a3.
destruct H0.
destruct H1.
assert( HH1 : Incid x4 x0 /\ Incid d x0).
split.
assumption.
assumption.
assert( HH2 : Incid x3 x1 /\ Incid e x1).
split.
assumption.
assumption.
assert( HH3 : Incid x4 x /\ Incid x3 x).
split.
assumption.
assumption.
assert( HH4 : Incid d x2 /\ Incid e x2).
split.
assumption.
assumption.
assert( HH5 : exists I : Point, Incid I x0 /\ Incid I x1).
exists c.
split.
assumption.
assumption.
assert( HH6 := a2 x4 d x3 e x0 x1 x x2 HH0 HH1 HH2 HH3 HH4 HH5).
destruct HH6.
assert( Intersect x x2).
unfold Intersect.
exists x5.
destruct H17.
split.
assumption.
assumption.
contradiction.
case_eq (eq_dec_u d e).
intros.
reflexivity.
intros.
inversion H9.
intros.
inversion H4.
Qed.

Lemma cop_trans_bis : forall a b c d e, collinear a b c = false -> coplanar a b c d = true -> coplanar a b c e = true -> coplanar a c d e = true.
Proof.
unfold coplanar.
intros a b c d e H.
case_eq (eq_dec_u a b).
case_eq (eq_dec_u a c).
intros.
reflexivity.
case_eq (eq_dec_u d e).
intros.
reflexivity.
destruct (a1_exist d e).
simpl.
destruct (a1_exist a c).
simpl.
case_eq (eq_dec_l x0 x).
intros.
reflexivity.
case_eq (eq_dec_p x0 x).
intros.
reflexivity.
intros.
clear H1 H2 H3 H4 H5 H6.
rewrite e0 in *.
assert( HH0 := col_1 b c).
rewrite HH0 in H.
inversion H.
case_eq (eq_dec_u c d).
case_eq (eq_dec_u c e).
case_eq (eq_dec_u a c).
intros.
reflexivity.
case_eq (eq_dec_u d e).
intros.
reflexivity.
destruct (a1_exist d e).
simpl.
destruct (a1_exist a c).
simpl.
case_eq (eq_dec_l x0 x).
intros.
reflexivity.
case_eq (eq_dec_p x0 x).
intros.
reflexivity.
intros.
clear H1 H2 H3 H4 H5 H6 H7 H8.
rewrite e0 in *.
rewrite e1 in *.
apply False_ind.
apply n1.
reflexivity.
destruct (a1_exist c e).
simpl.
destruct (a1_exist a b).
simpl.
case_eq (eq_dec_l x0 x).
case_eq (eq_dec_u a c).
intros.
reflexivity.
case_eq (eq_dec_u d e).
intros.
reflexivity.
destruct (a1_exist a c).
simpl.
destruct (a1_exist d e).
simpl.
case_eq (eq_dec_l x1 x2).
intros.
reflexivity.
case_eq (eq_dec_p x1 x2).
intros.
reflexivity.
intros.
clear H1 H2 H3 H4 H5 H6 H7 H8 H9.
rewrite e0 in *.
rewrite e1 in *.
destruct a0.
destruct a3.
assert( HH0 := uniqueness d e x x2 H1 H2 H3 H4).
destruct HH0.
contradiction.
rewrite H5 in *.
assert( HH0 : Intersect x1 x2).
unfold Intersect.
exists d.
destruct a2.
split.
assumption.
assumption.
contradiction.
case_eq (eq_dec_p x0 x).
case_eq (eq_dec_u a c).
intros.
reflexivity.
case_eq (eq_dec_u d e).
intros.
reflexivity.
destruct (a1_exist a c).
simpl.
destruct (a1_exist d e).
simpl.
case_eq (eq_dec_l x1 x2).
intros.
reflexivity.
case_eq (eq_dec_p x1 x2).
intros.
reflexivity.
intros.
clear H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
rewrite e0 in *.
destruct a0.
destruct a3.
assert( HH0 := uniqueness d e x x2 H1 H2 H3 H4).
destruct HH0.
contradiction.
rewrite H5 in *.
assert( HH0 : Intersect x1 x2).
unfold Intersect.
exists d.
destruct a2.
split.
assumption.
assumption.
contradiction.
intros.
inversion H6.
destruct (a1_exist a b).
simpl.
destruct (a1_exist c d).
simpl.
case_eq (eq_dec_l x x0).
case_eq (eq_dec_u c e).
case_eq (eq_dec_u a c).
intros.
reflexivity.
case_eq (eq_dec_u d e).
intros.
reflexivity.
destruct (a1_exist a c).
simpl.
destruct (a1_exist d e).
simpl.
case_eq (eq_dec_l x1 x2).
intros.
reflexivity.
case_eq (eq_dec_p x1 x2).
intros.
reflexivity.
intros.
clear H1 H2 H3 H4 H5 H6 H7 H8 H9.
rewrite e0 in *.
rewrite e1 in *.
destruct a1.
destruct a3.
assert( HH0 := uniqueness d e x0 x2 H2 H1 H3 H4).
destruct HH0.
contradiction.
rewrite H5 in *.
assert( HH0 : Intersect x1 x2).
unfold Intersect.
exists e.
destruct a2.
split.
assumption.
assumption.
contradiction.
destruct (a1_exist c e).
simpl.
case_eq (eq_dec_l x x1).
case_eq (eq_dec_u a c).
intros.
reflexivity.
case_eq (eq_dec_u d e).
intros.
reflexivity.
destruct (a1_exist a c).
simpl.
destruct (a1_exist d e).
simpl.
case_eq (eq_dec_l x2 x3).
intros.
reflexivity.
case_eq (eq_dec_p x2 x3).
intros.
reflexivity.
intros.
clear H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
rewrite e0 in *.
rewrite e1 in *.
destruct a1.
destruct a2.
destruct a4.
assert( HH0 := uniqueness d e x0 x3 H2 H4 H5 H6).
destruct HH0.
contradiction.
rewrite H7 in *.
destruct a0.
destruct a3.
assert( HH0 := uniqueness a c x2 x3 H10 H11 H8 H1).
destruct HH0.
contradiction.
rewrite H12 in *.
apply False_ind.
apply n0.
reflexivity.
case_eq (eq_dec_p x x1).
case_eq (eq_dec_u a c).
intros.
reflexivity.
case_eq (eq_dec_u d e).
intros.
reflexivity.
destruct (a1_exist a c).
simpl.
destruct (a1_exist d e).
simpl.
case_eq (eq_dec_l x2 x3).
intros.
reflexivity.
case_eq (eq_dec_p x2 x3).
intros.
reflexivity.
intros.
clear H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.
rewrite e0 in *.
destruct a0.
destruct a1.
destruct a3.
assert( HH0 := uniqueness a c x0 x2 H1 H3 H5 H6).
destruct HH0.
contradiction.
rewrite H7 in *.
assert( HH0 : Intersect x2 x3).
unfold Intersect.
exists d.
destruct a4.
split.
assumption.
assumption.
contradiction.
intros.
inversion H7.
case_eq (eq_dec_p x x0).
case_eq (eq_dec_u c e).
case_eq (eq_dec_u a c).
intros.
reflexivity.
case_eq (eq_dec_u d e).
intros.
reflexivity.
destruct (a1_exist a c).
simpl.
destruct (a1_exist d e).
simpl.
case_eq (eq_dec_l x1 x2).
intros.
reflexivity.
case_eq (eq_dec_p x1 x2).
intros.
reflexivity.
intros.
clear H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
rewrite e0 in *.
destruct a1.
destruct a3.
assert( HH0 := uniqueness d e x0 x2 H2 H1 H3 H4).
destruct HH0.
contradiction.
rewrite H5 in *.
assert( HH0 : Intersect x1 x2).
unfold Intersect.
exists e.
destruct a2.
split.
assumption.
assumption.
contradiction.
destruct (a1_exist c e).
simpl.
case_eq (eq_dec_l x x1).
case_eq (eq_dec_u a c).
intros.
reflexivity.
case_eq (eq_dec_u d e).
reflexivity.
destruct (a1_exist a c).
simpl.
destruct (a1_exist d e).
simpl.
case_eq (eq_dec_l x2 x3).
intros.
reflexivity.
case_eq (eq_dec_p x2 x3).
intros.
reflexivity.
intros.
clear H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.
rewrite e0 in *.
destruct a0.
destruct a2.
destruct a3.
assert( HH0 := uniqueness a c x1 x2 H1 H3 H5 H6).
destruct HH0.
contradiction.
rewrite H7 in *.
assert( HH0 : Intersect x2 x3).
unfold Intersect.
exists e.
destruct a4.
split.
assumption.
assumption.
contradiction.
case_eq (eq_dec_p x x1).
case_eq (eq_dec_u d e).
case_eq (eq_dec_u a c).
intros.
reflexivity.
intros.
reflexivity.
case_eq (eq_dec_u a c).
intros.
reflexivity.
destruct (a1_exist a c).
simpl.
destruct (a1_exist d e).
simpl.
case_eq (eq_dec_l x2 x3).
intros.
reflexivity.
case_eq (eq_dec_p x2 x3).
intros.
reflexivity.
intros.
clear H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.
(* Triple Pasch *)
(* Pasch 1 *)
unfold Intersect in i.
unfold Intersect in i0.
destruct i.
destruct i0.
case_eq (eq_dec_u x4 x5).
intros.
rewrite e0 in *.
destruct a1.
destruct a2.
destruct H1.
destruct H2.
assert( HH0 := uniqueness c x5 x0 x1 H4 H9 H6 H8).
destruct HH0.
rewrite <-H10 in *.
destruct a0.
destruct a3.
assert( HH0 := uniqueness a c x x2 H11 H1 H13 H14).
destruct HH0.
contradiction.
rewrite H15 in *.
assert( HH0 : collinear a b c = true).
unfold collinear.
case_eq (eq_dec_u a b).
intros.
reflexivity.
intros.
destruct (a1_exist a b).
simpl.
case_eq (incid_dec c x6).
intros.
reflexivity.
intros.
destruct a0.
assert( HH0 := uniqueness a b x2 x6 H11 H12 H18 H19).
destruct HH0.
contradiction.
rewrite H20 in *.
contradiction.
rewrite HH0 in H.
inversion H.
rewrite H10 in *.
destruct a4.
assert( HH0 := uniqueness d e x1 x3  H5 H7 H11 H12).
destruct HH0.
contradiction.
rewrite H13 in *.
assert( HH0 : Intersect x2 x3).
unfold Intersect.
exists c.
destruct a3.
split.
assumption.
assumption.
contradiction.
intros.
case_eq (eq_dec_u x4 d).
intros.
rewrite e0 in *.
destruct a1.
destruct a2.
destruct H1.
assert( HH0 := uniqueness c d x0 x1 H5 H6 H7 H9).
destruct HH0.
contradiction.
rewrite H10 in *.
destruct a4.
assert( HH0 := uniqueness d e x1 x3 H6 H8 H11 H12).
destruct HH0.
contradiction.
rewrite H13 in *.
assert( HH0 : Intersect x2 x3).
unfold Intersect.
exists c.
destruct a3.
split.
assumption.
assumption.
contradiction.
intros.
case_eq (eq_dec_u x5 e).
intros.
rewrite e0 in *.
destruct a1.
destruct a2.
destruct H2.
assert( HH0 := uniqueness c e x0 x1 H6 H10 H8 H9).
destruct HH0.
contradiction.
rewrite H11 in *.
destruct a4.
assert( HH0 := uniqueness d e x1 x3 H7 H9 H12 H13).
destruct HH0.
contradiction.
rewrite H14 in *.
assert( HH0 : Intersect x2 x3).
unfold Intersect.
exists c.
destruct a3.
split.
assumption.
assumption.
contradiction.
intros.
(* Cas dégénéré x4 = e *)
case_eq (eq_dec_u x4 e).
intros.
case_eq (eq_dec_u a d).
intros.
rewrite e1 in *.
assert( HH0 : Intersect x2 x3).
unfold Intersect.
exists d.
destruct a3.
destruct a4.
split.
assumption.
assumption.
contradiction.
case_eq (eq_dec_u a e).
intros.
rewrite e1 in *.
assert( HH0 : Intersect x2 x3).
unfold Intersect.
exists e.
destruct a3.
destruct a4.
split.
assumption.
assumption.
contradiction.
intros.
assert( HH0 : dist4 a e c d).
unfold dist4.
split.
assumption.
split.
assumption.
split.
assumption.
split.
intro.
rewrite H9 in *.
apply n4.
reflexivity.
split.
intro.
rewrite H9 in *.
apply n2.
reflexivity.
assumption.
destruct a0.
destruct a1.
destruct a2.
destruct a3.
destruct a4.
destruct H1.
destruct H2.
rewrite e0 in *.
assert( HH1 : Incid a x /\ Incid e x).
split.
assumption.
assumption.
assert( HH2 : Incid c x0 /\ Incid d x0).
split.
assumption.
assumption.
assert( HH3 : Incid a x2 /\ Incid c x2).
split.
assumption.
assumption.
assert( HH4 : Incid e x3 /\ Incid d x3).
split.
assumption.
assumption.
assert( HH5 : exists I : Point, (Incid I x /\ Incid I x0)).
exists x5.
split.
assumption.
assumption.
assert( HH6 := a2 a e c d x x0 x2 x3 HH0 HH1 HH2 HH3 HH4 HH5).
destruct HH6.
assert( HH7 : Intersect x2 x3).
unfold Intersect.
exists x6.
destruct H21.
split.
assumption.
assumption.
contradiction.
intros.
(* Cas degenere x5 = d *)
case_eq (eq_dec_u x5 d).
intros.
rewrite e0 in *.
case_eq (eq_dec_u a d).
intros.
rewrite e1 in *.
assert( HH0 : Intersect x2 x3).
unfold Intersect.
exists d.
destruct a3.
destruct a4.
split.
assumption.
assumption.
contradiction.
intros.
case_eq (eq_dec_u a e).
intros.
rewrite e1 in *.
assert( HH0 : Intersect x2 x3).
unfold Intersect.
exists e.
destruct a3.
destruct a4.
split.
assumption.
assumption.
contradiction.
intros.
assert( HH0 : dist4 a d c e).
unfold dist4.
split.
assumption.
split.
assumption.
split.
assumption.
split.
intro.
rewrite H10 in *.
apply n6.
reflexivity.
split.
assumption.
assumption.
destruct a0.
destruct a1.
destruct a2.
destruct a3.
destruct a4.
destruct H1.
destruct H2.
assert( HH1 : Incid a x /\ Incid d x).
split.
assumption.
assumption.
assert( HH2 : Incid c x1 /\ Incid e x1).
split.
assumption.
assumption.
assert( HH3 : Incid a x2 /\ Incid c x2).
split.
assumption.
assumption.
assert( HH4 : Incid d x3 /\ Incid e x3).
split.
assumption.
assumption.
assert( HH5 : exists I : Point, (Incid I x /\ Incid I x1)).
exists x4.
split.
assumption.
assumption.
assert( HH6 := a2 a d c e x x1 x2 x3 HH0 HH1 HH2 HH3 HH4 HH5).
destruct HH6.
destruct H22.
assert( HH7 : Intersect x2 x3).
unfold Intersect.
exists x6.
split.
assumption.
assumption.
contradiction.
intros.
(* Cas non degenere *)
assert( HH0 : dist4 x5 d x4 e).
unfold dist4.
split.
assumption.
split.
intro.
clear H3.
rewrite H8 in *.
apply n8.
reflexivity.
split.
assumption.
split.
intro.
clear H4.
rewrite H8 in *.
apply n9.
reflexivity.
split.
assumption.
assumption.
destruct a0.
destruct a1.
destruct a2.
destruct a3.
destruct a4.
destruct H1.
destruct H2.
assert( HH1 : Incid x5 x0 /\ Incid d x0).
split.
assumption.
assumption.
assert( HH2 : Incid x4 x1 /\ Incid e x1).
split.
assumption.
assumption.
assert( HH3 : Incid x5 x /\ Incid x4 x).
split.
assumption.
assumption.
assert( HH4 : Incid d x3 /\ Incid e x3).
split.
assumption.
assumption.
assert( HH5 : exists I : Point, (Incid I x0 /\ Incid I x1)).
exists c.
split.
assumption.
assumption.
assert( HH6 := a2 x5 d x4 e x0 x1 x x3 HH0 HH1 HH2 HH3 HH4 HH5).
destruct HH6.
(* Pasch 2 *)
assert( HH6 := a1_exist a d).
destruct HH6.
case_eq (eq_dec_u a d).
intros.
rewrite e0 in *.
assert( HH7 : Intersect x2 x3).
unfold Intersect.
exists d.
split.
assumption.
assumption.
contradiction.
intros.
case_eq (eq_dec_u a e).
intros.
rewrite e0 in *.
assert( HH7 : Intersect x2 x3).
unfold Intersect.
exists e.
split.
assumption.
assumption.
contradiction.
intros.
case_eq (eq_dec_u a x4).
intros.
rewrite <-e0 in *.
assert( HH7 := uniqueness a c x1 x2 H18 H12 H14 H15).
destruct HH7.
contradiction.
rewrite H24 in *.
assert( HH7 : Intersect x2 x3).
unfold Intersect.
exists e.
split.
assumption.
assumption.
contradiction.
intros.
assert( HH7 : dist4 a x4 d e).
unfold dist4.
split.
assumption.
split.
assumption.
split.
assumption.
split.
assumption.
split.
assumption.
assumption.
destruct a0.
assert( HH8 : Incid a x7 /\ Incid d x7).
split.
assumption.
assumption.
assert( HH9 : Incid x4 x1 /\ Incid e x1).
split.
assumption.
assumption.
assert( HH10 : Incid a x /\ Incid x4 x).
split.
assumption.
assumption.
assert( HH11 : Incid d x3 /\ Incid e x3).
split.
assumption.
assumption.
assert( HH12 : exists I : Point, (Incid I x /\ Incid I x3)).
exists x6.
destruct H20.
split.
assumption.
assumption.
assert( HH13 := a2 a x4 d e x x3 x7 x1 HH7 HH10 HH11 HH8 HH9 HH12). 
destruct HH13.
(* Pasch 3 *)
assert( HH14 : dist4 a d c e).
unfold dist4.
split.
assumption.
split.
assumption.
split.
assumption.
split.
intro.
rewrite H27 in *.
apply n6.
reflexivity.
split.
assumption.
assumption.
assert( HH15 : Incid a x7 /\ Incid d x7).
split.
assumption.
assumption.
assert( HH16 : Incid c x1 /\ Incid e x1).
split.
assumption.
assumption.
assert( HH17 : Incid a x2 /\ Incid c x2).
split.
assumption.
assumption.
assert( HH18 : Incid d x3 /\ Incid e x3).
split.
assumption.
assumption.
assert( HH19 : exists I : Point, (Incid I x7 /\ Incid I x1)).
exists x8.
destruct H26.
split.
assumption.
assumption.
assert( HH20 := a2 a d c e x7 x1 x2 x3 HH14 HH15 HH16 HH17 HH18 HH19).
destruct HH20.
destruct H27.
assert( HH21 : Intersect x2 x3).
unfold Intersect.
exists x9.
split.
assumption.
assumption.
contradiction.
intros.
inversion H8.
intros.
inversion H4.
Qed.

Lemma cop_trans_bis_bis : forall a b c d e, collinear a b c = false -> coplanar a b c d = true -> coplanar a b c e = true -> coplanar b c d e = true.
Proof.
unfold coplanar.
intros a b c d e H.
case_eq (eq_dec_u a b).
case_eq (eq_dec_u b c).
intros.
reflexivity.
case_eq (eq_dec_u d e).
intros.
reflexivity.
destruct (a1_exist b c).
simpl.
destruct (a1_exist d e).
simpl.
case_eq (eq_dec_l x x0).
intros.
reflexivity.
case_eq (eq_dec_p x x0).
intros.
reflexivity.
intros.
clear H0 H1 H2 H3 H4 H5 H6.
rewrite e0 in *.
assert( HH0 := col_1 b c).
rewrite HH0 in H.
inversion H.
case_eq (eq_dec_u c d).
case_eq (eq_dec_u c e).
case_eq (eq_dec_u b c).
intros.
reflexivity.
case_eq (eq_dec_u d e).
intros.
reflexivity.
destruct (a1_exist b c).
simpl.
destruct (a1_exist d e).
simpl.
case_eq (eq_dec_l x x0).
intros.
reflexivity.
case_eq (eq_dec_p x x0).
intros.
reflexivity.
intros.
clear H0 H1 H2 H3 H4 H5 H6 H7 H8.
rewrite e0 in *.
rewrite e1 in *.
assert( HH0 : Intersect x x0).
unfold Intersect.
exists d.
destruct a0.
destruct a1.
split.
assumption.
assumption.
contradiction.
destruct (a1_exist a b).
simpl.
destruct (a1_exist c e).
simpl.
case_eq (eq_dec_l x x0).
case_eq (eq_dec_u b c).
intros.
reflexivity.
case_eq (eq_dec_u d e).
intros.
reflexivity.
destruct (a1_exist b c).
simpl.
destruct (a1_exist d e).
simpl.
case_eq (eq_dec_l x1 x2).
intros.
reflexivity.
intros.
case_eq (eq_dec_p x1 x2).
intros.
reflexivity.
intros.
clear H0 H1 H2 H3 H4 H5 H6 H7 H8 H9.
rewrite e1 in *.
assert( HH0 : Intersect x1 x2).
unfold Intersect.
exists d.
destruct a2.
destruct a3.
split.
assumption.
assumption.
contradiction.
case_eq (eq_dec_p x x0).
case_eq (eq_dec_u b c).
intros.
reflexivity.
case_eq (eq_dec_u d e).
intros.
reflexivity.
destruct (a1_exist b c).
simpl.
destruct (a1_exist d e).
simpl.
destruct (eq_dec_l x1 x2).
intros.
reflexivity.
case_eq (eq_dec_p x1 x2).
intros.
reflexivity.
intros.
clear H0 H1 H2 H3 H4 H5 H6 H7 H8 H9.
rewrite e0 in *.
assert( HH0 : Intersect x1 x2).
unfold Intersect.
exists d.
destruct a2.
destruct a3.
split.
assumption.
assumption.
contradiction.
intros.
inversion H6.
destruct (a1_exist a b).
simpl.
destruct (a1_exist c d).
simpl.
case_eq (eq_dec_l x x0).
simpl.
case_eq (eq_dec_u c e).
case_eq (eq_dec_u d e).
case_eq (eq_dec_u b c).
intros.
reflexivity.
intros.
reflexivity.
case_eq (eq_dec_u b c).
intros.
reflexivity.
destruct (a1_exist b c).
simpl.
destruct (a1_exist d e).
simpl.
case_eq (eq_dec_l x1 x2).
intros.
reflexivity.
case_eq (eq_dec_p x1 x2).
intros.
reflexivity.
intros.
clear H0 H1 H2 H3 H4 H5 H6 H7 H8 H9.
rewrite e0 in *.
rewrite e1 in *.
assert( HH0 : Intersect x1 x2).
unfold Intersect.
exists e.
destruct a2.
destruct a3.
split.
assumption.
assumption.
contradiction.
destruct (a1_exist c e).
simpl.
case_eq (eq_dec_l x x1).
case_eq (eq_dec_u b c).
intros.
reflexivity.
case_eq (eq_dec_u d e).
intros.
reflexivity.
destruct (a1_exist b c).
simpl.
destruct (a1_exist d e).
simpl.
case_eq (eq_dec_l x2 x3).
intros.
reflexivity.
case_eq (eq_dec_p x2 x3).
intros.
reflexivity.
intros.
clear H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
rewrite e0 in *.
rewrite e1 in *.
destruct a0.
destruct a1.
destruct a3.
assert( HH0 := uniqueness b c x0 x2 H1 H2 H4 H5).
destruct HH0.
contradiction.
rewrite H6 in *.
assert( HH0 : Intersect x2 x3).
unfold Intersect.
exists d.
destruct a4.
split.
assumption.
assumption.
contradiction.
case_eq (eq_dec_p x x1).
case_eq (eq_dec_u b c).
intros.
reflexivity.
case_eq (eq_dec_u d e).
intros.
reflexivity.
destruct (a1_exist b c).
simpl.
destruct (a1_exist d e).
simpl.
case_eq (eq_dec_l x2 x3).
intros.
reflexivity.
case_eq (eq_dec_p x2 x3).
intros.
reflexivity.
intros.
clear H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.
rewrite e0 in *.
destruct a0.
destruct a1.
destruct a3.
assert( HH0 := uniqueness b c x0 x2 H1 H2 H4 H5).
destruct HH0.
contradiction.
rewrite H6 in *.
assert( HH0 : Intersect x2 x3).
unfold Intersect.
exists d.
destruct a4.
split.
assumption.
assumption.
contradiction.
intros.
inversion H7.
case_eq (eq_dec_p x x0).
case_eq (eq_dec_u c e).
case_eq (eq_dec_u b c).
intros.
reflexivity.
case_eq (eq_dec_u d e).
intros.
reflexivity.
destruct (a1_exist b c).
simpl.
destruct (a1_exist d e).
simpl.
case_eq (eq_dec_l x1 x2).
intros.
reflexivity.
case_eq (eq_dec_p x1 x2).
intros.
reflexivity.
intros. 
clear H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
rewrite e0 in *.
assert( HH0 : Intersect x1 x2).
unfold Intersect.
exists e.
destruct a2.
destruct a3.
split.
assumption.
assumption.
contradiction.
destruct (a1_exist c e).
simpl.
case_eq (eq_dec_l x x1).
case_eq (eq_dec_u b c).
intros.
reflexivity.
case_eq (eq_dec_u d e).
intros.
reflexivity.
destruct (a1_exist b c).
simpl.
destruct (a1_exist d e).
simpl.
case_eq (eq_dec_l x2 x3).
intros.
reflexivity.
case_eq (eq_dec_p x2 x3).
intros.
reflexivity.
intros.
clear H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.
rewrite e0 in *.
destruct a0.
destruct a2.
destruct a3.
assert( HH0 := uniqueness b c x1 x2 H1 H2 H4 H5).
destruct HH0.
contradiction.
rewrite H6 in *.
assert( HH0 : Intersect x2 x3).
unfold Intersect.
exists e.
destruct a4.
split.
assumption.
assumption.
contradiction.
case_eq (eq_dec_p x x1).
case_eq (eq_dec_u b c).
intros.
reflexivity.
case_eq (eq_dec_u d e).
intros.
reflexivity.
destruct (a1_exist b c).
simpl.
destruct (a1_exist d e).
simpl.
case_eq (eq_dec_l x2 x3).
intros.
reflexivity.
case_eq (eq_dec_p x2 x3).
intros.
reflexivity.
intros.
clear H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.
(* Triple Pasch *)
(* Pasch 1 *)
unfold Intersect in i.
destruct i.
unfold Intersect in i0.
destruct i0.
destruct a0.
destruct a1.
destruct a2.
destruct a3.
destruct a4.
destruct H0.
destruct H1.
case_eq (eq_dec_u x5 e).
intros.
rewrite e0 in *.
assert( HH0 := uniqueness c e x0 x1 H4 H13 H6 H7).
destruct HH0.
contradiction.
rewrite H15 in *.
assert( HH0 := uniqueness d e x1 x3 H5 H7 H10 H11).
destruct HH0.
contradiction.
rewrite H16 in *.
assert( HH0 : Intersect x2 x3).
unfold Intersect.
exists c.
split.
assumption.
assumption.
contradiction.
intros.
case_eq (eq_dec_u x4 d).
intros.
rewrite e0 in *.
assert( HH0 := uniqueness c d x0 x1 H4 H5 H6 H12).
destruct HH0.
rewrite H16 in *.
assert( HH0 := uniqueness d e x1 x3 H6 H7 H10 H11).
destruct HH0.
contradiction.
rewrite H17 in *.
assert( HH0 : Intersect x2 x3).
unfold Intersect.
exists d.
split.
assumption.
assumption.
contradiction.
rewrite H16 in *.
assert( HH0 := uniqueness d e x1 x3 H5 H7 H10 H11).
destruct HH0.
contradiction.
rewrite H17 in *.
assert( HH0 : Intersect x2 x3).
unfold Intersect.
exists c.
split.
assumption.
assumption.
contradiction.
intros.
case_eq (eq_dec_u x4 x5).
intros.
clear H14 H15 H16.
rewrite e0 in *.
assert( HH0 := uniqueness c x5 x0 x1 H4 H13 H6 H12).
destruct HH0.
rewrite <-H14 in *.
assert( HH0 := uniqueness b c x x2 H3 H0 H8 H9).
destruct HH0.
contradiction.
rewrite H15 in *.
assert( HH0 : collinear a b c = true).
unfold collinear.
case_eq (eq_dec_u a b).
intros.
reflexivity.
intros.
destruct (a1_exist a b).
simpl.
case_eq (incid_dec c x6).
intros.
reflexivity.
intros.
destruct a0.
assert( HH0 := uniqueness a b x2 x6 H2 H3 H18 H19).
destruct HH0.
contradiction.
rewrite H20 in *.
contradiction.
rewrite HH0 in H.
inversion H.
rewrite H14 in *.
assert( HH0 := uniqueness d e x1 x3 H5 H7 H10 H11).
destruct HH0.
contradiction.
rewrite H15 in *.
assert( HH0 : Intersect x2 x3).
unfold Intersect.
exists c.
split.
assumption.
assumption.
contradiction.
intros.
(* Cas degenere x4 = e *)
case_eq (eq_dec_u x4 e).
intros.
clear H14 H15 H16 H17.
rewrite e0 in *.
case_eq (eq_dec_u x5 d).
intros.
rewrite e1 in *.
assert( HH0 := uniqueness d e x x3 H1 H0 H10 H11).
destruct HH0.
contradiction.
rewrite H15 in *.
assert( HH0 : Intersect x2 x3).
unfold Intersect.
exists b.
split.
assumption.
assumption.
contradiction.
intros.
case_eq (eq_dec_u b d).
intros.
rewrite e1 in *.
assert( HH0 : Intersect x2 x3).
unfold Intersect.
exists d.
split.
assumption.
assumption.
contradiction.
intros.
case_eq (eq_dec_u b e).
intros.
rewrite e1 in *.
assert( HH0 : Intersect x2 x3).
unfold Intersect.
exists e.
split.
assumption.
assumption.
contradiction.
intros.
assert( HH0 : dist4 b e c d).
unfold dist4.
split.
assumption.
split.
assumption.
split.
assumption.
split.
intro.
rewrite H17 in *.
apply n4.
reflexivity.
split.
assumption.
assumption.
assert( HH1 : Incid b x /\ Incid e x).
split.
assumption.
assumption.
assert( HH2 : Incid c x0 /\ Incid d x0).
split.
assumption.
assumption.
assert( HH3 : Incid b x2 /\ Incid c x2).
split.
assumption.
assumption.
assert( HH4 : Incid e x3 /\ Incid d x3).
split.
assumption.
assumption.
assert( HH5 : exists I : Point, Incid I x /\ Incid I x0).
exists x5.
split.
assumption.
assumption.
assert( HH6 := a2 b e c d x x0 x2 x3 HH0 HH1 HH2 HH3 HH4 HH5).
destruct HH6.
assert( HH7 : Intersect x2 x3).
unfold Intersect.
destruct H17.
exists x6.
split.
assumption.
assumption.
contradiction.
intros.
(* Cas degenere  x5 = d *)
case_eq (eq_dec_u x5 d).
intros.
case_eq (eq_dec_u b d).
intros.
rewrite e1 in *.
assert( HH0 : Intersect x2 x3).
unfold Intersect.
exists d.
split.
assumption.
assumption.
contradiction.
intros.
case_eq (eq_dec_u b e).
intros.
rewrite e1 in *.
assert( HH0 : Intersect x2 x3).
unfold Intersect.
exists e.
split.
assumption.
assumption.
contradiction.
intros.
rewrite e0 in *.
assert( HH0 : dist4 d b e c).
unfold dist4.
split.
intro.
clear H19.
rewrite H21 in *.
apply n12.
reflexivity.
split.
assumption.
split.
intro.
rewrite H21 in *.
apply n6.
reflexivity.
split.
assumption.
split.
assumption.
intro.
rewrite H21 in *.
apply n4.
reflexivity.
assert( HH1 : Incid d x /\ Incid b x).
split.
assumption.
assumption.
assert( HH2 : Incid e x1 /\ Incid c x1).
split.
assumption.
assumption.
assert( HH3 : Incid d x3 /\ Incid e x3).
split.
assumption.
assumption.
assert( HH4 : Incid b x2 /\ Incid c x2).
split.
assumption.
assumption.
assert( HH5 : exists I : Point, Incid I x /\ Incid I x1).
exists x4.
split.
assumption.
assumption.
assert( HH6 := a2 d b e c x x1 x3 x2 HH0 HH1 HH2 HH3 HH4 HH5).
destruct HH6.
destruct H21.
assert( HH7 : Intersect x2 x3).
unfold Intersect.
exists x6.
split.
assumption.
assumption.
contradiction.
intros.
(* Cas non degenere *)
assert( HH0 : dist4 x5 d x4 e).
unfold dist4.
split.
assumption.
split.
intro.
clear H16.
rewrite H19 in n10.
apply n10.
reflexivity.
split.
assumption.
split.
intro.
clear H15.
rewrite H19 in *.
apply n9.
reflexivity.
split.
assumption.
assumption.
assert( HH1 : Incid x5 x0 /\ Incid d x0).
split.
assumption.
assumption.
assert( HH2 : Incid x4 x1 /\ Incid e x1).
split.
assumption.
assumption.
assert( HH3 : Incid x5 x /\ Incid x4 x).
split.
assumption.
assumption.
assert( HH4 : Incid d x3 /\ Incid e x3).
split.
assumption.
assumption.
assert( HH5 : exists I : Point, Incid I x0 /\ Incid I x1).
exists c.
split.
assumption.
assumption.
assert( HH6 := a2 x5 d x4 e x0 x1 x x3 HH0 HH1 HH2 HH3 HH4 HH5).
destruct HH6.
destruct H19.
assert( HH7 := a1_exist b d).
destruct HH7.
case_eq (eq_dec_u b x4).
intros.
rewrite <-e0 in *.
assert( HH8 := uniqueness b c x1 x2 H12 H6 H8 H9).
destruct HH8.
contradiction.
rewrite H22 in *.
assert( HH8 : Intersect x2 x3).
unfold Intersect.
exists e.
split.
assumption.
assumption.
contradiction.
intros.
case_eq (eq_dec_u b d).
intros.
rewrite e0 in *.
assert( HH8 : Intersect x2 x3).
unfold Intersect.
exists d.
split.
assumption.
assumption.
contradiction.
intros.
case_eq (eq_dec_u b e).
intros.
rewrite e0 in *.
assert( HH8 : Intersect x2 x3).
unfold Intersect.
exists e.
split.
assumption.
assumption.
contradiction.
(* Pasch 2 *)
intros.
assert( HH8 : dist4 b x4 d e).
unfold dist4.
split.
assumption.
split.
assumption.
split.
assumption.
split.
assumption.
split.
assumption.
assumption.
destruct a0.
assert( HH9 : Incid b x /\ Incid x4 x).
split.
assumption.
assumption.
assert( HH10 : Incid d x3 /\ Incid e x3).
split.
assumption.
assumption.
assert( HH11 : Incid b x7 /\ Incid d x7).
split.
assumption.
assumption.
assert( HH12 : Incid x4 x1 /\ Incid e x1).
split.
assumption.
assumption.
assert( HH13 : exists I : Point, Incid I x /\ Incid I x3).
exists x6.
split.
assumption.
assumption.
assert( HH14 := a2 b x4 d e x x3 x7 x1 HH8 HH9 HH10 HH11 HH12 HH13).
destruct HH14.
destruct H26.
(* Pasch 3 *)
assert( HH15 : dist4 b d c e).
unfold dist4.
split.
assumption.
split.
assumption.
split.
assumption.
split.
intro.
rewrite H28 in *.
apply n6.
reflexivity.
split.
assumption.
assumption.
assert( HH16 : Incid b x7 /\ Incid d x7).
split.
assumption.
assumption.
assert( HH17 : Incid c x1 /\ Incid e x1).
split.
assumption.
assumption.
assert( HH18 : Incid b x2 /\ Incid c x2).
split.
assumption.
assumption.
assert( HH19 : Incid d x3 /\ Incid e x3).
split.
assumption.
assumption.
assert( HH20 : exists I : Point, Incid I x7 /\ Incid I x1).
exists x8.
split.
assumption.
assumption.
assert( HH21 := a2 b d c e x7 x1 x2 x3 HH15 HH16 HH17 HH18 HH19 HH20).
destruct HH21.
destruct H28.
assert( HH22 : Intersect x2 x3).
unfold Intersect.
exists x9.
split.
assumption.
assumption.
contradiction.
intros.
inversion H8.
intros.
inversion H4.
Qed.

Lemma col_to_cop :
forall x x0 x1 x2,
collinear x x0 x1 = true -> coplanar x x0 x1 x2 = true.
Proof.
intros.
generalize H.
unfold coplanar.
intros.
case_eq (eq_dec_u x x0).
intros.
reflexivity.
intros.
case_eq (eq_dec_u x1 x2).
intros.
reflexivity.
intros.
destruct (a1_exist x x0).
destruct (a1_exist x1 x2).
simpl.
case_eq (eq_dec_l x3 x4).
intros.
reflexivity.
intros.
case_eq (eq_dec_p x3 x4).
intros.
reflexivity.
intros.
generalize H.
unfold collinear.
case_eq (eq_dec_u x x0).
intros.
contradiction.
destruct (a1_exist x x0).
simpl.
case_eq (incid_dec x1 x5).
intros.
destruct a.
destruct a1.
assert (HH0 := uniqueness x x0 x3 x5 H8 H9 H10 H11).
destruct HH0.
contradiction.
clear H5.
rewrite <-H12 in *.
assert( HH0 : Intersect x3 x4).
unfold Intersect.
exists x1.
split.
assumption.
destruct a0.
assumption.
contradiction.
intros.
inversion H7.
Qed.

Global Instance coplanar_morph : Proper (eq ==> eq ==> eq ==> eq ==> Logic.eq) coplanar.
Proof.
repeat red.
intros; subst.
unfold coplanar.
case_eq(eq_dec_u y y0).
reflexivity.
case_eq(eq_dec_u y1 y2).
reflexivity.
intros.

destruct(a1_exist y y0).
destruct(a1_exist y1 y2).
simpl.
reflexivity.
Qed.

End s_psohEquivCop.

Ltac my_cop2 :=
  repeat match goal with
  |[H : coplanar ?W ?X ?Y ?Z = true |- coplanar ?W ?X ?Y ?Z = true] => solve[intuition]
  |[H : coplanar ?W ?X ?Z ?Y = true |- coplanar ?W ?X ?Y ?Z = true] => rewrite cop_exchange2;solve[intuition]
  |[H : coplanar ?W ?Y ?X ?Z = true |- coplanar ?W ?X ?Y ?Z = true] => rewrite cop_exchange3;solve[intuition]
  |[H : coplanar ?W ?Y ?Z ?X = true |- coplanar ?W ?X ?Y ?Z = true] => rewrite cop_exchange3;rewrite cop_exchange2;solve[intuition]
  |[H : coplanar ?W ?Z ?X ?Y = true |- coplanar ?W ?X ?Y ?Z = true] => rewrite cop_exchange2;rewrite cop_exchange3;solve[intuition]
  |[H : coplanar ?W ?Z ?Y ?X = true |- coplanar ?W ?X ?Y ?Z = true] => rewrite cop_exchange2;rewrite cop_exchange3;rewrite cop_exchange2;solve[intuition]
  |[H : coplanar ?X ?W ?Y ?Z = true |- coplanar ?W ?X ?Y ?Z = true] => rewrite cop_exchange1;solve[intuition]
  |[H : coplanar ?X ?W ?Z ?Y = true |- coplanar ?W ?X ?Y ?Z = true] => rewrite cop_exchange1;rewrite cop_exchange2;solve[intuition]
  |[H : coplanar ?X ?Y ?W ?Z = true |- coplanar ?W ?X ?Y ?Z = true] => rewrite cop_exchange1;rewrite cop_exchange3;solve[intuition]
  |[H : coplanar ?X ?Y ?Z ?W = true |- coplanar ?W ?X ?Y ?Z = true] => rewrite cop_exchange1;rewrite cop_exchange3;rewrite cop_exchange2;solve[intuition]
  |[H : coplanar ?X ?Z ?W ?Y = true |- coplanar ?W ?X ?Y ?Z = true] => rewrite cop_exchange1;rewrite cop_exchange2;rewrite cop_exchange3;solve[intuition]
  |[H : coplanar ?X ?Z ?Y ?W = true |- coplanar ?W ?X ?Y ?Z = true] => rewrite cop_exchange1;rewrite cop_exchange3;rewrite cop_exchange2;rewrite cop_exchange3;solve[intuition]
  |[H : coplanar ?Y ?W ?X ?Z = true |- coplanar ?W ?X ?Y ?Z = true] => rewrite cop_exchange3;rewrite cop_exchange1;solve[intuition]
  |[H : coplanar ?Y ?W ?Z ?X = true |- coplanar ?W ?X ?Y ?Z = true] => rewrite cop_exchange3;rewrite cop_exchange1;rewrite cop_exchange2;solve[intuition]
  |[H : coplanar ?Y ?X ?W ?Z = true |- coplanar ?W ?X ?Y ?Z = true] => rewrite cop_exchange3;rewrite cop_exchange1;rewrite cop_exchange3;solve[intuition]
  |[H : coplanar ?Y ?X ?Z ?W = true |- coplanar ?W ?X ?Y ?Z = true] => rewrite cop_exchange3;rewrite cop_exchange1;rewrite cop_exchange3;rewrite cop_exchange2;solve[intuition]
  |[H : coplanar ?Y ?Z ?W ?X = true |- coplanar ?W ?X ?Y ?Z = true] => rewrite cop_exchange3;rewrite cop_exchange1;rewrite cop_exchange2;rewrite cop_exchange3;solve[intuition]
  |[H : coplanar ?Y ?Z ?X ?W = true |- coplanar ?W ?X ?Y ?Z = true] => rewrite cop_exchange3;rewrite cop_exchange1;rewrite cop_exchange2;rewrite cop_exchange3;rewrite cop_exchange2;solve[intuition]
  |[H : coplanar ?Z ?W ?X ?Y = true |- coplanar ?W ?X ?Y ?Z = true] => rewrite cop_exchange2;rewrite cop_exchange3;rewrite cop_exchange1;solve[intuition]
  |[H : coplanar ?Z ?W ?Y ?X = true |- coplanar ?W ?X ?Y ?Z = true] => rewrite cop_exchange2;rewrite cop_exchange3;rewrite cop_exchange1;rewrite cop_exchange2;solve[intuition]
  |[H : coplanar ?Z ?X ?W ?Y = true |- coplanar ?W ?X ?Y ?Z = true] => rewrite cop_exchange2;rewrite cop_exchange1;rewrite cop_exchange3;rewrite cop_exchange1;solve[intuition]
  |[H : coplanar ?Z ?X ?Y ?W = true |- coplanar ?W ?X ?Y ?Z = true] => rewrite cop_exchange2;rewrite cop_exchange3;rewrite cop_exchange1;rewrite cop_exchange3;rewrite cop_exchange2;solve[intuition]
  |[H : coplanar ?Z ?Y ?W ?X = true |- coplanar ?W ?X ?Y ?Z = true] => rewrite cop_exchange2;rewrite cop_exchange3;rewrite cop_exchange1;rewrite cop_exchange2;rewrite cop_exchange3;solve[intuition]
  |[H : coplanar ?Z ?Y ?X ?W = true |- coplanar ?W ?X ?Y ?Z = true] => rewrite cop_exchange2;rewrite cop_exchange3;rewrite cop_exchange1;rewrite cop_exchange3;rewrite cop_exchange2;rewrite cop_exchange3;solve[intuition]
end.