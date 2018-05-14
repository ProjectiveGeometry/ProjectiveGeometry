Require Export ProjectiveGeometry.Dev.projective_space_axioms.

Section s_basicSpaceFacts.

Context `{PS : ProjectiveSpace}.
Context `{EP : EqDecidability Point}.

Lemma incidABl : forall (A B:Point)(l:Line), ~Incid A l /\ Incid B l -> A <> B.
Proof.
intros A B l H2 HAB.
subst A.
tauto.
Qed.

Hint Resolve incidABl : incidence.

Lemma incidAl1l2 : forall (l1 l2:Line)(A:Point), ~Incid A l1 /\ Incid A l2 -> l2 <> l1.
Proof.
intros l1 l2 A H2 Hl2l1. 
subst l1.
tauto.
Qed.

Hint Resolve incidAl1l2 : incidence.

Lemma a1_unique : forall (A B : Point)(l1 l2 : Line),
  ~ A [==] B -> Incid A l1 -> Incid B l1  -> Incid A l2 -> Incid B l2 -> l1=l2.
Proof.
intros.
assert (A[==]B\/l1=l2).
eapply uniqueness; intuition.
intuition.
Qed.

Lemma a2_unique : forall(l1 l2 : Line)(A B : Point),
  l1<>l2 -> Incid A l1 -> Incid A l2 -> Incid B l1 -> Incid B l2 -> A [==] B.
Proof.
intros.
assert (A [==] B\/l1=l2).
eapply uniqueness; intuition.
intuition.
Qed.

Lemma eq_line_dec : forall d1 d2 : Line, d1 = d2\/d1 <> d2.
Proof.
generalize a3_1 a3_2.
intros Hsa31' Hsa32'.
intros l1 l2.
elim (Hsa31' l1).
intros M HM; elim HM; clear HM; intros N HN; elim HN; clear HN; intros P HMNP.
elim (incid_dec M l2).
intros HMl2; elim (incid_dec N l2).
intros HNl2.
left.
decompose [and] HMNP.
assert ((N [==] M)\/(l1=l2)).
apply uniqueness; intuition.
assert (~ N [==] M).
decompose [and] HMNP.
intro.
rewrite H11 in H6.
apply H6.
reflexivity.
destruct H4.
contradiction.
assumption.

intro.
right.
apply incidAl1l2 with (A:=N).
intuition.
intro.
right.
apply incidAl1l2 with (A:=M); intuition.
Qed.

Lemma two_lines_aux : 
  forall P, forall l, ~Incid P l -> exists m:Line, exists n:Line, m<>n /\ Incid P m /\ Incid P n.
Proof.
generalize a3_1 a3_2 a3_3.
intros H1 H2 H3.
intros P l HPl.
elim (H1 l).
intros A HA; elim HA; clear HA; intros B HB; elim HB; clear HB; intros C HC.
elim (a1_exist P A).
intros l1 Hl1.
elim (a1_exist P B).
intros l2 Hl2.
exists l1.
exists l2.
intuition.
subst.
assert ((A [==] B)\/l2=l).
apply uniqueness; intuition.
case H11.
intro.
intuition.
intro.
subst;
intuition.
Qed.

Lemma two_lines_P : forall P:Point, exists l1:Line, exists l2:Line, l1<>l2/\Incid P l1/\Incid P l2.
Proof.
generalize a3_3 a3_2 a3_1.
intros H1 H2 H3.
intros P.
elim H2; intros l1 Hl1; elim Hl1; clear Hl1; intros l2 Hl2.
elim (incid_dec P l1).
intros.
elim (incid_dec P l2).
intros.
assert False.
apply (Hl2 P); intuition.
intuition.
intros HPl2.
eapply two_lines_aux; eauto with incidence.
intros HPl2.
eapply two_lines_aux; eauto with incidence.
Qed.

Lemma only_one_intersection : forall l1 l2:Line, forall B C:Point,Incid C l1 /\ ~Incid C l2 /\ Incid B l2 /\ ~Incid B l1 ->
exists l3:Line,   l1 <>l3 /\ l2 <> l3/\ (Intersect l3 l1) /\(Intersect l3 l2).
Proof.
intros l1 l2 B C (HCl1,(HCl2,( HBl2, HBl1))).
elim (a1_exist B C).
intros l (HBl, HCl).
exists l.
split.
intro; subst; intuition.
split.
intro;subst;intuition.
unfold Intersect; firstorder.
Qed.

Lemma two_points_not_incident_l1l2 : 
forall l1 l2:Line, l1<>l2 -> exists B, 
(Incid B l1 /\ ~Incid B l2) /\ exists C, 
(~Incid C l1 /\ Incid C l2).
Proof.
intros l1 l2 Hl1l2.
elim (a3_1 l1); intros A1 HA1; elim HA1; clear HA1; intros B1 HB1; elim HB1; clear HB1; intros C1 Hl1.
elim (a3_1 l2); intros A2 HA2; elim HA2; clear HA2; intros B2 HB2; elim HB2; clear HB2; intros C2 Hl2.
elim (incid_dec A1 l2).
intros.
assert (~Incid B1 l2).
intro.
assert (A1 [==] B1).
apply a2_unique with (l1:=l1) (l2:=l2); intuition.
intuition.
elim (incid_dec A2 l1).
intros.
assert (~Incid B2 l1).
intro.
assert (A2 [==] B2).
apply a2_unique with (l1:=l1) (l2:=l2); intuition.
intuition.
firstorder.

intro.

firstorder.
intro.
exists A1.
firstorder.

elim (incid_dec A2 l1).
intros HA2l1.
assert (~Incid B2 l1).
intro.
assert (A2 [==] B2).
apply a2_unique with (l1:=l1) (l2:=l2); intuition.
intuition.
firstorder.
intros HA2l1.
firstorder.
Qed.

Lemma third_line : forall l1 l2:Line, 
exists l3 :Line,  l1 <>l3 /\ l2 <> l3/\ (Intersect l3 l1) /\(Intersect l3 l2).
Proof.
intros l1 l2.
elim (eq_line_dec l1 l2).
intro; subst.
elim (a3_1 l2); intros A2 HA2; elim HA2; clear HA2; intros B2 HB2; elim HB2; clear HB2; intros C2 Hl2.
elim (two_lines_P A2).
intros d1 Hd1; elim Hd1; intros d2 Hd.
elim (eq_line_dec l2 d1).
intro; subst.
exists d2.
unfold Intersect in *; firstorder.
intro; subst.
exists d1.
unfold Intersect in *; firstorder.
intros Hl1l2.
elim (two_points_not_incident_l1l2 l1 l2 Hl1l2).
intros A (HA, Hex).
elim Hex; intros B HB. 
apply (only_one_intersection l1 l2 B A).
intuition.
Qed.

Lemma a3_3simplified : forall l1 l2:Line, exists l3 :Line, l1 <>l3 /\ l2 <> l3.
Proof.
intros l1 l2; elim (third_line l1 l2).
intros l H2; elim H2; intros A HA; elim HA; intros B HB.
exists l; intuition.
Qed.

Lemma second_line : forall l1 : Line, exists l2:Line, l1<>l2.
Proof.
intros l1.
elim a3_2.
intros d1 H2; elim H2; intros d2 H'.
elim (third_line l1 d2).
intros d (Hd1, (Hd2, (HexI, HexJ))).
exists d.
intuition.
Qed.

Lemma second_point : forall A:Point, forall l:Line, Incid A l -> exists B : Point, (~ B [==]A)/\(Incid B l).
Proof.
intros A l HAl.
elim (a3_1 l).
intros P1 H2.
elim H2; intros P2 H'.
elim H'; intros P3 H''.
elim (eq_dec_u A P1).
intros HAP1.
exists P2.
rewrite HAP1.
intuition.
intros HAP1.
exists P1.
intuition.
Qed.

Lemma third_point : forall A B : Point, forall l:Line,
~ A [==]B /\ Incid A l /\ Incid B l ->
exists C : Point, ~A[==]B /\ ~B[==]C /\ ~A[==]C /\ Incid C l.
Proof.
intros A B l HABl.
elim (a3_1 l).
intros P1 H2.
elim H2; intros P2 H'.
elim H'; intros P3 H''.
elim (eq_dec_u A P1).
intros HAP1.

decompose [and] H''.
intuition.
rewrite <- HAP1 in *.

elim (eq_dec_u B P2).
intros HBP2.
rewrite <- HBP2 in *.
exists P3.
intuition.
intros HBP2.
exists P2.
intuition.
intros HBP2.
decompose [and] HABl; clear HABl.
decompose [and] H''; clear H''.
decompose [and] H2;clear H2.

elim (eq_dec_u B P1).
intros HBP1.
elim (eq_dec_u A P2).
intros.
exists P3.
rewrite HBP1 in *.
rewrite a in *.
intuition.

intros HAP2.
rewrite HBP1 in *.

elim (eq_dec_u B P2).
intros.
rewrite a in *.
cut False;
intuition.

exists P2.
intuition.
exists P1.
intuition.
Qed.

Lemma line_equivalence : forall l1 l2, l1 = l2 <-> forall M : Point, (Incid M l1 <-> Incid M l2).
Proof.
intros.
split.

intros.
split.

intros.
rewrite H in H0;assumption.
intros.
rewrite <-H in H0;assumption.

intros.
assert(HH := a3_1 l1).
destruct HH.
destruct s.
destruct s.
destruct a.
destruct H1.
destruct H2.
destruct H3.
destruct H4.
assert(HH := H x).
assert(HH0 := H x0).
destruct HH.
assert(HH := H6 H3).
destruct HH0.
assert(HH0 := H8 H4).
assert(HH1 := uniqueness x x0 l1 l2 H3 H4 HH HH0).
destruct HH1.
rewrite H10 in H0.
apply False_ind;apply H0;reflexivity.
assumption.
Qed.

End s_basicSpaceFacts.
