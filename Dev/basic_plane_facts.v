Require Export ProjectiveGeometry.Dev.projective_plane_axioms.

Section s_basicPlaneFacts.

Context `{PP : ProjectivePlane'}.
Context `{EP : EqDecidability Point}.

Lemma incidABl : forall (A B:Point)(l:Line), ~Incid A l /\ Incid B l -> ~ A [==] B.
Proof.
intros l1 l2 A H Hl2l1;rewrite Hl2l1 in *; tauto.
Qed.

Hint Resolve incidABl : incidence.

Lemma incidAl1l2 :forall (l1 l2:Line)(A:Point), ~Incid A l1 /\ Incid A l2 -> l2 <> l1.
Proof.
intros A B l H HAB; subst A; tauto.
Qed.

Hint Resolve incidAl1l2 : incidence.

Lemma a1_unique:forall (A B :Point)(l1 l2:Line),
  ~A[==]B -> Incid A l1 -> Incid B l1  -> Incid A l2 -> Incid B l2 -> l1=l2.
Proof.
intros A B l1 l2 HAB HAl1 HBl1 HAl2 HBl2.
assert ((A=B)\/(l1=l2)).
apply uniqueness; intuition.
intuition.
Qed.

Lemma a2_unique : forall(l m :Line)(A B :Point), 
  l<>m -> Incid A l -> Incid A m -> Incid B l -> Incid B m -> A[==]B. 
Proof.
intros l1 l2 A B Hl1l2 HAl1 HAl2 HBl1 HBl2.
assert ((A[==]B)\/(l1=l2)).
apply uniqueness; intuition.
intuition.
Qed.

Lemma second_point : forall A:Point, forall l:Line, Incid A l -> {B : Point | (~ B [==]A) /\ (Incid B l)}.
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
{C : Point | ~A[==]B /\ ~B[==]C /\ ~A[==]C /\ Incid C l}.
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

End s_basicPlaneFacts.