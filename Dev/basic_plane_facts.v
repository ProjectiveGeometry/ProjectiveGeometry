Require Export ProjectiveGeometry.Dev.projective_plane_axioms.

Section s_basicPlaneFacts.

Context `{PPP : PreProjectivePlane}.

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

End s_basicPlaneFacts.