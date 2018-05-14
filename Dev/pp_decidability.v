Require Export ProjectiveGeometry.Dev.basic_plane_facts.

Section s_ProjectivePlane'Decidability.

Context `{PP : ProjectivePlane'}.

Lemma eq_dec_point_sublemma :  
  forall A B : Point, forall d : Line, ~Incid A d -> ~Incid B d -> {A [==] B} + {~A [==] B}.
Proof.
generalize a3_1 a3_2.
intros Ha31' Ha32'.
intros A B d HAd HBd.
elim (Ha31' d).
intros M HM.
elim HM; clear HM; intros N HN.
elim HN; clear HN; intros P HMNP.
elim (a1_exist A M).
intros l1 Hl1.
elim (a1_exist A N).
intros l2 Hl2.
assert (l1 <> l2).
intros Hl1l2.
subst l1.
elim Hl2; intros Hl2a Hl2b.
elim Hl1; intros Hl1a Hl1b.
assert (~ N [==] M).
destruct HMNP;intro;rewrite H1 in H;apply H;reflexivity.
elim HMNP; clear HMNP; intros Hdist3 HMNP.
elim HMNP; clear HMNP; intros HM HNP.
elim HNP; clear HNP; intros HN HP.
destruct HP;destruct H1.
generalize (a1_unique N M l2 d H Hl2b Hl1b H1 H0).
intros Hl2d.
subst l2.
solve[intuition].
elim (incid_dec B l1).
intros HBl1.
elim (incid_dec B l2).
intros HBl2.
left.
eapply a2_unique.
apply H.
solve[intuition].
solve[intuition].
assumption.
assumption.
intros HBl2.
right.
assert (~ B [==] A) ; [idtac | intuition].
eapply incidABl.
split.
apply HBl2.
solve[intuition].
intros HBl1.
right.
assert (~ B [==] A); [idtac | intuition].
eapply incidABl.
split.
apply HBl1.
solve[intuition].
Qed.

Lemma eq_dec_point : forall A B: Point, {A [==] B} + {~A [==] B}.
Proof.
generalize a3_1 a3_2.
intros Ha31' Ha32'.
elim Ha32'; intros delta_0 Hdelta.
elim Hdelta; clear Hdelta; intros delta_1 Hdelta.
intros A B.
elim (incid_dec A delta_0).
intros HAd.
elim (incid_dec B delta_0).
intros HBd.
elim (incid_dec A delta_1).

(* cas1 *)
intros HAd1.
elim (incid_dec B delta_1).
intros HBd1.
left.
eapply a2_unique;eauto.

intros HBd1.
right.
assert (~B[==]A).
eapply (incidABl B A);eauto.
solve[intuition].

intros HAd1.
elim (incid_dec B delta_1).
intros HBd1.
right.
eapply incidABl.
split.
apply HAd1.
apply HBd1.
(* cas 2 *)
intros HBd1.
eapply eq_dec_point_sublemma;eauto.

intros HBd.
right.
assert (~B[==]A).
apply (incidABl B A delta_0).
split.
assumption.
assumption.
intuition.

intros HAd.
elim (incid_dec B delta_0).
intros HBd.
right.
eapply incidABl with (l:=delta_0).
split.
assumption.
assumption.
(* cas 2 *)
intros HBd.
eapply eq_dec_point_sublemma; eauto.
Qed.

Lemma eq_dec_line :  
  forall d1 d2 : Line, {d1 = d2} + {d1 <> d2}.
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
decompose [and] HMNP;Collapse2.
destruct H4.
contradiction.
solve[intuition].


intros HNl2.
right.
apply incidAl1l2 with (A:=N).
solve[intuition].
right.
apply incidAl1l2 with (A:=M);solve[intuition].
Qed.

Lemma first_point : forall l : Line, {V : Point| Incid V l}.
Proof.
intros l.
elim (a3_1 l).
intros P HP.
elim HP; intros B HB ; elim HB; intros.
exists P; intuition.
Qed.

(*** essai de preuve de décidabilité de l'incidence à partir de celles de l'égalité
pour les points et aussi pour les droites *)

Lemma incid_dec2 : forall A : Point, forall l : Line, {Incid A l}+{~Incid A l}. 
Proof.
intros A l.
elim (first_point l).
intros M HM.
elim (eq_dec_point A M).
intros;rewrite a; left;solve[intuition].
intros HAM.
elim (a1_exist A M).
intros lAM (HA,HM').
elim (eq_dec_line lAM l).
intros; subst; left; auto.
intros;right; unfold not; intro H.
generalize (a1_unique A M lAM l HAM HA HM' H HM).
intros; subst; intuition.
Qed.

Lemma second_line : forall l1 : Line, { l2 : Line | l1<>l2}.
Proof.
intros l1.
elim a3_2.
intros d1 Hd1.
elim Hd1; clear Hd1; intros d2 Hd1d2.
elim (eq_dec_line l1 d1). 
intros Hl1d1; subst l1.
exists d2.
assumption.
intros Hl1d1.
exists d1.
assumption.
Qed.

Lemma second_point : forall A : Point, forall l : Line, Incid A l -> {B : Point | (~ B [==] A) /\ (Incid B l)}.
Proof.
intros A l HAl.
elim (a3_1 l).
intros P1 H.
elim H; intros P2 H'.
elim H'; intros P3 H''.
elim (eq_dec_point A P1).
intros HAP1;rewrite HAP1 in *.
decompose [and] H''.
exists P2.
solve[intuition].
decompose [and] H''.
exists P1.
solve[intuition].
Qed.

Lemma third_point : forall A B : Point, forall l : Line, ~ A[==]B /\ Incid A l /\ Incid B l -> 
{ C : Point | ~ A[==]B /\ ~ A[==]C /\ ~ B[==]C /\ Incid C l}.
Proof.
intros A B l HABl.
elim (a3_1 l).
intros P1 H.
elim H; intros P2 H'.
elim H'; intros P3 H''.
elim (eq_dec_point A P1).
intros HAP1.
rewrite HAP1 in *.
elim (eq_dec_point B P2).
intros HBP2.
rewrite HBP2 in *.
exists P3.
solve[intuition].
intros HBP2.
exists P2.
solve[intuition].
intros HAP1.
elim (eq_dec_point B P1).
intros HBP1.
rewrite HBP1 in *.
elim (eq_dec_point A P2).
exists P3.
rewrite a in *.
solve[intuition].
intros HAP2.
exists P2.
solve[intuition].
intros HBP1.
exists P1.
solve[intuition].
Qed.

Lemma outsider : forall l1 l2: Line, { P:Point | ~Incid P l1/\~Incid P l2}.
Proof.
intros l1 l2.
elim (eq_dec_line l1 l2).
intros Hl1l2; subst l1.
elim (second_line l2).
intros d Hl2d.
elim (a3_1 d).
intros P HP.
elim (incid_dec P l2).
intros HPl2.
elim (incid_dec P d).
intros HPd.
elim (second_point P d HPd). 
intros Q (HQP,HQd).
exists Q.
assert (~Incid Q l2).
intros HQl2.
apply HQP.
eapply (a2_unique l2 d Q P Hl2d); assumption.
solve[intuition].
intros HPd.
elim (a2_exist l2 d); intros C (HCl2,HCd).
elim (second_point C d HCd). 
intros Q (HQC,HQd).
exists Q.
assert (~Incid Q l2).
intros HQl2.
apply HQC.
apply (a2_unique l2 d Q C); assumption.
solve[intuition].
intros HPl2; exists P; tauto.

intros Hl1l2.
elim (a2_exist l1 l2).
intros C (HCl1,HCl2).
elim (second_point C l1 HCl1).
intros P1 (HP1C,HP1l1).
elim (second_point C l2 HCl2).
intros P2 (HP2C,HP2l2).
elim (a1_exist P1 P2).
intros d (HP1d,HP2d).
elim (eq_dec_point P1 P2).

intros HP1P2.
rewrite HP1P2 in *.
assert (P2[==]C).
eapply (a2_unique l1 l2 P2 C); assumption. 
assert (Hf:False) by (apply (HP2C H)).
elim Hf.
intros HP1P2.
elim (third_point P1 P2 d (conj HP1P2 (conj HP1d HP2d))).
intros newP (Hdist3,HnewPd).
exists newP.
split.
intros HnewPl1.
assert (H : (~ newP[==]P1)) by (solve[intuition]).
apply H.
assert (d<>l1).
intros Hdl1.
subst l1.
apply HP2C.
eapply (a2_unique d l2 P2 C); assumption.
eapply (a2_unique d l1 newP P1);solve[intuition].
intros HnewPl2.
assert (H : (~ newP[==]P2)) by (solve[intuition]).
apply H.
assert (d<>l2).
intros Hdl2.
subst l2.
apply HP1C.
eapply (a2_unique l1 d P1 C) ; assumption.
eapply (a2_unique d l2 newP P2);solve[intuition]. 
Qed.

End s_ProjectivePlane'Decidability.
