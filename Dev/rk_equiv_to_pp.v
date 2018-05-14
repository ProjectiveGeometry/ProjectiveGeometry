Require Export ProjectiveGeometry.Dev.rank_plane_properties.


(*****************************************************************************)
(** Proof of projective space geometry to matroid' **)


Section s_rkEquivToPp.

Context `{RPP : RankProjectivePlane}.
Context `{EP : EqDecidability Point}.

(*** Definition LineInd ***)
Inductive LineInd : Type :=
| Cline : forall (A B : Point) (H: ~ A [==] B), LineInd.

Definition Line := LineInd.

(*** Definition fstP ***)
Definition fstP : Line -> Point.
intros.
elim H0.
intros.
exact A.
Defined.

(*** Definition sndP ***)
Definition sndP : Line -> Point.
intros.
elim H0.
intros.
exact B.
Defined.

(*** Definition Incid ***)
Definition Incid (A : Point)(l : Line) := rk (triple (fstP l) (sndP l) A) = 2.

Lemma incid_dec :  forall (A : Point)(l : Line), {Incid A l} + {~Incid A l}.
Proof.
intros.
unfold Incid.
exact (eq_nat_dec (rk (triple (fstP l) (sndP l) A)) 2).
Qed.

Lemma second_point : forall A : Point, {B : Point | ~ A [==] B}.
Proof.
intros.
assert (T:= rk_lower_dim).
destruct T.
destruct s.
destruct s.
assert(HH0 := rk_three_points).
assert(HH1 := HH0 A x).
destruct HH1.
destruct a.
destruct H1.
assert(HH := couple_rk1 A x2 H2).
exists x2.
assumption.
Qed.

Definition line_eq l m := rk (quadruple (fstP l) (sndP l) (fstP m) (sndP m)) = 2.

Lemma line_eq_refl : forall l, line_eq l l.
Proof.
intro.
induction l.
unfold line_eq, Incid.
simpl.
setoid_replace (quadruple A B A B) with (couple A B) by (clear_all;fsetdecide).
apply rk_couple1.
auto.
Qed.

Lemma line_eq_sym : forall l m, line_eq l m -> line_eq m l.
Proof.
intros.
induction l.
induction m.
unfold line_eq, Incid in *.
simpl in *.
setoid_replace (quadruple A0 B0 A B) with (quadruple A B A0 B0).
auto.
clear_all;fsetdecide.
Qed.

Lemma line_eq_trans : forall l m n, line_eq l m -> line_eq m n -> line_eq l n.
Proof.
intros.
induction l.
induction m.
induction n.
unfold line_eq, Incid in *.
simpl in *.
assert (rk (union (quadruple A B A0 B0) (quadruple A0 B0 A1 B1)) +
           rk (couple A0 B0) <=
           rk (quadruple A B A0 B0) + rk (quadruple A0 B0 A1 B1)).
apply matroid3_useful.
clear_all;fsetdecide.
assert (rk (couple A0 B0) = 2).
apply rk_couple1;auto.
assert (rk (union (quadruple A B A0 B0) (quadruple A0 B0 A1 B1)) <= 2).
omega.
apply le_antisym.
cut (rk (quadruple A B A1 B1) <= rk (union (quadruple A B A0 B0) (quadruple A0 B0 A1 B1)) ).
omega.
apply matroid2;clear H0 H1 H5 H6 H7; fsetdecide.
assert (rk (couple A1 B1) = 2).
apply rk_couple1;auto.
rewrite <- H8.
apply matroid2.
clear_all;fsetdecide.
Qed.

Lemma a1_exist : forall (A B :Point) , {l : Line | Incid A l /\ Incid B l}.
Proof.
intros.
assert(HH := rk_three_points A B).
destruct HH.
destruct a.
destruct H1.
assert(HH0 := couple_rk1 A x H2).
exists (Cline A x HH0).
unfold Incid.
simpl.
split.
setoid_replace (triple A x A) with (couple A x) by (clear_all;fsetdecide).
assumption.
setoid_replace (triple A x B) with (triple A B x) by (clear_all;fsetdecide).
assumption.
Qed.

Lemma uniqueness : forall (A B :Point)(l1 l2 : Line),
   Incid A l1 -> Incid B l1  -> Incid A l2 -> Incid B l2 -> A [==] B \/ line_eq l1 l2.
Proof.
intros A B l1 l2.
case_eq(eq_dec A B);intros.
solve[intuition].
induction l1.
induction l2.
intros.
right.
unfold Incid, line_eq in *.
simpl in *.
assert (rk (couple A0 B0) = 2).
apply rk_couple1;assumption.
assert (rk (couple A1 B1) = 2).
apply rk_couple1;assumption.
assert (rk (couple A B) = 2).
apply rk_couple1;assumption.

assert (rk (quadruple A0 B0 A B) = 2).
apply le_antisym.
assert (rk (union (triple A0 B0 A) (triple A0 B0 B)) + rk (couple A0 B0) <=
           rk (triple A0 B0 A) + rk (triple A0 B0 B)).
apply (matroid3_useful (triple A0 B0 A) (triple A0 B0 B) (couple A0 B0)).
clear_all;fsetdecide.
setoid_replace (union (triple A0 B0 A) (triple A0 B0 B)) with (quadruple A0 B0 A B) in H10.
omega.
clear_all;fsetdecide.
rewrite <- H1.
apply matroid2.
clear_all;fsetdecide.

assert (rk (quadruple A1 B1 A B) = 2).
apply le_antisym.
assert (rk (union (triple A1 B1 A) (triple A1 B1 B)) + rk (couple A1 B1) <=
           rk (triple A1 B1 A) + rk (triple A1 B1 B)).
apply (matroid3_useful (triple A1 B1 A) (triple A1 B1 B) (couple A1 B1)).
clear_all;fsetdecide.
setoid_replace (union (triple A1 B1 A) (triple A1 B1 B)) with (quadruple A1 B1 A B) in H11.
omega.
clear_all;fsetdecide.
rewrite <- H3.
apply matroid2.
clear_all;fsetdecide.
 
assert (rk (union (quadruple A0 B0 A B) (quadruple A1 B1 A B)) +
           rk (couple A B) <=
           rk (quadruple A0 B0 A B) + rk (quadruple A1 B1 A B)).
apply (matroid3_useful (quadruple A0 B0 A B) (quadruple A1 B1 A B) (couple A B)).
clear_all;fsetdecide.
assert (rk (union (quadruple A0 B0 A B) (quadruple A1 B1 A B)) <= 2).
omega.
apply le_antisym.
assert (rk (quadruple A0 B0 A1 B1) <= rk (union (quadruple A0 B0 A B) (quadruple A1 B1 A B))).
apply matroid2.
clear_all;fsetdecide.
omega.
rewrite <- H7.
apply matroid2.
clear_all;fsetdecide.
Qed.

Lemma a2_exist : forall (l1 l2 : Line), {A : Point | Incid A l1 /\ Incid A l2}.
Proof.
intros.
induction l1.
induction l2.
assert(HH := rk_inter A B A0 B0).
destruct HH.
exists x.
unfold Incid.
simpl.
assumption.
Qed.

Lemma a3_1 : forall l : Line, { A : Point & { B : Point & { C : Point | 
~ A [==] B /\ ~ A [==] C /\ ~ B [==] C /\ Incid A l /\ Incid B l /\ Incid C l}}}.
Proof.
intros.
induction l.
exists A.
exists B.
elim (rk_three_points A B).
intro C.
intros.
exists C.
unfold Incid.
simpl.
setoid_replace (triple A B A) with (couple A B).
setoid_replace (triple A B B) with (couple A B).
assert (rk (couple A B) = 2).
apply rk_couple1;auto.
intuition.
rewrite H3 in H5.
apply couple_rk1 in H5;intuition.
rewrite H3 in H4.
apply couple_rk1 in H4;intuition.
apply triple_couple_1.
assumption.
apply triple_couple_4.
assumption.
Qed.

Lemma a3_2 : {l1 : Line & {l2 : Line | l1 <> l2}}.
Proof.
assert(HH := rk_lower_dim).
destruct HH.
destruct s.
destruct s.
assert(HH0 := rk_three_points x x0).
destruct HH0.
destruct a.
destruct H1.
assert(HH1 := couple_rk1 x x2 H2).
exists (Cline x x2 HH1).
assert(HH2 := rk_three_points x x1).
destruct HH2.
destruct a.
destruct H4.
assert(HH3 := couple_rk1 x x3 H5).
exists (Cline x x3 HH3).
intro.
inversion H6.
rewrite H8 in *.
assert (rk (union (triple x x0 x3) (triple x x1 x3)) + rk (couple x x3) <=
           rk (triple x x0 x3) + rk (triple x x1 x3)).
apply matroid3_useful.
clear_all;fsetdecide.
rewrite H0 in H7.
rewrite H3 in H7.
rewrite H5 in H7.
setoid_replace (union (triple x x0 x3) (triple x x1 x3)) with (quadruple x x0 x1 x3) in H7.
assert(HH4 : rk (quadruple x x0 x1 x3) <= 2).
omega.
assert(HH5 : rk (triple x x0 x1) <= rk (quadruple x x0 x1 x3)).
apply matroid2.
clear_all;fsetdecide.
omega.
clear_all;fsetdecide.
Qed.

(*
Require Export ProjectiveGeometry.Dev.projective_plane_axioms.

Instance ObjectPointFano : ObjectPoint := {
Point := Point
}.


Instance ProjectiveStructureFano : ProjectiveStructure ObjectPointFano := {
Line := s_rkEquivToPp.Line;
Incid := s_rkEquivToPp.Incid
}.
apply LineInd.
apply Incid.

Print Line.
Line := Line
}.
;
Incid := Incid;
incid_dec := incid_dec
}.

Instance ProjectiveStructureLEFano : ProjectiveStructureLE ProjectiveStructureFano := {
a1_exist := a1_exist
}.

Instance ProjectiveStructureLEUFano : ProjectiveStructureLEU ProjectiveStructureLEFano := {
uniqueness := uniqueness
}.

Instance PreProjectivePlaneFano : PreProjectivePlane ProjectiveStructureLEUFano := {
a2_exist := a2_exist
}.

Instance ProjectivePlaneFano : ProjectivePlane PreProjectivePlaneFano := {
a3 := a3
}.
*)

End s_rkEquivToPp.