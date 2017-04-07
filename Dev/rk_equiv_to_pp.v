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

Lemma second_point : forall A : Point, exists B : Point, ~ A [==] B.
Proof.
intro.
assert (T:= rk_lower_dim).
case_eq(eq_dec P0 A);intros.
case_eq(eq_dec P1 P0);intros.
rewrite e0 in *.
case_eq(eq_dec P2 P0);intros.
rewrite e1 in *.
setoid_replace (triple P0 P0 P0) with (singleton P0) in T by (clear_all;fsetdecide).
rewrite rk_singleton in T.
cut False.
intuition.
omega.
exists P2;rewrite <-e;intuition.
exists P1;rewrite <-e;intuition.
exists P0;intuition.
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

Lemma a1_exist : forall (A B :Point) , exists l : Line , Incid A l /\ Incid B l.
Proof.
intros.
case_eq(eq_dec A B);intros.
elim (second_point B).
intros C H1.
exists (Cline B C H1).
unfold Incid.
simpl.
rewrite e.
setoid_replace (triple B C B) with (couple C B) by (clear_all;fsetdecide).
split.
apply rk_couple1.
solve[intuition].
apply rk_couple1.
solve[intuition].
exists (Cline A B n).
unfold Incid.
simpl.
setoid_replace (triple A B A) with (couple A B) by (clear_all;fsetdecide).
setoid_replace (triple A B B) with (couple A B) by (clear_all;fsetdecide).
split.
apply rk_couple1.
solve[intuition].
apply rk_couple1.
solve[intuition].
Qed.

Lemma uniqueness : forall (A B :Point)(l1 l2:Line),
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

Lemma a2_exist : forall (l1 l2 : Line), exists A : Point, Incid A l1 /\ Incid A l2.
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

Lemma a3_1 : forall l : Line, exists A : Point, exists B : Point, exists C : Point, 
~ A [==] B /\ ~ A [==] C /\ ~ B [==] C /\ Incid A l /\ Incid B l /\ Incid C l.
Proof.
intros.
induction l.
exists A.
exists B.
elim (rk_three_points_on_lines A B).
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
rewrite H4 in H5.
apply couple_rk1 in H5;intuition.
apply couple_rk1 in H1;intuition.
apply triple_couple_1.
assumption.
apply triple_couple_4.
assumption.
Qed.

Lemma a3_2 : exists l1 : Line,exists l2 : Line, l1 <> l2.
Proof.
exists (Cline P0 P1 base_points_distinct_1).
exists (Cline P1 P2 base_points_distinct_2).
intro.
inversion H0.
assert(HH0 := base_points_distinct_1).
rewrite H2 in HH0.
apply False_ind.
apply HH0.
reflexivity.
Qed.

End s_rkEquivToPp.