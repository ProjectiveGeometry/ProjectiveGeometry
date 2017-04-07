Require Export ProjectiveGeometry.Dev.p_equiv_list_additions.

(*****************************************************************************)
(** Contains two distinct points **)


Section s_pEquivC2P_1.

Context `{PS : ProjectiveStructure}.
Context `{EP : EqDecidability Point}.
Context `{OP : OrderedType Point}.

(*** Definition c2p ***)
Fixpoint contains_two_distinct_points l :=
match l with 
| nil => false
| a :: nil => false
| a:: ((b::q) as reste) =>  if (eq_dec_u a b) then (contains_two_distinct_points (reste)) else true
end.

Functional Scheme c_two := Induction for contains_two_distinct_points Sort Prop.

End s_pEquivC2P_1.


Ltac my_ctwo :=
  intuition
  repeat match goal with
  |[H : _ |- _] => progress intros
  |[H : _ |- _] => progress intro
  |[H : _ |- _] => progress intuition
  |[H : _ |- _] => progress subst
  |[H : _ |- contains_two_distinct_points _ = _] => progress simpl
  |[H : _ |- (if ?X then _ else _)= _] => destruct X
  |[H : _ |- _] => intuition
  end.


Section s_pEquivC2P_2.

Context `{PS : ProjectiveStructure}.
Context `{EP : EqDecidability Point}.
Context `{OP : OrderedType Point}.

Global Instance contains_two_morph : Proper (@equivlistA Point eq ==> (@Logic.eq bool)) contains_two_distinct_points.
Proof.
repeat red.

intros x y.
generalize x;clear x.
elim y using c_two.
intros; subst.
apply equivlistA_nil_eq in H.
rewrite H.
reflexivity.
solve [intuition].
intros l a reste Hl Hreste; subst.
intros x; elim x using c_two.
intros; trivial.
intros; trivial.
intros; simpl; subst.
apply H.
unfold equivlistA.
intros; split; intros.
apply H0; solve [intuition].
rewrite _x0 in *.
assert (T:InA eq x0 (b::b::_x)).
apply H0; solve [intuition].
inversion T.
rewrite H3 in *.
solve [intuition].
assumption.

intros; simpl; subst.
assert (T:InA eq a0 (a::nil)).
apply H; solve [intuition].
inversion T.
assert (U:InA eq b (a::nil)).
apply H; solve [intuition].
inversion U.
rewrite <- H1 in *.
apply False_ind; apply _x0; symmetry; solve [intuition].
inversion H4.
inversion H1.

intros; subst.
rewrite H.
trivial.
red; intros; split; intros.
assert (T:InA eq x0 (a:: b::_x)).
apply H0; assumption.
inversion T.
rewrite H3 in *.
rewrite _x0 in *.
apply InA_cons_hd.
reflexivity.
assumption.
apply H0.
apply InA_cons_tl.
assumption.

intros l a reste Hl b _x Hreste _x0 Heq_dec x; subst.
elim x using c_two.
intros; subst.
assert (T:InA eq a nil).
apply (H a); solve [intuition].
inversion T.
intros;subst.
assert (T:InA eq a (a0::nil)).
apply (H a); solve [intuition].
inversion T.
assert (U:InA eq b (a0::nil)).
apply (H b); solve [intuition].
inversion U.
clear Heq_dec;rewrite H1 in _x0;rewrite H4 in _x0.
apply False_ind;my_inA.
inversion H4.
inversion H1.

intros; simpl; subst.
apply H.
red; intros; split; intros.
apply H0; solve [intuition].
clear e1; rewrite _x2 in *.
assert (T:InA eq x0 (b0::b0::_x1)).
apply H0; solve [intuition].
inversion T.
rewrite H3 in *.
solve [intuition].
assumption.

intros; subst; solve [trivial].
Qed.

Lemma contains_two_distinct_points_sublist_aux : forall l, forall a,
contains_two_distinct_points l = true ->
contains_two_distinct_points (a::l) = true.
Proof.
my_ctwo;case_eq l;my_ctwo.
Qed.

Lemma contains_two_distinct_points_sublist :
forall l m, inclA eq l m -> 
(contains_two_distinct_points l = true) ->
(contains_two_distinct_points m = true).
Proof.
intros l m;elim l using c_two.
- my_ctwo.
- my_ctwo.
- my_ctwo;my_inA.
- my_ctwo;my_inA;
  revert H; elim m using c_two.
  + my_ctwo;assert(HH := H b);my_inA.
  + my_ctwo. case_eq(eq_dec_u a a0);assert(HH := H b).
    intros;clear e1;my_subst;my_inA.
    assert(HH0 := H a);my_inA.
  + my_ctwo;my_inA;apply H;my_ctwo.
    assert(HH := H1 x);my_inA;my_ctwo.
  + my_ctwo.
Qed.

End s_pEquivC2P_2.