Require Export ProjectiveGeometry.Dev.p_equiv_colwa.

(*****************************************************************************)
(** Contains three non collinear points **)


Section s_pEquivC3P.

Context `{PSLEU : ProjectiveStructureLEU}.
Context `{EP : EqDecidability Point}.
Context `{OP : OrderedType Point}.

(*** Definition contains_three_non_collinear_points ***)
Fixpoint contains_three_non_collinear_points l :=
match l with
| nil => false
| a::r => if collinear_with_all a (all_pairs r) 
              then contains_three_non_collinear_points r
              else true
end.

Lemma contains_1 : forall l, contains_three_non_collinear_points l = true <-> 
exists A B C, InA eq A l /\ InA eq B l /\ InA eq C l /\ collinear A B C = false.
Proof.
induction l.
simpl;split; intros Hc.
discriminate.
destruct Hc as [A [B [C (HA,HBC)]]].
inversion HA.
simpl.
case_eq (collinear_with_all a (all_pairs l)); intros Hall.
split.
intros Hc.
apply IHl in Hc.
destruct Hc as [A [B [C (HA,(HB,(HC,HABC)))]]].
exists A.
exists B.
exists C.
repeat split.
apply InA_cons_tl; assumption.
apply InA_cons_tl; assumption.
apply InA_cons_tl; assumption.
assumption.
intros.
apply IHl.
destruct H as [A [B [C (HA,(HB,(HC, Hcol)))]]].
destruct (eq_dec_u B C) as [Heq | Hneq].
rewrite Heq in Hcol.
assert (T: collinear A C C = true).
apply col_2.
rewrite T in Hcol; inversion Hcol.
destruct (eq_dec_u A C) as [HeqC | HneqC].
rewrite HeqC in Hcol.
assert (T:collinear C B C= true).
rewrite col_shift.
apply col_2.
rewrite T in Hcol; inversion Hcol.
destruct (eq_dec_u A B) as [HeqB | HneqB].
rewrite HeqB in Hcol.
assert (T:collinear B B C= true).
apply col_1.
rewrite T in Hcol; inversion Hcol.

assert (U:collinear_with_all a (all_pairs (a::l))=true).
simpl.
apply collinear_app.
apply collinear_with_all_map.
assumption.

inversion HA; subst.
assert (T:InA eq2 (B, C) (all_pairs (a :: l))\/InA eq2 (C, B) (all_pairs (a :: l))).
apply (InA_eq_eq2_all_pairs B C (a::l) HB HC Hneq).
destruct T as [T | T].
rewrite( col_with_all_col a (all_pairs (a::l)) U B C T) in Hcol.
inversion Hcol.
assert (Hcol':collinear a C B = false).
rewrite col_shift; rewrite col_exchange; rewrite <- col_shift.
assumption.
rewrite( col_with_all_col a (all_pairs (a::l)) U C B T) in Hcol'.
inversion Hcol'.

inversion HB; subst.

assert (T:InA eq2 (A, C) (all_pairs (a :: l))\/InA eq2 (C, A) (all_pairs (a :: l))).
apply (InA_eq_eq2_all_pairs A C (a::l) HA HC HneqC).
destruct T as [T | T].
assert (Hcol': collinear a A C = false).
rewrite col_exchange; assumption.
rewrite( col_with_all_col a (all_pairs (a::l)) U A C T) in Hcol'.
inversion Hcol'.
assert (Hcol': collinear a C A = false).
rewrite <- col_shift; assumption.
rewrite( col_with_all_col a (all_pairs (a::l)) U C A T) in Hcol'.
inversion Hcol'.

inversion HC; subst.
assert (T:InA eq2 (A, B) (all_pairs (a :: l))\/InA eq2 (B, A) (all_pairs (a :: l))).
apply (InA_eq_eq2_all_pairs A B (a::l) HA HB HneqB).
destruct T as [T | T].
assert (Hcol': collinear a A B = false).
rewrite col_shift; assumption.
rewrite( col_with_all_col a (all_pairs (a::l)) U A B T) in Hcol'.
inversion Hcol'.
assert (Hcol': collinear a B A = false).
rewrite col_shift; rewrite col_exchange; assumption.
rewrite( col_with_all_col a (all_pairs (a::l)) U B A T) in Hcol'.
inversion Hcol'.

exists A.
exists B.
exists C.
repeat split; assumption.

intros.
generalize (contains_1_aux a (all_pairs l)); intros Hyp.
split.
intros.
apply Hyp in Hall; clear Hyp.
exists a.
destruct Hall as [B [C (HBC,Hcol)]].
exists B.
exists C.
split.
apply InA_cons_hd; reflexivity.
destruct  (InA_eq2_eq_all_pairs B C l HBC) as [HB HC].
split.
apply InA_cons_tl; assumption.
split.
apply InA_cons_tl; assumption.
assumption.
solve [intuition].
Qed.

Lemma contains_2 : forall l, contains_three_non_collinear_points l = false <-> 
forall A B C, InA eq A l -> InA eq B l -> InA eq C l -> collinear A B C = true.
Proof.
induction l.
simpl.
split.
intros.
inversion H0.
solve [trivial].
(* -> *)
split; intros.
simpl in H.
case_eq (collinear_with_all a (all_pairs l)).
intros.
inversion H0; subst.
inversion H1; subst.
apply col_1.
inversion H2; subst.
rewrite col_shift; apply col_2.

destruct (eq_dec_u B C).
rewrite e.
rewrite col_shift; apply col_1.
eapply col_aux; try eassumption.
apply InA_eq_eq2_all_pairs; assumption.

inversion H1; subst.
inversion H2; subst.
apply col_2.
destruct (eq_dec_u A C).
rewrite e.
rewrite col_exchange; apply col_2.
rewrite col_exchange.
eapply col_aux; try eassumption.
apply InA_eq_eq2_all_pairs; assumption.

inversion H2; subst.
rewrite <- col_shift.
destruct (eq_dec_u A B).
rewrite e.
apply col_2.
eapply col_aux; try eassumption.
apply InA_eq_eq2_all_pairs; assumption.

destruct IHl as [IHl1 IHl2].
rewrite H3 in H.
generalize (IHl1 H); intros Hr; clear IHl1 IHl2.
apply Hr; assumption.
intros Hrew; rewrite Hrew in H.
inversion H.
(* <- *)
simpl.
case_eq (collinear_with_all a (all_pairs l)).
intros; apply IHl.
intros.
apply H.
apply InA_cons_tl; assumption.
apply InA_cons_tl; assumption.
apply InA_cons_tl; assumption.
intros.
apply False_ind; eapply forall_InA_collinear_with_all; eassumption.
Qed.

Lemma matroid3_aux1 : forall l, forall a,
collinear_with_all a (all_pairs (l)) = true ->
contains_three_non_collinear_points (l) = false.
Proof.
intros.
induction l.
simpl.
reflexivity.
simpl.
case_eq (collinear_with_all a0 (all_pairs l)).
intros.
apply IHl.
assert (HH := matroid3_aux0 l a a0 H).
assumption.
intros.
assert (HH := matroid3_aux0_bis l a a0 H).
rewrite HH in H0.
inversion H0.
Qed.

Lemma contains_three_non_collinear_points_sublist_aux :
forall l, forall a,
contains_three_non_collinear_points l = true ->
contains_three_non_collinear_points (a :: l) = true.
Proof.
intro.
induction l.
- intros.
  simpl in *.
  discriminate.
- intros.
  simpl.
  case_eq (collinear_with_all a0 (map_monotonic (fun x : Point => (a, x)) l ++ all_pairs l)).
  (* 1.collinear_with_all a0 (map (fun x : Point => (a, x)) l ++ all_pairs l) *)
    intro.
    apply H.
  (* 2.collinear_with_all a0 (map (fun x : Point => (a, x)) l ++ all_pairs l) *)
    intro.
    reflexivity.
Qed.

Lemma contains_three_non_collinear_points_sublist :
forall l m, inclA eq l m ->
(contains_three_non_collinear_points l = true) ->
(contains_three_non_collinear_points m = true).
Proof.
intros l m Hincl Hc.
apply contains_1 in Hc.
apply contains_1.
destruct Hc as [A [B [C (HA,(HB,(HC,Hcol)))]]].
exists A; exists B; exists C.
split.
apply Hincl; assumption.
split.
apply Hincl; assumption.
split.
apply Hincl; assumption.
assumption.
Qed.

Global Instance contains_three_morph : Proper (@equivlistA Point eq ==> (@Logic.eq bool)) contains_three_non_collinear_points.
Proof.
repeat red;intros.
case_eq (contains_three_non_collinear_points x);
  case_eq (contains_three_non_collinear_points y).
solve [trivial].
intros Hp1 Hp2.
apply contains_1 in Hp2.
generalize (contains_2 y) ; intros Hg; destruct Hg as[Hg1 Hg2].
generalize (Hg1 Hp1); intros Hq; clear Hg1 Hg2.
destruct Hp2 as [X [Y [Z HXYZ]]].
rewrite Hq in HXYZ.
solve [intuition].
rewrite <- H; solve [intuition].
rewrite <- H; solve [intuition].
rewrite <- H; solve [intuition].

intros Hp1 Hp2.
generalize (contains_1 y); intros Hg; destruct Hg as [Hg1 Hg2].
generalize (Hg1 Hp1); intros Hq; clear Hg1 Hg2.
generalize (contains_2 x); intros Hh; destruct Hh as [Hh1 Hh2].
generalize (Hh1 Hp2); intros Hr; clear Hh1 Hh2.
destruct Hq as [X [Y [Z (HX,(HY,(HZ, HXYZ)))]]].
rewrite <- H in HX,HY,HZ.
rewrite Hr in HXYZ.
inversion HXYZ.
assumption.
assumption.
assumption.
solve [trivial].
Qed.

Lemma contains_three_to_two :
forall l,forall x,
contains_three_non_collinear_points (x :: l) = true ->
contains_two_distinct_points l = true.
Proof.
intros.
induction l.
- intros.
  simpl in *.
  discriminate.
- intros.
  simpl.
  case_eq l.
  (* 1.case_eq l *)
    intro.
    rewrite H0 in *.
    inversion H.
  (* 2.case_eq l *)
    intros.
    case (eq_dec_u).
    (* 1.case (DecPoints.eq_dec) *)
      intros.
      rewrite H0 in *.
      apply IHl.
      rewrite e in H.
      assert( HH : equivlistA eq (x :: p :: p :: l0) (x :: p :: l0)).
      my_inA.
      rewrite <-HH.
      assumption.
    (* 2.case (DecPoints.eq_dec) *)
      intro.
      reflexivity.
Qed.

Lemma contains_three_to_two_bis :
forall l,forall x,
contains_three_non_collinear_points (l++(x::nil)) = true ->
contains_two_distinct_points l = true.
Proof.
intros.
induction l.
- intros.
  simpl in *.
  discriminate.
- intros.
  simpl.
  case_eq l.
  (* 1.case_eq l *)
    intro.
    rewrite H0 in *.
    inversion H.
  (* 2.case_eq l *)
    intros.
    case (eq_dec_u).
    (* 1.case (DecPoints.eq_dec) *)
      intros.
      rewrite H0 in *.
      apply IHl.
      rewrite e in H.
      assert( HH : equivlistA eq ((p :: p :: l0) ++ x :: nil) ((p :: l0) ++ x :: nil)).
      my_inA.
      rewrite <-HH.
      assumption.
    (* 2.case (DecPoints.eq_dec) *)
      intro.
      reflexivity.
Qed.

End s_pEquivC3P.
