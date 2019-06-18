Require Export Arith.
Require Export Ensembles.
Require Export Classical.
Require Export ProjectiveGeometry.Dev.basic_space_facts.
Require Export ProjectiveGeometry.Dev.proof_irrevelance.

(*****************************************************************************)
(** Flat **)

Ltac last_hyp := match goal with H:_ |- _ => destruct H as [H|H]; contradiction || (subst; new_subst) end.

Section s_flat.

Context `{PS : ProjectiveSpace}.
Context `{EP : EqDecidability Point}.
Context `{EL : EqDecidabilityL Line}.

Lemma strong_a2 : forall A B C D:Point, forall lAB lCD lAC lBD :Line, 
 ~ A [==] C -> ~ B [==] D -> 
Incid A lAB/\Incid B lAB ->  
Incid C lCD/\Incid D lCD -> 
Incid A lAC/\Incid C lAC -> 
Incid B lBD/\Incid D lBD ->
(exists I:Point, (Incid I lAB /\ Incid I lCD)) -> 
exists J:Point, (Incid J lAC /\Incid J lBD). 
Proof.
intros A B C D lAB lCD lAC lBD HAC HBD.
intros.
DecompAndAll.
assert (T:exists I : Point, Incid I lAB /\ Incid I lCD) by assumption.
elim T; intros I (HI1,HI2); clear T.

elim (eq_dec_u A D).
intros HAD; new_subst.
exists D; intuition.

intros .
elim (eq_dec_u B C).
intros HB; new_subst. 
exists C; solve [intuition].
intros.
elim (eq_dec_u A B).
intros; new_subst. 
exists B; solve [intuition].
intros.
elim (eq_dec_u C D).
intros; new_subst.
solve [eauto].
intros.
eapply (a2 A B C D lAB lCD lAC lBD).
split;intuition.
split;intuition.
split;intuition.
split;intuition.
split;intuition.
destruct H3.
exists x.
split;intuition.
Qed.

Definition pset := Ensemble Point.

Parameter v_subst : forall v : pset, forall A B : Point, A[==]B -> v A -> v B.

Definition pempty : pset := fun (x:Point) => False.
Definition pspace : pset := fun (x:Point) => True.
Definition psingleton (x:Point) : pset := fun (y:Point) => (x[==]y).
Definition pline (l:Line) : pset := fun (x:Point) => Incid x l.

Definition pplane (l1 l2 : Line) (H1 : l1<>l2) (H2 : Intersect l1 l2) : pset := 
fun (x:Point) => exists l : Line, Incid x l /\ exists I, exists J, ~I[==]J /\ Intersect_In l l1 I /\ Intersect_In l l2 J.

Definition flat (v:pset) : Prop := 
  forall A B:Point, v A -> v B -> ~ A [==] B ->
    forall l:Line, Incid A l -> Incid B l -> 
      forall C:Point, Incid C l -> v C.

(**********************************************************************************)
(*                             Lemmas                                             *)
(**********************************************************************************)

(* the empty set is a flat *)
Lemma fp_empty : flat (pempty).
unfold flat, pempty.
intros; tauto.
Qed.

(* the whole space is a flat *)
Lemma fp_space :  flat (pspace). 
unfold flat, pspace.
tauto.
Qed.

(* singleton points are flats *)
Lemma fp_singleton : forall x:Point, flat (psingleton x). 
intros X; unfold flat,psingleton.
intros A B.
intros.
rewrite H in *.
rewrite H0 in *.
assert False; solve [intuition].
Qed.

(* lines are flats *)
Lemma fp_line : forall l:Line, flat (pline l).
intros l.
unfold pline, flat.
intros A B.
intros HAl HBl  HAB.
intros l0 HAl0 HBl0.

assert (A [==] B\/(l=l0)).
assert (HH := uniqueness A B l l0 HAl HBl HAl0 HBl0).
destruct HH.
left;rewrite H;reflexivity.
right;assumption.
assert (l=l0) by intuition.
subst l0.
intros C HCl.
trivial.
Qed.

(* general case : A I1 I2 B J1 J2 distincts *)
Lemma fp_plane : 
forall l1 l2:Line, forall (H2:l1<>l2), forall (H3:Intersect l1 l2), flat (pplane l1 l2 H2 H3).
intros l1 l2 H2 H3.
unfold flat.
assert (foo := H3); unfold Intersect in ;
elim foo; intro I; intros (HI1, HI2);clear foo.

intros A B HA HB HAB.
intros l HAl HBl C HCl.
unfold pplane in HA, HB.
elim HA; clear HA; intros lA (HAlA,Hexists).
elim Hexists; clear Hexists; intros A1 HA1; 
elim HA1; clear HA1; intros A2 (HA1A2,(HIlAl1,HIlAl2)).
elim HB; clear HB; intros lB (HBlB,Hexists).
elim Hexists; clear Hexists; intros B1 HB1; 
elim HB1; clear HB1; intros B2 (HB1B2,(HIlBl1,HIlBl2)).

intros.
unfold Intersect_In in *.
DecompAndAll.
(* let's get rid of special cases ... *)
elim (incid_dec A l1).
intros HAl1.
elim (incid_dec B l2).
intros HBl2.
unfold pplane.
exists l.
split.
intuition.
exists A.
exists B.
solve [unfold Intersect_In; intuition].
intros HBl2.
assert (HlAlB:exists J : Point, Incid J lA /\ Incid J lB).
apply (strong_a2 A1 B1 A2 B2 l1 l2 lA lB);unfold Intersect_In in *;(solve [intuition]).
elim (eq_dec_u A2 B2).
intro HA2B2; new_subst.

unfold pplane.
CleanDuplicatedHyps.
compute_case.
assert (X:A1[==]A \/ lA = l1) by assumption.
elim X; clear X.
intro; new_subst.

elim (eq_dec_u I B2).
intro HKB2; new_subst.
Collapse2; last_hyp.
Collapse2; last_hyp.
Collapse2; last_hyp.

elim (second_point B2 l2).
intros D (HD1 , HD2).
elim (a1_exist C D).
intros x (HlC, HlD).

exists x.
split; auto.
exists C.
exists D.
unfold Intersect_In.
split.
intro; new_subst.
Collapse2; last_hyp.
Collapse2; last_hyp.
solve [intuition].
solve [intuition].

intro HKB2.

assert (T : exists J, Incid J l2 /\ Incid J l).
apply (strong_a2 I A B2 B l1 lB l2 l); solve [assumption | split; assumption | intuition fo].
elim T; clear T.
intros L (HL1, HL2).

elim (eq_dec_u A L).
intro; new_subst.

Collapse2; last_hyp.
elim (a1_exist C B2).
intros lCB2 (HZ1, HZ2).
assert (T: exists J : Point, Incid J lCB2 /\ Incid J l1).
apply (strong_a2 C I B2 B1 l lB lCB2 l1).
intro;new_subst.
Collapse2; last_hyp.
contradiction.
intro;new_subst.
Collapse2; last_hyp.
contradiction.
assert(HH := uniqueness I L l1 lA HI1 H8 HI2 HAlA).
last_hyp. 
solve[intuition].
Collapse2; last_hyp.

Collapse2; last_hyp.
solve[intuition].
solve[intuition].
solve[intuition].
fo.

elim T; clear T; intros M (HM1 , HM2).
exists lCB2.
split.
solve [intuition].
exists M.
exists B2.
split.
intro; new_subst.
Collapse2; last_hyp.
Collapse2; last_hyp.

solve [unfold Intersect_In; intuition].

intro.
exists l.
split.
solve [auto].
exists A.
exists L.
split; solve [unfold Intersect_In; intuition].

intro; subst.
CleanDuplicatedHyps.

Collapse2; last_hyp.
Collapse2; last_hyp.

elim (second_point B2 l2).
intros D (HD1 , HD2).
elim (a1_exist C D).
intros x (HlC, HlD).

exists x.
split.
solve [auto].
exists C.
exists D.
unfold Intersect_In.
split.

intro;new_subst.
Collapse2; last_hyp.

solve[intuition].
solve[intuition].

intros HA2B2.
unfold pplane.
assert (HNEI2 : (exists J : Point, Incid J l /\ Incid J l2)).
apply (strong_a2  A A2 B B2 lA lB l l2); solve [unfold Intersect_In in *; intuition | fo].
elim HNEI2; clear HNEI2.
intros newI (HnewI1,HnewI2).
elim (incid_dec B l1).
intros HBl1.
assert (Hll1: l=l1).
eapply (a1_unique A B l l1 HAB); solve [intuition].
subst l.
exists l1.
split.
solve [intuition].
elim (second_point newI l1).
intros newJ (HIJ, HJl1).
exists newJ.
exists newI.
split.
assumption.
unfold Intersect_In.
split; solve [intuition].
solve [intuition].

intros HBl1.
assert (Hll1:l<>l1).
intro; subst.
solve [intuition].
elim (eq_dec_l lA l1).
intro; subst.
CleanDuplicatedHyps.

elim (eq_dec_u A newI).
intro HAnewI; rewrite HAnewI in *; clear HAnewI.
Collapse2; last_hyp.

elim (eq_dec_u C B1).
intro; new_subst.
assert(HH := uniqueness newI B1 l l1 HAl HCl H5 H4).
last_hyp.
Collapse2; last_hyp.
contradiction.

intro.
elim (a1_exist C B1).
intros lCB1 (HClCB1 , HB1lCB1).

assert (T:exists J : Point, Incid J lCB1 /\ Incid J l2).
apply (strong_a2 C  newI B1 B2 l lB lCB1 l2);(solve [assumption | (split; assumption) | intuition fo]).
elim T; clear T; intros J (HJ1, HJ2).
exists lCB1.
split.
solve [auto].
exists B1.
exists J.
split.
intro HB1J; rewrite HB1J in *; clear HB1J.
Collapse2; last_hyp.
contradiction.
solve [unfold Intersect_In; intuition].

intro HAnewI.

exists l.
split.
solve [auto].
exists A.
exists newI.

split.
auto.
solve [unfold Intersect_In; auto].

intro HlAl1.

Collapse2; last_hyp.

assert (T: exists J : Point, Incid J l /\ Incid J l2).
apply (strong_a2 B B2 A A2 lB lA l l2); (solve [intuition | destruct HlAlB; fo]).
elim T;intros J (HJ1, HJ2);clear T.

elim (eq_dec_l l l2).
intro;subst.
contradiction.

intros.
elim (eq_dec_u A J).
intro; new_subst.
elim (a1_exist C A2).
intros lCA2 (HlCA2C, HlCA2A2).

elim (a1_exist B1 C).
intros lB1C (HlB1C1, HlB1C2).

assert (T: exists J : Point, Incid J lB /\ Incid J lCA2).
apply (strong_a2 B2 A2 B C l2 l lB lCA2).
intro;new_subst.
Collapse2; last_hyp.
intro;new_subst.
Collapse2; last_hyp.
Collapse2; last_hyp.
solve[intuition].
solve[intuition].
solve[intuition].
solve[intuition].
fo.
elim T; clear T;intros J' (HJ'1, HJ'2).
assert (T: exists J : Point, Incid J lB1C /\ Incid J l2).
apply (strong_a2 B1 B2 C A2 lB lCA2 lB1C l2).
intro;new_subst.
Collapse2; last_hyp.
Collapse2; last_hyp.
Collapse2; last_hyp.
Collapse2; last_hyp.
Collapse2; last_hyp.
intro;new_subst.
Collapse2; last_hyp.
apply HA2B2; reflexivity.
solve[intuition].
solve[intuition].
solve[intuition].
solve[intuition].
fo.
elim T; clear T;intros K (HK1, HK2).
assert (T: exists J : Point, Incid J l1 /\ Incid J lCA2).
apply (strong_a2 B1 C I A2 lB1C l2 l1 lCA2).
intro;new_subst.
Collapse2; last_hyp.
Collapse2; last_hyp.
contradiction.
intro;new_subst.
Collapse2; last_hyp.
Collapse2; last_hyp.
solve[intuition].
solve[intuition].
solve[intuition].
solve[intuition].
fo.
elim T; clear T;intros L (HL1, HL2).

exists lCA2.
split.
solve [auto].
exists  L.
exists A2.
split.
intro;new_subst.
Collapse2; last_hyp.
Collapse2; last_hyp.
Collapse2; last_hyp.
solve [unfold Intersect_In; intuition].

intro.
Collapse2; last_hyp.

exists l.
split.
solve [auto].
exists A.
exists J.
solve [unfold Intersect_In; intuition].

intros HAl1.
elim (incid_dec B l1).
intro.
compute_cases. (* TODO: transform the following in last_hyp *)
assert (X : B1[==]B \/ lB = l1) by assumption.
elim X; clear X.
intro; new_subst. 

elim (eq_dec_u A2 B2).
intro; new_subst.
unfold pplane.
CleanDuplicatedHyps.

elim (eq_dec_l l l2).
intro; subst.
Collapse2; last_hyp.

exists l2.
split.
solve [auto].
exists B; exists B2;repeat split; 
solve [unfold Intersect_In in *; intuition].

intro Hll2.

elim (eq_dec_u A B2).
intro; new_subst.
Collapse2; last_hyp.
exists lB.
split. 
solve [auto].
exists B; exists B2; repeat split; 
 solve [unfold Intersect_In in *; intuition].

intro HAB2.
elim (eq_dec_u B2 I).
intro; new_subst.
Collapse2; last_hyp.
Collapse2; last_hyp.

intro HBIII.
assert (T:exists J : Point, Incid J l /\ Incid J l2).
apply (strong_a2 A B2 B I lA l1 l l2);(solve [intuition | (intro; new_subst;intuition) |fo]). 
elim T; intro Q; intros (HQ1, HQ2);clear T.

elim (eq_dec_u B Q).
intro; new_subst.
Collapse2; last_hyp.

elim (a1_exist C A1).
intro lCA1.
intros (Hx1, Hx2).

elim (eq_dec_u C A1).
intro.
Collapse2; last_hyp.
destruct (a1_exist A1 B2) as [lA1B2 (HA1B2a,HA1B2b)]. 
exists lA1B2.
split.
new_subst.
solve [auto].
exists A1.
exists B2.
solve [unfold Intersect_In in *; intuition].

intro.
assert (T:exists J : Point, Incid J lCA1 /\ Incid J l2).
apply (strong_a2 C Q A1 B2 l lA lCA1 l2); (solve [assumption | split; assumption | intuition fo]).
exists lCA1.
split;auto.
exists A1.
elim T;intro Q';intros (HQ1', HQ2'); clear T.
exists Q'.
unfold Intersect_In; repeat split. 
intro; new_subst.
Collapse2; last_hyp.
Collapse2; last_hyp.
solve[intuition].
solve[intuition].
solve[intuition].
solve[intuition].

intro HnotBQ.
exists l.
split.
solve [auto].
exists B.
exists Q.
solve [unfold Intersect_In; split; auto].

intro HA2B2.
elim (eq_dec_u B I).
intro; new_subst.
Collapse2. (* ??? *)

elim (a1_exist C A2).
intro lCA2.
intros (HX, HY).

elim (eq_dec_u C A2).
intro; new_subst. 
unfold pplane.
exists lA.
split.
solve [auto].
exists A1; exists A2; repeat split; solve [unfold Intersect_In in *; intuition].

intros HCA2.
elim (eq_dec_u I A1).
intro; new_subst.
Collapse2; last_hyp.
Collapse2; last_hyp.
Collapse2; last_hyp.

exists l2.
split.
solve [auto].
exists A1; exists B2;
 solve [unfold Intersect_In in *; intuition].

intros HIA1.

assert (X:exists J : Point, Incid J lCA2 /\ Incid J l1).
apply (strong_a2 C I A2 A1 l lA lCA2 l1); (solve [assumption | split; assumption | intuition fo]). 
elim X;intro Q;intros (HQ1,HQ2);clear X.

exists lCA2.
split.
solve [auto].
exists Q.
exists A2.
split.
intro; new_subst.
Collapse2; last_hyp.
contradiction.
solve [unfold Intersect_In;auto].

intro HI.

assert (X:exists J : Point, Incid J lA /\ Incid J lB).
apply (strong_a2 A1 B A2 B2 l1 l2 lA lB); (solve [intuition]). 
assert (T:exists J : Point, Incid J l /\ Incid J l2).
apply (strong_a2 A A2 B B2 lA lB l l2); (solve [intuition]).
elim T;intro R; intros (HR1, HR2);clear T.
exists l.
unfold Intersect_In.
split.
solve [auto].
exists B.
exists R.
split.
intro; new_subst.
Collapse2; last_hyp.
Collapse2; last_hyp.
solve[intuition].

intro; subst.
assert (T:exists J : Point, Incid J l /\ Incid J l2).
apply (strong_a2 A A2 B B2 lA l1 l l2).
intro;new_subst.
Collapse2; last_hyp.
intro;new_subst.
Collapse2; last_hyp.
contradiction.
solve[intuition].
solve[intuition].
solve[intuition].
solve[intuition].
fo.
elim T; intros Q (HQ1,HQ2); clear T.
elim (eq_dec_u B Q).
intro; new_subst.
Collapse2; last_hyp.

elim (eq_dec_u C A1).
intro; new_subst.
CleanDuplicatedHypsModulo.
exists l1; split; [solve [auto] | idtac].
exists B1; exists Q.
solve [unfold Intersect_In; intuition].
intros HCA1x.
elim (a1_exist C A1).
intros CA1 (HCA1,HCA1').
assert (T:exists J : Point, Incid J CA1 /\ Incid J l2).
apply (strong_a2 C Q A1 A2 l lA CA1 l2). 
intro; new_subst.
Collapse2; last_hyp.
solve[intuition].
intro;new_subst.
Collapse2; last_hyp.
revert H1; intros H1; last_hyp.
solve [intuition].
solve[intuition].
solve[intuition].
solve[intuition].
solve[intuition].
fo.
elim T; intros R (HR1,HR2); clear T.
elim (eq_dec_u A1 R).
intro; new_subst. 
Collapse2; last_hyp.
solve [exists l; firstorder].

intros HA1R.
exists CA1.
split; auto.
exists A1.
exists R.
split.
assumption.
solve [unfold Intersect_In; intuition].

intros HBQ.
exists l.
split; auto.
exists B.
exists Q.
solve [split; unfold Intersect_In; auto].

intros HBl1.
elim (incid_dec A l2).

intros HAl2.
assert (T:exists J : Point, Incid J lA /\ Incid J lB).
apply (strong_a2 A1 B1 A B2 l1 l2 lA lB).
intro;new_subst.
Collapse2; last_hyp.
assumption.
solve[intuition].
solve[intuition].
solve[intuition].
solve[intuition].
fo.
elim (eq_dec_u A1 B1).
intro; new_subst. 
elim (eq_dec_u I B1).
(* A1=B1 et I=B1 *)
intro; new_subst. 
Collapse2; last_hyp.
Collapse2; last_hyp.
Collapse2; last_hyp.
exists l2.
split.
solve [auto].
exists B1.
exists A2.
solve [unfold Intersect_In in *; intuition].

intros HIB1.
assert (X:exists J : Point, Incid J l /\ Incid J l1).
apply (strong_a2 A I B B1 l2 lB l l1); (solve [intuition | exists B2; intuition]).
elim X; intros Q (HQ1,HQ2); clear X.
exists l.
split; auto.
exists Q.
exists A.
split.
intro; new_subst.
Collapse2; last_hyp.
solve [unfold Intersect_In; split; intuition].

intros HA1B1.
assert (U:exists J : Point, Incid J l1 /\ Incid J l).
apply (strong_a2 A1 A B1 B lA lB l1 l); (solve [intuition]).
elim U; intros Q (HQ1,HQ2); clear U.
unfold pplane.
exists l.
split; auto.
exists Q.
exists A.
split ; [idtac | unfold Intersect_In; intuition].
intro;new_subst.
Collapse2; last_hyp.

intros HAl2.
elim (incid_dec B l2).
intros HBl2.
assert (exists J : Point, Incid J lA /\ Incid J lB).
apply (strong_a2 A1 B1 A2 B l1 l2 lA lB).
assumption.
intro; new_subst.
Collapse2; last_hyp.
solve[intuition].
solve[intuition].
solve[intuition].
solve[intuition].
fo.
elim (eq_dec_u A1 B1).
intro; new_subst.
assert (T: exists J : Point, Incid J l1 /\ Incid J l).
apply (strong_a2 B1 A I B lA l2 l1 l).
intro; new_subst.
Collapse2; last_hyp.
contradiction.
solve[intuition].
solve[intuition].
solve[intuition].
solve[intuition].
solve[intuition].
fo.
elim T; intros Q (HQ1,HQ2); clear T.
exists l.
split; auto.
exists Q.
exists B.
split.
intro; new_subst.
Collapse2; last_hyp.

solve [unfold Intersect_In; intuition].

intros HA1B1.
assert (T:exists J : Point, Incid J l /\ Incid J l1).
apply (strong_a2  A A1 B B1 lA lB l l1); (solve[intuition]).
elim T; intros Q (HQ1,HQ2); clear T.
exists l.
split; auto.
exists Q.
exists B.
split.
intro; new_subst.
Collapse2; last_hyp.
solve [unfold Intersect_In; intuition].

intros HBl2.
(* main case : A and B do not belong to l1 and l2. *)
elim (eq_dec_u A1 B1).
intro; new_subst. 
elim (a1_exist I A).
intros KA (HKA1, HKA2).

elim (eq_dec_u I A).
intro; new_subst; solve [intuition].

intro.
assert (T:exists J : Point, Incid J KA  /\ Incid J lB).
apply (strong_a2 I B2 A B1 l2 lA KA lB);solve[intuition | fo].

elim T; clear T; intros M (HM1, HM2).

elim (eq_dec_u I B1).
intro; new_subst.
Collapse2; last_hyp.
Collapse2; last_hyp.
solve[intuition].

intro.
assert (U:exists J : Point, Incid J l1  /\ Incid J l).
apply (strong_a2 I A B1 B KA lB l1 l); (solve [assumption | split; assumption| intuition fo]).
elim U; intros N (HN1 , HN2);clear U.

elim (eq_dec_u A2 B2).
intro; new_subst. 
Collapse2; last_hyp.
Collapse2; last_hyp.
compute_case; last_hyp.
compute_cases; last_hyp. 

unfold pplane.
exists lA.
split.
solve [auto].
exists N.
exists B2.
solve [unfold Intersect_In; intuition].
unfold pplane.
exists lA.
split.
solve [auto].
exists N.
exists B2.
solve [unfold Intersect_In; intuition].
unfold pplane.
exists lA.
split.
solve [auto].
exists N.
exists B2.
solve [unfold Intersect_In; intuition].

intro.

assert (V:exists J : Point, Incid J l /\ Incid J l2).
apply (strong_a2 A A2 B B2 lA lB l l2); (solve [assumption | split; assumption | intuition fo]).
elim V;clear V; intros P (HP1, HP2).

elim (eq_dec_u P N).
intro; new_subst.
Collapse2; last_hyp.
Collapse2; last_hyp.
compute_case.
assert(V := uniqueness M B lB KA HM2 HBlB HM1 HBl).
assert(VV := V).
elim V; clear V. 
intro; new_subst. 
CleanDuplicatedHyps.

unfold pplane.
elim (a1_exist C B1).
intros CB1 (HCB1, HCB2).
assert (T:    exists J : Point, Incid J l2 /\ Incid J CB1).
apply (strong_a2 N C A2 B1 KA lA l2 CB1).
intro;new_subst.
Collapse2; last_hyp.
contradiction.
intro;new_subst.
Collapse2; last_hyp.
contradiction.
solve[intuition].
solve[intuition].
solve[intuition].
solve[intuition].
fo.
elim T; clear T; intros J (HJ1, HJ2).

elim (eq_dec_u B1 J).
intro; new_subst.
Collapse2; last_hyp.
intro.
exists CB1.
split.
solve [auto].
exists B1.
exists J.
solve [unfold Intersect_In; intuition].
intro; subst.
Collapse2; last_hyp.
contradiction.

intro HPN.
exists l.
split.
solve [auto].
exists N.
exists P.
split.
intro; apply HPN; symmetry; assumption.
solve [unfold Intersect_In;auto].

intros HA1B1.
elim (eq_dec_u A2 B2).
intros HA2B2; new_subst.
elim (a1_exist A I).
intros AK (HAK1, HAK2).
assert (T:exists J : Point, Incid J AK /\ Incid J lB).
apply (strong_a2 A B2 I B1 lA l1 AK lB).
intro;new_subst;solve[intuition].
solve[intuition].
solve[intuition].
solve[intuition].
solve[intuition].
solve[intuition].
fo.
elim T; clear T; intros M (HM1, HM2).
assert (U:exists J : Point, Incid J l /\ Incid J l2).
apply (strong_a2 A I B B2 AK lB l l2).
solve[intuition].
intro;new_subst.
Collapse2; last_hyp.
contradiction.
solve[intuition].
solve[intuition].
solve[intuition].
solve[intuition].
fo.
elim U; intros N (HN1,HN2).

assert (V:exists J : Point, Incid J l /\ Incid J l1).
apply (strong_a2 A A1 B B1 lA lB l l1); (solve [assumption | split; assumption | intuition fo]).
elim V; intros P (HP1,HP2).
elim (eq_dec_u P N).
intro; new_subst.
Collapse2; last_hyp.
compute_cases_old.
assert (W:A[==]N \/ AK = l) by assumption.
elim W; clear W.
intro; new_subst.
CleanDuplicatedHyps.
solve[intuition].

intro; subst.
CleanDuplicatedHyps.

elim (a1_exist C B2).
intros CB2 (HCB2,HCB2').
elim (a1_exist C A1).
intros CA1 (HCA1, HCA1').
elim (eq_dec_u C A1).
intro; new_subst.
assert (W:A1[==]B2\/lA=CB2) by (compute_cases_old; assumption).
elim W; clear W.
solve [intro; intuition].
intro; subst.
exists CB2.
split.
assumption.
exists A1; exists B2; repeat split; solve [intuition].

intros HnotCA1.
elim (eq_dec_u C B2).
intro; new_subst.
unfold pplane.
exists CA1.
split.
solve [auto].
exists A1.
exists B2.
split.
solve [intuition].
split; solve [unfold Intersect_In in *; intuition].
intro.
exists CB2.
split.
solve [auto].
elim (eq_dec_u B B1).
intro; new_subst; solve[intuition].
intros HBB1.
assert (W:exists I:Point, Incid I lB /\ Incid I CA1).
apply (strong_a2 B1 A1 B C  l1 l  lB CA1); solve [intuition | destruct V; fo].
assert (X:exists J : Point, Incid J CB2  /\  Incid J l1).
eapply (strong_a2 C A1 B2 B1 CA1 lB CB2 l1); solve [intuition| destruct W; fo]. 
elim X; intros Z (HZ1,HZ2); clear X.
exists Z.
exists B2.
split.
intro; new_subst.
Collapse2; last_hyp.
contradiction.
solve [unfold Intersect_In; intuition].

intros HPN.
unfold pplane.
exists l.
split.
solve [auto].
exists P.
exists N.
split.
solve [auto].
solve [unfold Intersect_In; intuition].
(* ok *)
intros HA2B2.
assert (exists J : Point, Incid J lA /\ Incid J lB).
apply (strong_a2 A1 B1 A2 B2 l1 l2 lA lB); unfold Intersect_In in *; (solve [intuition]).
(* lA lB meet ! *)

assert (HNEI1 : (exists J : Point, Incid J l /\ Incid J l1)).
apply (a2  A A1 B B1 lA lB l l1) ; unfold Intersect_In in *; 
repeat split; solve [intuition | intro; new_subst; Collapse2; intuition].
assert (HNEI2 : (exists J : Point, Incid J l /\ Incid J l2)).
apply (strong_a2  A A2 B B2 lA lB l l2); solve [intuition].
elim HNEI1; clear HNEI1.
elim HNEI2; clear HNEI2.
intros P2 (HP2l,HP2l2); intros  P1 (HP1l,HP1l1).
elim (eq_dec_u P1 P2).
intros HP1P2; new_subst.
assert (Hdist3 : ~(A1[==]P2) /\ ~(A2[==]C)).
split.
intro; new_subst.
Collapse2; last_hyp.
solve[intuition]. 

intro; new_subst.
elim (eq_dec_u A C).
intro; new_subst.
Collapse2; last_hyp.
intros; Collapse2; last_hyp.
elim (eq_dec_u A1 P2).
intros; new_subst.
Collapse2; last_hyp.
contradiction.
intros; Collapse2; last_hyp.
contradiction.

generalize (a1_exist A2 C); intros Hlnew; elim Hlnew; clear Hlnew; intros lnew Hlnew.
assert (HNEI:   exists J : Point, Incid J l1 /\ Incid J lnew).
apply (strong_a2 A1 A2 P2 C lA l l1 lnew); solve [intuition | fo].

elim HNEI; intros X HX.
exists lnew.
split.
intuition.
exists X.
exists A2.
split.
DecompAndAll.
intro; new_subst.
Collapse2; last_hyp.
contradiction.
solve [unfold Intersect_In; intuition].

intros HP1P2.
exists l.
split.
solve [intuition].

exists P1.
exists P2.
solve [unfold Intersect_In; intuition].
Qed.

(* characterization *)

(* decomposition requires excluded middle *)
Lemma set01 : forall v:pset, (exists x:Point, v(x)) \/ forall x:Point, ~v(x).
intros v.
elim (classic (exists x:Point, v(x))).
intros; left; intuition.
intros H2; right.
intros x Hx.
apply H2.
exists x.
assumption.
Qed.

Lemma set12 : forall v:pset, (exists x:Point, v(x)) -> 
(exists a :Point, exists b:Point, ~(a[==]b)/\v(a)/\v(b))\/(exists w:Point, v(w)/\forall p:Point, ~(p[==]w) -> ~v(p)).
intros v H2.
elim H2; intros v1 Hv1; clear H2.
elim (classic (forall p:Point, ~(p[==]v1) -> ~v(p))).
intros Hc.
right.
exists v1.
intuition.
intros Hc.
left.
exists v1.
apply not_all_not_ex.
intros H2.
apply Hc.
intros p Hpv1.
generalize (H2 p).
intuition.
Qed.

Lemma set23 : forall v:pset, (exists a :Point, exists b:Point, ~(a[==]b)/\v(a)/\v(b)) ->
  (exists a :Point, exists b:Point, exists c:Point, ~(a[==]b)/\~(a[==]c)/\~(b[==]c)/\v(a)/\v(b)/\v(c))
\/(exists a:Point, exists b:Point, ~(a[==]b)/\v(a)/\v(b)/\forall p:Point, ~(p[==]a) -> ~(p[==]b) -> ~v(p)).
intros v H2.
elim H2; intros a Ha; clear H2.
elim Ha; intros b (Hab,(Hva,Hvb)).
elim (classic (forall p:Point,  ~(p[==]a) -> ~(p[==]b) -> ~v(p))).
intros Hc.
right.
exists a.
exists b.
intuition.
intros Hc.
left.
exists a.
exists b.
apply not_all_not_ex.
intros H2.
apply Hc.
intros p Hpa Hpb.
generalize (H2 p).
intuition.
Qed.

(* either zero, one, two or at least 3 points in v *)
Lemma pset_decompose : 
forall v:pset, 
(forall x:Point, ~(v x))
\/(exists y:Point, v y /\ forall x:Point, ~x[==]y -> ~v x)
\/(exists x:Point, exists y:Point, ~(x[==]y)/\v(x)/\v(y)/\forall p:Point, ~(p[==]x) -> ~(p[==]y) -> ~v(p))
\/(exists x :Point, exists y:Point, exists z:Point, ~(x[==]y)/\~(x[==]z)/\~(y[==]z)/\v(x)/\v(y)/\v(z)).
Proof.
intros v.
elim (set01 v).
intros H2.
elim (set12 v H2).
intros H'.
elim (set23 v H').
right;right;right.
assumption.
intros H''.
right;right;left.
assumption.
intros H''.
right;left.
assumption.
left.
assumption.
Qed.


(* either v is included in w or there exists p in v and not in w *)
Lemma included_or_not : forall v w: pset,
(forall p:Point, v(p) -> w(p))\/(exists p:Point, v(p)/\~ w(p)).
intros v w.
elim (classic (forall p : Point, v p -> w p)).
intros; left; intuition.
intros;right.
apply not_all_not_ex.
intros H'.
apply H.
intros p Hvp.
elim  (not_and_or (v p) (~ w p) (H' p)).
intros H3; cut False.
intros Hf; elim Hf.
apply H3; assumption.
intros Hnotnot.
elim (classic (w p)).
intuition.
intros Hnot.
elim (Hnotnot Hnot).
Qed.

(* "en dim 3, les seuls plats sont : l'ensemble vide, les points (singletons), les droites (d:M | Incid M d), les plans (l1, l2) et l'espace tout entier" *)

(* intermediate lemma : a line and a plane always intersect *)
Lemma plane_line : forall l1 l2:Line, forall l:Line, forall (H:l1<>l2), forall (H':Intersect l1 l2), 
exists P:Point, pplane l1 l2  H H' P /\ Incid P l.
intros l1 l2 l H2 H'.
elim (eq_line_dec l1 l).
intro; subst.
elim (a3_1 l).
intros A HA; elim HA; clear HA; intros B HB; elim HB; clear HB; intros C (HABC,(HA',(HB',HC'))).
elim (incid_dec A l2).
intros HAl2.
assert (~Incid B l2).
intro HBl2.
compute_cases.
DecompAndAll.
Collapse2.
solve [intuition].
elim (a3_1 l2).
intros A2 HA2; elim HA2; clear HA2; intros B2 HB2; elim HB2; clear HB2; 
  intros C2 (HABC2,(HA2,(HB2,HC2))).
exists B.
elim (incid_dec A2 l).
intros HA2l2.
assert (~Incid B2 l).
intro HB2l.
compute_cases.
DecompAndAll.
Collapse2.
solve [intuition].
elim (a1_exist B B2).
intros m (HBm, HB2m).
unfold pplane.
split; [idtac | auto].
exists m.
split.
auto.
exists B.
exists B2.
split.
intro; new_subst; solve [intuition].
solve [unfold Intersect_In;intuition].
DecompAndAll;solve[intuition].
intros HA2l.
split; [idtac | auto].
elim (a1_exist B A2).
intros m (HBm, HB2m).
unfold pplane.
exists m.
split.
auto.
exists B.
exists A2.
split.
intro; new_subst; solve [intuition].
solve [unfold Intersect_In; intuition].
DecompAndAll;solve[intuition].
intros HAl2.
exists A.
elim (a3_1 l2).
intros A2 HA2; elim HA2; clear HA2; intros B2 HB2; elim HB2; clear HB2; 
  intros C2 (HABC2,(HA2,(HB2,HC2))).
elim (incid_dec A2 l).
intros HA2l.
assert (~Incid B2 l).
intro HB2l.
compute_cases.
DecompAndAll.
Collapse2.
solve [intuition].
elim (a1_exist A B2).
intros m (HBm, HB2m).
split.
unfold pplane.
exists m.
split.
auto.
exists A.
exists B2.
split.
intro;new_subst; solve [intuition].
solve [unfold Intersect_In; intuition].
DecompAndAll;assumption.
intros HA2l.
elim (a1_exist A A2).
intros m (HBm, HA2m).
split.
unfold pplane.
exists m.
split.
auto.
exists A.
exists A2.
split.
intro; new_subst; solve [intuition].
solve [unfold Intersect_In; intuition].
DecompAndAll;assumption.
intros Hl1l.
elim (eq_line_dec l2 l).
intros; subst.
elim (a3_1 l).
intros A HA; elim HA; clear HA; intros B HB; elim HB; clear HB; 
  intros C (HABC,(HA,(HB,HC))).
elim (a3_1 l1).
intros A1 HA1; elim HA1; clear HA1; intros B1 HB1; elim HB1; clear HB1; 
  intros C1 (HABC1,(HA1,(HB1,HC1))).
elim (incid_dec A l1).
intro HAl1.
assert (~Incid B l1).
intro HBl1.
compute_cases.
DecompAndAll.
Collapse2.
solve [intuition].
exists B.
elim (incid_dec A1 l).
intros HA1l.
assert (~Incid B1 l).
intro HB1l.
compute_cases.
DecompAndAll.
Collapse2.
solve [intuition].
split; [idtac | auto].
unfold pplane.
elim (a1_exist B B1).
intros m (HmB,HmB1).
exists m.
split.
auto.
exists B1.
exists B.
split.
intro; new_subst; solve [intuition].
solve [unfold Intersect_In; intuition].
DecompAndAll;solve [intuition].
intros HA1l.
elim (a1_exist B A1).
intros m (HmB,HmA1).
split; [idtac|auto].
exists m.
split;auto.
exists A1.
exists B.
split.
intro; new_subst; solve [intuition]. 
solve [unfold Intersect_In; intuition].
DecompAndAll;solve [intuition].
intros HAl1.
exists A.
elim (incid_dec A1 l).
intros HA1l.
assert (~Incid B1 l).
intro.
compute_cases.
DecompAndAll.
Collapse2.
solve [intuition].
elim (a1_exist B1 A).
intros m (HmB1,HmA).
split.
exists m.
split.
auto.
exists B1.
exists A.
split.
intro; new_subst; solve [intuition].
solve [unfold Intersect_In; intuition].
DecompAndAll;assumption.
intros HA1l.
elim (a1_exist A1 A).
intros m (HmA1,HmA).
split.
exists m.
split.
auto.
exists A1.
exists A.
split.
intro; new_subst; solve [intuition].
solve [unfold Intersect_In; intuition].
DecompAndAll;assumption.

intros Hl2l.
elim (a3_3 l l1 l2).
intros l4 H'4.
elim H'4; clear H'4;intros J1 HJ1;elim HJ1; clear HJ1; 
                                intros J2 HJ2; elim HJ2; clear HJ2.
intros J3 (HJ1,(HJ2,HJ3)).
(* ici commence les problemes*)
exists J1.
split.
exists l.
split.
solve [unfold Intersect_In in *; intuition].

admit.
solve [unfold Intersect_In in *; intuition].
(*
exists J1.
split.
exists l4.
split.
solve [unfold Intersect_In in *; intuition].
exists J2.
exists J3.
solve [unfold Intersect_In in *; intuition].
solve [unfold Intersect_In in *; intuition].*)
solve [intuition].
Admitted.

Section s_flatPI.

Context `{PI : ProofIrrevelance}.

Lemma characterization : forall v:pset, flat v -> 
(forall x:Point, (v x)<->(pempty x))
\/ (exists y:Point, forall x:Point, ((v x) <-> ((psingleton y) x))) 
\/ (exists l:Line, forall x:Point, ((v x) <-> ((pline l) x)))
\/ (exists l1:Line, exists l2:Line, forall H:l1<>l2, forall H':Intersect l1 l2, forall x:Point, ((v x) <-> (pplane l1 l2 H H' x)))
\/(forall x:Point, (v x) <-> (pspace x)).
intros v Hflat.
unfold flat in Hflat.
elim (pset_decompose v).
(* empty set *)
intros Hempty.
left.
unfold pempty.
intros x; split.
apply Hempty.
intuition.
intros Helim; elim Helim.
(* singleton *)
intros Hsingleton.
right; left.
elim Hsingleton.
intros wit [Hwit1 Hwit2].
unfold psingleton.
exists wit.
intros x; split.
generalize Hwit1 Hwit2; case (eq_dec_u wit x).
solve [intuition].
intros Hwitx Hvwit Hforall Hvx0.
assert (~(x [==] wit)) by intuition.
elim (Hwit2 x H Hvx0).
intros.
apply v_subst with (A:=wit).
assumption.
assumption.

clear Helim; intros Hatleast2.
(* at least 2 elements *) 
elim Hatleast2; [intro Hequal2 | intro Hatleast3]; clear Hatleast2.
(* exactly 2 points *)
elim Hequal2; intros A H'; elim H'; clear H'.
intros B.
(* a line *)
intros [ HnAB [HvA [HvB Hv]]].
elim (a1_exist A B).
intros l [ HAl HBl ].
right;right;left.
exists l.
unfold pline.
intros x; elim (incid_dec x l).
intros Hxl.
split.
intuition.
intros HIncid.
eapply Hflat with (A:=A) (B:=B) (l:=l) ; assumption.
intros nIncid.
split.
intros Hvx.
case (eq_dec_u x A).
intro; new_subst; solve [intuition].
intros HxA.
case (eq_dec_u x B).
intro; new_subst; solve [intuition].
intros HxB.
elim (Hv x HxA HxB Hvx).
intros Hf; cut False; solve [intuition].
(* at least 3 points *)
elim Hatleast3; clear Hatleast3; 
  intros x Ha1; elim Ha1; clear Ha1; intros y Ha2; elim Ha2; clear Ha2; intros z (Hxy,(Hxz, (Hyz, (Hvx, (Hvy, Hvz))))).
elim (a1_exist x y).
intros l (Hlx,Hly).
elim (included_or_not v (fun p => Incid p l)).
(* every single point belongs to l *)
intros Hline.
right;right;left.
unfold pline.
exists l; intros a; split.
intuition.
eapply Hflat with (l:=l) (A:=x) (B:=y); intuition.
(* at least a plane : one point outside l *)
intros Hex; elim Hex; clear Hex; intros O (HvO,HnIncid).
elim (a1_exist x O).
intros l2 (Hxl2, HOl2).
assert (H'1 : (l<>l2)).
intro; subst; intuition.
assert (H'2:(Intersect l l2)).
unfold Intersect.
exists x; intuition.
(* everything in v is in the plane ! *)
elim (included_or_not v (pplane l l2 H'1 H'2)).
intros Hplane.
right;right;right;left.
exists l.
exists l2.
intros Ha Hb w; split.
intros Hvw.
rewrite (proof_irr (l<>l2) Ha H'1).
rewrite (proof_irr (Intersect l l2) Hb H'2).
intuition.
unfold pplane.
intros Hpplane.
elim Hpplane.
intros lw (Hwlw, Hex).
elim Hex; clear Hex; intros I HI; elim HI; intros J (HIJ,(HIlw, HJlw)).
eapply Hflat with (l:=lw) (A:=I) (B:=J); unfold Intersect_In in *;try (solve [intuition]).
eapply Hflat with (l:=l) (A:=x) (B:=y); (solve [intuition]).
eapply Hflat with (l:=l2) (A:=O) (B:=x); try (solve [intuition]).
intro; new_subst; solve [intuition].
(* at least one point is outside the plane *)
intros Hext; elim Hext; clear Hext; intros Q (HQ1,HQ2).
right;right;right;right.
intros w; unfold pspace; split.
trivial.
intros Htrue.
elim (eq_dec_u Q w).
intros; apply v_subst with (A:=Q); assumption.
intros HQw.
elim (a1_exist Q w); intros Qw (HQw1,HQw2). 
elim (plane_line l l2  Qw H'1 H'2).
intros P (HP1,HP2).
eapply Hflat with (l:=Qw) (A:=Q) (B:=P); try (solve [intuition]).
elim HP1.
intros m (Hm1, Hex).
elim Hex; clear Hex; intros I HI; elim HI; intros J (HIJ,(HIlw, HJlw)).
eapply Hflat with (l:=m) (A:=I) (B:=J); unfold Intersect_In in *; try (solve [intuition]).
eapply Hflat with (l:=l) (A:=x) (B:=y);  (solve [intuition]).
eapply Hflat with (l:=l2) (A:=O) (B:=x); try (solve [intuition]).
intro; new_subst; solve [intuition].
intro; new_subst; solve [intuition].
Qed.

End s_flatPI.

End s_flat.



(* Local Variables: *)
(* coq-prog-name: "coqtop" *)
(* coq-load-path: (("/Users/magaud/containers/theories" "Containers") ("/Users/magaud/galapagos/dev/trunk/ProjectiveGeometry/" "ProjectiveGeometry") ) *)
(* suffixes: .v *)
(* End: *)