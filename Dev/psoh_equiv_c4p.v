Require Export ProjectiveGeometry.Dev.psoh_equiv_copwa.

(*****************************************************************************)
(** Coplanar **)


Section s_psohEquivC4P.

Context `{PPS : PreProjectiveSpace}.
Context `{EP : EqDecidability Point}.
Context `{OP : OrderedType Point}.
Context `{EL : EqDecidabilityL Line}.
Context `{ELI : EqDecidabilityP Line Intersect}.

(*** Definition c4p ***)
Fixpoint contains_four_non_coplanar_points l :=
match l with
| nil => false
| a::r => if coplanar_with_all a (all_triples r) 
              then contains_four_non_coplanar_points r
              else true
end.

Lemma contains_1_cop : forall l, contains_four_non_coplanar_points l = true <-> 
exists A B C D, InA eq A l /\ InA eq B l /\ InA eq C l /\ InA eq D l /\ coplanar A B C D = false.
Proof.
induction l.
simpl;split; intros Hc.
discriminate.
destruct Hc as [A [B [C [D (HA,HBCD)]]]].
inversion HA.
simpl.
case_eq (coplanar_with_all a (all_triples l)); intros Hall.
split.
intros Hc.
apply IHl in Hc.
destruct Hc as [A [B [C [D (HA,(HB,(HC,(HD,HABC))))]]]].
exists A.
exists B.
exists C.
exists D.
repeat split.
apply InA_cons_tl; assumption.
apply InA_cons_tl; assumption.
apply InA_cons_tl; assumption.
apply InA_cons_tl; assumption.
assumption.
intros.
apply IHl.
destruct H as [A [B [C [D (HA,(HB,(HC,(HD,Hcop))))]]]].
destruct (eq_dec_u B C) as [HeqBC | HneqBC].
rewrite HeqBC in Hcop.
assert (T:= cop_2 A C D).
rewrite T in Hcop; inversion Hcop.
destruct (eq_dec_u A C) as [HeqAC | HneqAC].
rewrite HeqAC in Hcop.
assert (T:= cop_2 B C D).
rewrite cop_exchange1 in T.
rewrite T in Hcop; inversion Hcop.
destruct (eq_dec_u A B) as [HeqAB | HneqAB].
rewrite HeqAB in Hcop.
assert (T:= cop_1 B C D).
rewrite T in Hcop; inversion Hcop.
destruct (eq_dec_u A D) as [HeqAD | HneqAD].
rewrite HeqAD in Hcop.
assert (T:= cop_2 B D C).
rewrite cop_exchange1 in T.
rewrite cop_exchange2 in T.
rewrite T in Hcop; inversion Hcop.
destruct (eq_dec_u B D) as [HeqBD | HneqBD].
rewrite HeqBD in Hcop.
assert (T:= cop_2 A D C).
rewrite cop_exchange2 in T.
rewrite T in Hcop; inversion Hcop.
destruct (eq_dec_u C D) as [HeqCD | HneqCD].
rewrite HeqCD in Hcop.
assert (T:= cop_3 A B D).
rewrite T in Hcop; inversion Hcop.

assert (U:coplanar_with_all a (all_triples (a::l))=true).
simpl.
apply coplanar_app.
apply coplanar_with_all_map.
assumption.

inversion HA; subst.
assert (T:InA eq3 (B, C, D) (all_triples (a :: l)) 
\/ InA eq3 (B, D, C) (all_triples (a :: l))
\/ InA eq3 (C, B, D) (all_triples (a :: l))
\/ InA eq3 (C, D, B) (all_triples (a :: l))
\/ InA eq3 (D, B, C) (all_triples (a :: l))
\/ InA eq3 (D, C, B) (all_triples (a :: l))
).

apply (InA_eq_eq3_all_triples B C D (a::l) HB HC HD HneqBC HneqBD HneqCD).
destruct T as [T | T].
rewrite( cop_with_all_cop a (all_triples (a::l)) U B C D T) in Hcop.
inversion Hcop.
destruct T as [T | T].
rewrite cop_exchange2 in Hcop.
rewrite( cop_with_all_cop a (all_triples (a::l)) U B D C T) in Hcop.
inversion Hcop.
destruct T as [T | T].
rewrite cop_exchange3 in Hcop.
rewrite( cop_with_all_cop a (all_triples (a::l)) U C B D T) in Hcop.
inversion Hcop.
destruct T as [T | T].
rewrite cop_exchange3 in Hcop.
rewrite cop_exchange2 in Hcop.
rewrite( cop_with_all_cop a (all_triples (a::l)) U C D B T) in Hcop.
inversion Hcop.
destruct T as [T | T].
rewrite cop_exchange2 in Hcop.
rewrite cop_exchange3 in Hcop.
rewrite( cop_with_all_cop a (all_triples (a::l)) U D B C T) in Hcop.
inversion Hcop.
rewrite cop_exchange3 in Hcop.
rewrite cop_exchange2 in Hcop.
rewrite cop_exchange3 in Hcop.
rewrite( cop_with_all_cop a (all_triples (a::l)) U D C B T) in Hcop.
inversion Hcop.


inversion HB; subst.
assert (T:InA eq3 (A, C, D) (all_triples (a :: l)) 
\/ InA eq3 (A, D, C) (all_triples (a :: l))
\/ InA eq3 (C, A, D) (all_triples (a :: l))
\/ InA eq3 (C, D, A) (all_triples (a :: l))
\/ InA eq3 (D, A, C) (all_triples (a :: l))
\/ InA eq3 (D, C, A) (all_triples (a :: l))
).

apply (InA_eq_eq3_all_triples A C D (a::l) HA HC HD HneqAC HneqAD HneqCD).
destruct T as [T | T].
rewrite cop_exchange1 in Hcop.
rewrite( cop_with_all_cop a (all_triples (a::l)) U A C D T) in Hcop.
inversion Hcop.
destruct T as [T | T].
rewrite cop_exchange1 in Hcop.
rewrite cop_exchange2 in Hcop.
rewrite( cop_with_all_cop a (all_triples (a::l)) U A D C T) in Hcop.
inversion Hcop.
destruct T as [T | T].
rewrite cop_exchange1 in Hcop.
rewrite cop_exchange3 in Hcop.
rewrite( cop_with_all_cop a (all_triples (a::l)) U C A D T) in Hcop.
inversion Hcop.
destruct T as [T | T].
rewrite cop_exchange1 in Hcop.
rewrite cop_exchange3 in Hcop.
rewrite cop_exchange2 in Hcop.
rewrite( cop_with_all_cop a (all_triples (a::l)) U C D A T) in Hcop.
inversion Hcop.
destruct T as [T | T].
rewrite cop_exchange1 in Hcop.
rewrite cop_exchange2 in Hcop.
rewrite cop_exchange3 in Hcop.
rewrite( cop_with_all_cop a (all_triples (a::l)) U D A C T) in Hcop.
inversion Hcop.
rewrite cop_exchange1 in Hcop.
rewrite cop_exchange3 in Hcop.
rewrite cop_exchange2 in Hcop.
rewrite cop_exchange3 in Hcop.
rewrite( cop_with_all_cop a (all_triples (a::l)) U D C A T) in Hcop.
inversion Hcop.

inversion HC; subst.
assert (T:InA eq3 (A, B, D) (all_triples (a :: l)) 
\/ InA eq3 (A, D, B) (all_triples (a :: l))
\/ InA eq3 (B, A, D) (all_triples (a :: l))
\/ InA eq3 (B, D, A) (all_triples (a :: l))
\/ InA eq3 (D, A, B) (all_triples (a :: l))
\/ InA eq3 (D, B, A) (all_triples (a :: l))
).

apply (InA_eq_eq3_all_triples A B D (a::l) HA HB HD HneqAB HneqAD HneqBD).
destruct T as [T | T].
rewrite cop_exchange3 in Hcop.
rewrite cop_exchange1 in Hcop.
rewrite( cop_with_all_cop a (all_triples (a::l)) U A B D T) in Hcop.
inversion Hcop.
destruct T as [T | T].
rewrite cop_exchange3 in Hcop.
rewrite cop_exchange1 in Hcop.
rewrite cop_exchange2 in Hcop.
rewrite( cop_with_all_cop a (all_triples (a::l)) U A D B T) in Hcop.
inversion Hcop.
destruct T as [T | T].
rewrite cop_exchange3 in Hcop.
rewrite cop_exchange1 in Hcop.
rewrite cop_exchange3 in Hcop.
rewrite( cop_with_all_cop a (all_triples (a::l)) U B A D T) in Hcop.
inversion Hcop.
destruct T as [T | T].
rewrite cop_exchange3 in Hcop.
rewrite cop_exchange1 in Hcop.
rewrite cop_exchange3 in Hcop.
rewrite cop_exchange2 in Hcop.
rewrite( cop_with_all_cop a (all_triples (a::l)) U B D A T) in Hcop.
inversion Hcop.
destruct T as [T | T].
rewrite cop_exchange3 in Hcop.
rewrite cop_exchange1 in Hcop.
rewrite cop_exchange2 in Hcop.
rewrite cop_exchange3 in Hcop.
rewrite( cop_with_all_cop a (all_triples (a::l)) U D A B T) in Hcop.
inversion Hcop.
rewrite cop_exchange3 in Hcop.
rewrite cop_exchange1 in Hcop.
rewrite cop_exchange3 in Hcop.
rewrite cop_exchange2 in Hcop.
rewrite cop_exchange3 in Hcop.
rewrite( cop_with_all_cop a (all_triples (a::l)) U D B A T) in Hcop.
inversion Hcop.

inversion HD; subst.
assert (T:InA eq3 (A, B, C) (all_triples (a :: l)) 
\/ InA eq3 (A, C, B) (all_triples (a :: l))
\/ InA eq3 (B, A, C) (all_triples (a :: l))
\/ InA eq3 (B, C, A) (all_triples (a :: l))
\/ InA eq3 (C, A, B) (all_triples (a :: l))
\/ InA eq3 (C, B, A) (all_triples (a :: l))
).

apply (InA_eq_eq3_all_triples A B C (a::l) HA HB HC HneqAB HneqAC HneqBC).
destruct T as [T | T].
rewrite cop_exchange2 in Hcop.
rewrite cop_exchange3 in Hcop.
rewrite cop_exchange1 in Hcop.
rewrite( cop_with_all_cop a (all_triples (a::l)) U A B C T) in Hcop.
inversion Hcop.
destruct T as [T | T].
rewrite cop_exchange2 in Hcop.
rewrite cop_exchange3 in Hcop.
rewrite cop_exchange1 in Hcop.
rewrite cop_exchange2 in Hcop.
rewrite( cop_with_all_cop a (all_triples (a::l)) U A C B T) in Hcop.
inversion Hcop.
destruct T as [T | T].
rewrite cop_exchange2 in Hcop.
rewrite cop_exchange3 in Hcop.
rewrite cop_exchange1 in Hcop.
rewrite cop_exchange3 in Hcop.
rewrite( cop_with_all_cop a (all_triples (a::l)) U B A C T) in Hcop.
inversion Hcop.
destruct T as [T | T].
rewrite cop_exchange2 in Hcop.
rewrite cop_exchange3 in Hcop.
rewrite cop_exchange1 in Hcop.
rewrite cop_exchange3 in Hcop.
rewrite cop_exchange2 in Hcop.
rewrite( cop_with_all_cop a (all_triples (a::l)) U B C A T) in Hcop.
inversion Hcop.
destruct T as [T | T].
rewrite cop_exchange2 in Hcop.
rewrite cop_exchange3 in Hcop.
rewrite cop_exchange1 in Hcop.
rewrite cop_exchange2 in Hcop.
rewrite cop_exchange3 in Hcop.
rewrite( cop_with_all_cop a (all_triples (a::l)) U C A B T) in Hcop.
inversion Hcop.
rewrite cop_exchange2 in Hcop.
rewrite cop_exchange3 in Hcop.
rewrite cop_exchange1 in Hcop.
rewrite cop_exchange3 in Hcop.
rewrite cop_exchange2 in Hcop.
rewrite cop_exchange3 in Hcop.
rewrite( cop_with_all_cop a (all_triples (a::l)) U C B A T) in Hcop.
inversion Hcop.

exists A.
exists B.
exists C.
exists D.
repeat split; assumption.

(**)
intros.
generalize (contains_1_aux a (all_triples l)); intros Hyp.
split.
intros.
apply Hyp in Hall; clear Hyp.
exists a.
destruct Hall as [B [C [D (HBCD,Hcop)]]].
exists B.
exists C.
exists D.
split.
apply InA_cons_hd; reflexivity.
destruct (InA_eq3_eq_all_triples B C D l HBCD).
split.
apply InA_cons_tl; assumption.
split.
destruct H1.
apply InA_cons_tl; assumption.
split.
destruct H1.
apply InA_cons_tl; assumption.
assumption.
solve [intuition].
Qed.

Lemma contains_2_cop : forall l, contains_four_non_coplanar_points l = false <-> 
(forall A B C D, InA eq A l -> InA eq B l -> InA eq C l -> InA eq D l -> coplanar A B C D = true).
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
case_eq (coplanar_with_all a (all_triples l)).
intros.
inversion H0; subst.
inversion H1; subst.
apply cop_1.
inversion H2; subst.
rewrite cop_exchange3. 
apply cop_1.
inversion H3; subst.
rewrite cop_exchange2. 
rewrite cop_exchange3.
apply cop_1.


case_eq (eq_dec_u B C).
intros.
rewrite e.
apply cop_2.
intros.
case_eq (eq_dec_u B D).
intros.
rewrite e.
rewrite cop_exchange3.
apply cop_3.
intros.
case_eq (eq_dec_u C D).
intros.
rewrite e.
apply cop_3.
intros.
assert(HH := cop_aux a B C D (all_triples l) H4).
apply HH.
apply InA_eq_eq3_all_triples; assumption.

inversion H1;subst.
inversion H2;subst.
apply cop_2.
inversion H3;subst.
rewrite cop_exchange2.
apply cop_2.

case_eq (eq_dec_u A C).
intros.
rewrite e.
rewrite cop_exchange1.
apply cop_2.
intros.
case_eq (eq_dec_u A D).
intros.
rewrite e.
rewrite cop_exchange2.
rewrite cop_exchange3.
apply cop_1.
intros.
case_eq (eq_dec_u C D).
intros.
rewrite e.
apply cop_3.
intros.
rewrite cop_exchange1.
assert(HH := cop_aux a A C D (all_triples l) H4).
apply HH.
apply InA_eq_eq3_all_triples; assumption.

inversion H2; subst.
inversion H3; subst.
apply cop_3.

case_eq (eq_dec_u A B).
intros.
rewrite e.
apply cop_1.
intros.
case_eq (eq_dec_u A D).
intros.
rewrite e.
rewrite cop_exchange1.
rewrite cop_exchange3.
apply cop_3.
intros.
case_eq (eq_dec_u B D).
intros.
rewrite e.
rewrite cop_exchange3.
apply cop_3.
intros.
rewrite cop_exchange3.
rewrite cop_exchange1.
assert(HH := cop_aux a A B D (all_triples l) H4).
apply HH.
apply InA_eq_eq3_all_triples; assumption.

inversion H3;subst.

case_eq (eq_dec_u A B).
intros.
rewrite e.
apply cop_1.
intros.
case_eq (eq_dec_u A C).
intros.
rewrite e.
rewrite cop_exchange1.
apply cop_2.
intros.
case_eq (eq_dec_u B C).
intros.
rewrite e.
apply cop_2.
intros.
rewrite cop_exchange2.
rewrite cop_exchange3.
rewrite cop_exchange1.
assert(HH := cop_aux a A B C (all_triples l) H4).
apply HH.
apply InA_eq_eq3_all_triples; assumption.


destruct IHl as [IHl1 IHl2].
rewrite H4 in H.
generalize (IHl1 H); intros Hr; clear IHl1 IHl2.
apply Hr; assumption.
intros Hrew; rewrite Hrew in H.
inversion H.
(* <- *)
simpl.
case_eq (coplanar_with_all a (all_triples l)).
intros; apply IHl.
intros.
apply H.
apply InA_cons_tl; assumption.
apply InA_cons_tl; assumption.
apply InA_cons_tl; assumption.
apply InA_cons_tl; assumption.
intros.
apply False_ind. eapply forall_InA_coplanar_with_all; eassumption.
Qed.

Lemma matroid3_aux1_cop : forall l, forall a,
coplanar_with_all a (all_triples (l)) = true ->
contains_four_non_coplanar_points (l) = false.
Proof.
intros.
induction l.
simpl.
reflexivity.
simpl.
case_eq (coplanar_with_all a0 (all_triples l)).
intros.
apply IHl.
assert (HH := matroid3_aux0_cop l a a0 H).
assumption.
intros.
assert (HH := matroid3_aux0_cop_bis l a a0 H).
rewrite HH in H0.
inversion H0.
Qed.

Lemma contains_four_non_coplanar_points_sublist_aux :
forall l, forall a,
contains_four_non_coplanar_points l = true ->
contains_four_non_coplanar_points (a :: l) = true.
Proof.
intro.
induction l.
- intros.
  simpl in *.
  discriminate.
- intros.
  simpl.
  case_eq (coplanar_with_all a0
      (flatten (Point * Point * Point)
         (List.map (fun y : Point => map_monotonic (fun x : Point => (a, x, y)) l) l) ++
       all_triples l)).
  intro.
  simpl in H.
  apply H.
  intro.
  reflexivity.
Qed.

Lemma contains_four_non_coplanar_points_sublist :
forall l m, inclA eq l m ->
(contains_four_non_coplanar_points l = true) ->
(contains_four_non_coplanar_points m = true).
Proof.
intros l m Hincl Hc.
apply contains_1_cop in Hc.
apply contains_1_cop.
destruct Hc as [A [B [C [D (HA,(HB,(HC,(HD,Hcol))))]]]].
exists A; exists B; exists C; exists D.
split.
apply Hincl; assumption.
split.
apply Hincl; assumption.
split.
apply Hincl; assumption.
split.
apply Hincl; assumption.
assumption.
Qed.

Lemma contains_four_to_three_aux :
forall l, forall a,
contains_four_non_coplanar_points (a :: a :: l) = true ->
contains_four_non_coplanar_points (a :: l) = true.
Proof.
intros.
case_eq l.
intros.
rewrite H0 in H.
inversion H.
intros.
rewrite <- H0.
assert(inclA eq (a :: a :: l) (a :: l)).
unfold inclA.
intros.
inversion H1.
rewrite H3.
intuition.
assumption.
assert( HH := contains_four_non_coplanar_points_sublist (a :: a :: l) (a :: l) H1 H).
assumption.
Qed.

Lemma contains_four_to_three_aux' :
forall l,
contains_four_non_coplanar_points l = true ->
contains_three_non_collinear_points l = true.
Proof.
induction l.
simpl.
intros.
inversion H.
intros.
apply contains_1_cop in H.
apply contains_1.
destruct H.
destruct H.
destruct H.
destruct H.
exists x. 
exists x0.
exists x1.
destruct H.
destruct H0.
destruct H1.
split.
assumption.
split.
assumption.
split.
assumption.
destruct H2.
generalize H3.
unfold coplanar.
case_eq (eq_dec_u x x0).
intros.
inversion H5.
case_eq (eq_dec_u x1 x2).
intros.
inversion H6.
destruct (a1_exist x x0).
destruct (a1_exist x1 x2).
simpl.
case_eq (eq_dec_l x3 x4).
intros.
inversion H7.
case_eq (eq_dec_p x3 x4).
intros.
inversion H8.
intros.
unfold collinear.
case_eq (eq_dec_u x x0).
intros.
contradiction.
destruct(a1_exist x x0).
simpl.
intros.
destruct (incid_dec x1 x5).
destruct a0.
destruct a2.
assert( HH0 := uniqueness x x0 x3 x5 H10 H11 H12 H13).
destruct HH0.
contradiction.
clear H4.
rewrite H14 in *.
assert( HH0 : Intersect x5 x4).
unfold Intersect.
exists x1.
destruct a1.
split.
assumption.
assumption.
contradiction.
reflexivity.
Qed.

Global Instance contains_four_morph : Proper (@equivlistA Point eq ==> (@Logic.eq bool)) contains_four_non_coplanar_points.
Proof.
repeat red;intros.
case_eq (contains_four_non_coplanar_points x);
  case_eq (contains_four_non_coplanar_points y).
solve [trivial].
intros Hp1 Hp2.
apply contains_1_cop in Hp2.
generalize (contains_2_cop y) ; intros Hg; destruct Hg as[Hg1 Hg2].
generalize (Hg1 Hp1); intros Hq; clear Hg1 Hg2.
destruct Hp2 as [X [Y [Z [W HXYZW]]]].
rewrite Hq in HXYZW.
solve [intuition].
rewrite <- H; solve [intuition].
rewrite <- H; solve [intuition].
rewrite <- H; solve [intuition].
rewrite <- H; solve [intuition].

intros Hp1 Hp2.
generalize (contains_1_cop y); intros Hg; destruct Hg as [Hg1 Hg2].
generalize (Hg1 Hp1); intros Hq; clear Hg1 Hg2.
generalize (contains_2_cop x); intros Hh; destruct Hh as [Hh1 Hh2].
generalize (Hh1 Hp2); intros Hr; clear Hh1 Hh2.
destruct Hq as [X [Y [Z [W (HX,(HY,(HZ,(HW,HXYZ))))]]]].
rewrite <- H in HX,HY,HZ,HW.
rewrite Hr in HXYZ.
inversion HXYZ.
assumption.
assumption.
assumption.
assumption.
solve [trivial].
Qed.

Lemma contains_four_to_three_aux2 :
forall l, forall x,
contains_four_non_coplanar_points (x :: l) = true ->
contains_three_non_collinear_points l = true.
Proof.
intros.
induction l.
- intros.
  simpl in *.
  discriminate.
- intros.
  induction l.
  simpl in *.
  inversion H.
  clear IHl0.
  apply contains_1_cop in H.
  destruct H.
  destruct H.
  destruct H.
  destruct H.
  destruct H.
  destruct H0.
  destruct H1.
  destruct H2.
  apply contains_1.
  inversion H;subst.
  inversion H0;subst.
  assert( HH := cop_1 x x2 x3).
  rewrite HH in H3.
  inversion H3.
  inversion H1;subst.
  rewrite cop_exchange3 in H3.
  assert( HH := cop_1 x x1 x3).
  rewrite HH in H3.
  inversion H3.
  inversion H2;subst.
  rewrite cop_exchange2 in H3.
  rewrite cop_exchange3 in H3.
  assert( HH := cop_1 x x1 x2).
  rewrite HH in H3.
  inversion H3.
  case_eq (collinear x1 x2 x3).
  intros.
  assert( HH := col_to_cop x1 x2 x3 x H4).
  rewrite cop_exchange2 in HH.
  rewrite cop_exchange3 in HH.
  rewrite cop_exchange1 in HH.
  rewrite HH in H3.
  inversion H3.
  intros.
  exists x1.
  exists x2.
  exists x3.
  split.
  assumption.
  split.  
  assumption.
  split.
  assumption.
  assumption.
  inversion H0;subst.
  inversion H1;subst.
  assert( HH0 := cop_2 x0 x x3).
  rewrite HH0 in H3.
  inversion H3.
  inversion H2;subst.
  rewrite cop_exchange2 in H3.
  assert( HH0 := cop_2 x0 x x2).
  rewrite HH0 in H3.
  inversion H3.
  case_eq (collinear x0 x2 x3).
  intros.
  assert( HH := col_to_cop x0 x2 x3 x H4).
  rewrite cop_exchange2 in HH.
  rewrite cop_exchange3 in HH.
  rewrite HH in H3.
  inversion H3.
  intros.
  exists x0.
  exists x2.
  exists x3.
  split.
  assumption.
  split.  
  assumption.
  split.
  assumption.
  assumption.
  inversion H1;subst.
  inversion H2;subst.
  assert( HH := cop_3 x0 x1 x).
  rewrite HH in H3.
  inversion H3.
  case_eq (collinear x0 x1 x3).
  intros.
  assert( HH := col_to_cop x0 x1 x3 x H4).
  rewrite cop_exchange2 in HH.
  rewrite HH in H3.
  inversion H3.
  intros.
  exists x0.
  exists x1.
  exists x3.
  split.
  assumption.
  split.  
  assumption.
  split.
  assumption.
  assumption.
  case_eq (collinear x0 x1 x2).
  intros.
  assert( HH := col_to_cop x0 x1 x2 x3 H4).
  rewrite HH in H3.
  inversion H3.
  intros.
  exists x0.
  exists x1.
  exists x2.
  split.
  assumption.
  split.  
  assumption.
  split.
  assumption.
  assumption.
Qed.

Lemma contains_four_to_three :
forall l,forall x,
contains_four_non_coplanar_points (l++(x::nil)) = true ->
contains_three_non_collinear_points l = true.
Proof.
intros.
assert( equivlistA eq (l ++ x :: nil) (x :: l)).
unfold equivlistA.
intros.
split.
intros.
my_inA.
intros.
my_inA.
rewrite H0 in H.
apply contains_four_to_three_aux2 with (x:=x).
assumption.
Qed.

End s_psohEquivC4P.
