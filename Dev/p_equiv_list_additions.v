Require Export ProjectiveGeometry.Dev.projective_axioms.
Require Export Containers.SetListInstance.
Require Export Containers.SetList.

Module FL := SetList.

Export FL.

(*****************************************************************************)
(** SetoidList additions **)


Ltac simplgen H := simpl in H;generalize H.


Section s_pEquivListAdditions_1.

Context `{PS : ProjectiveStructure}.
Context `{EP : EqDecidability Point}.
Context `{OP : OrderedType Point}.

Global Instance eq_equiv : Equivalence (@eq Point).
Proof.
repeat split.
unfold Symmetric;intros;rewrite H;reflexivity.
unfold Transitive;intros;rewrite H;rewrite H0;reflexivity.
Qed.

Lemma eq_reverse : forall a b, a[==]b -> b[==]a.
Proof.
intuition.
Qed.

End s_pEquivListAdditions_1.


Ltac my_subst :=
  subst;
  repeat match goal with
  |[H : eq_dec _ _ = _ _ |- _] => clear H
  |[H : ?X [==] ?Y |- _] => rewrite H in *;clear H;intuition
  end.

Ltac my_inA :=
  intuition;unfold equivlistA in *; unfold inclA in *;
  repeat match goal with
  |[H : _ |- _] => progress intros
  |[H : _ |- _] => progress intro
  |[H : _ |- _] => progress intuition
  |[H : _ |- _] => progress my_subst
  |[H : _ |- Equivalence eq] => apply eq_equiv
  |[H : InA eq _ _ |- InA eq _ ( _ ++ _ )] => apply InA_app_iff
  |[H : InA eq _ ( _ ++ _ ) |- _] => apply InA_app_iff in H
  |[H : _ |- _] => split;intuition
  |[H : InA eq _ ( ?P :: ?Q ) |- _] => inversion H; clear H
  |[H : InA eq _ nil |- _] => inversion H
  |[H : _ = nil |- _] => inversion H
  |[H : InA eq ?P ( ?P :: ?Q ) -> _ |- _] => let T:=fresh in
                                            assert(T : InA eq P (P :: Q)) by (intuition)
  |[H : InA eq ?P ( ?Q :: ?P :: ?Z ) -> _ |- _] => let T:=fresh in
                                            assert(T : InA eq P (Q :: P :: Z)) by (apply InA_cons_tl;intuition)
  end.

Ltac my_inAS :=
  intuition;unfold inclA in *;unfold equivlistA in *;
  repeat match goal with
  |[H : _ |- _] => progress intros
  |[H : _ |- _] => progress intro
  |[H : _ |- _] => progress intuition
  |[H : _ |- _] => split;intuition
  |[H : InA eq _ (?P ::  _ ) |- _] => inversion H;clear H
  |[H : _ = _ |- _] => rewrite <-H
  |[H : InA eq _ nil |- _] => inversion H
         | [H : InA eq ?P ( ?Q :: ?R ) -> _ |- _] => let T:=fresh in
                                            assert(T : InA eq P (Q :: R)) by (my_inAS);
                                            generalize (H T);clear H;clear T;intro
  end.


Section s_pEquivListAdditions_2.

Context `{PS : ProjectiveStructure}.
Context `{EP : EqDecidability Point}.
Context `{OP : OrderedType Point}.

Lemma inclA_aux4_bis : 
forall a l m, inclA (@eq Point) l m -> inclA eq l (a :: m).
Proof.
my_inAS.
Qed.

Lemma inclA_aux5 :
forall a l m, inclA (@eq Point) l m -> inclA eq (a :: l) (a :: m).
Proof.
my_inA.
Qed.

Lemma list_concat_reverse : forall l m, equivlistA (@eq Point) (l ++ m) (m ++ l).
Proof.
my_inA.
Qed.

(*** Definition Inb ***)
Fixpoint Inb (a:Point) (l:list Point) {struct l} : bool :=
    match l with
      | nil => false
      | b :: m => if (eq_dec_u b a) then true else Inb a m
    end.

Lemma Inb_aux1 :
forall a l, Inb a l = true -> InA eq a l.
Proof.
my_inA;induction l;my_inA.
- inversion H.
- simplgen H;case_eq(eq_dec_u a0 a);my_inA.
Qed.

Lemma Inb_aux3 :
forall a l, Inb a l = false -> ~InA eq a l.
Proof.
my_inA;induction l;my_inA.
- simplgen H;case_eq(eq_dec_u a0 a0);my_inA.
- simplgen H;case_eq(eq_dec_u a0 a);my_inA.
Qed.

Global Instance Inb_morph : Proper (eq ==> equivlistA eq ==> Logic.eq) Inb.
Proof.
repeat red;my_inA.
case_eq (Inb y x0); case_eq (Inb y y0).
- my_inA.
- my_inA;assert(HH0 := Inb_aux3 y y0 H);assert(HH1 := Inb_aux1 y x0 H1);
assert(HH2 := H0 y);my_inA.
- my_inA;assert(HH0 := Inb_aux1 y y0 H);assert(HH1 := Inb_aux3 y x0 H1);
assert(HH2 := H0 y);my_inA.
- my_inA.
Qed.

(*** Definition list_inter ***)
Definition list_inter l1 l2 := filter (fun x : Point => Inb x l2) l1.

Lemma list_inter_split :
forall a l m, InA eq a (list_inter l m) -> InA eq a m -> InA eq a l.
Proof.
my_inA;induction l;my_inA.
simplgen H;unfold list_inter;simpl;case_eq(Inb a0 m);my_inA.
Qed.

Lemma list_inter_split_bis :
forall a l m, InA eq a (list_inter l m) -> InA eq a l /\ InA eq a m.
Proof.
intros.
my_inA;induction l;my_inA.
- simplgen H;unfold list_inter;simpl;case_eq(Inb a0 m);my_inA.
- inversion H.
- simplgen H;unfold list_inter;simpl;case_eq(Inb a0 m);my_inA;apply Inb_aux1;my_inA.
Qed.

Lemma list_inter_split_reverse :
forall a l m, InA eq a m -> InA eq a l -> InA eq a (list_inter l m).
Proof.
my_inA;induction l;my_inA.
- unfold list_inter;simpl;case_eq(Inb a0 m);my_inA;assert(HH := Inb_aux3 a0 m H0);my_inA.
- unfold list_inter;simpl;case_eq(Inb a0 m);my_inA.
Qed.

End s_pEquivListAdditions_2.


Ltac solve_equivlistA := first [assumption |  apply InA_cons_hd;reflexivity | apply InA_cons_tl ; solve_equivlistA].

Ltac inv_unifA :=
  unfold inclA in *; try split; intros;
  repeat match goal with 
         | [H : InA eq _ (?P ::  _ ) |- _] => inversion H;clear H
         | [H: _ = _ |- _] => rewrite <- H in *;try solve [contradiction|apply eq_sym in H;contradiction];clear H
         | [H : InA eq _ nil |- _] => inversion H
         | [H : InA eq _ (?L++?M) |- _] => apply InA_app_iff in H; destruct H
         | [H :_ |- InA eq _ (?L++?M) ] => apply InA_app_iff
         | [H : InA eq _ (list_inter ?L ?M) |- _] => apply list_inter_split_bis in H; destruct H
         | [H : _ |- InA eq _ (list_inter ?L ?M)] => apply list_inter_split_reverse
         | [H : InA eq ?P ( ?Q :: ?R ) -> _ |- _] => let T:=fresh in
                                            assert(T : InA eq P (Q :: R)) by (solve_equivlistA);
                                            generalize (H T);clear H;clear T;intro
         end.

Ltac my_inAO := solve[inv_unifA ; solve_equivlistA].


Section s_pEquivListAdditions_3.

Context `{PS : ProjectiveStructure}.
Context `{EP : EqDecidability Point}.
Context `{OP : OrderedType Point}.

Lemma inclA_inter :
forall l m, inclA eq (list_inter l m) l.
Proof.
my_inAO.
Qed.

Lemma inclA_inter_bis :
forall l m, inclA eq (list_inter l m) m.
Proof.
my_inAO.
Qed.

Lemma list_inter_reverse : forall l m, equivlistA eq (list_inter l m) (list_inter m l).
Proof.
my_inAO.
Qed.

Global Instance list_inter_morph: Proper (equivlistA eq ==> equivlistA eq ==> equivlistA eq) list_inter.
Proof.
repeat red.
my_inA;assert(HH := H x1);assert(HH0 := H0 x1);my_inA.
- apply list_inter_split_reverse;apply list_inter_split_bis in H1;my_inA.
- apply list_inter_split_reverse;apply list_inter_split_bis in H1;my_inA.
Qed.

Lemma list_inter_rewrite : forall l m, filter (fun x : Point => Inb x m) l = list_inter l m.
Proof.
intros.
unfold list_inter.
reflexivity.
Qed.

End s_pEquivListAdditions_3.

