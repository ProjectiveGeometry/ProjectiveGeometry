Require Export ProjectiveGeometry.Dev.projective_plane_axioms.

(**  PG(2,7). **)

(** To show that our axiom system is consistent we build a finite model. **)

Section s_fanoPlaneModelPG27Generated.

(** We can not use directly the inductive type for a technical reason related to Coq's implementation. **)

Inductive ind_Point : Set := p0 | p1 | p2 | p3 | p4 | p5 | p6 | p7 | p8 | p9 | p10 | p11 | p12 | p13 | p14 | p15 | p16 | p17 | p18 | p19 | p20 | p21 | p22 | p23 | p24 | p25 | p26 | p27 | p28 | p29 | p30 | p31 | p32 | p33 | p34 | p35 | p36 | p37 | p38 | p39 | p40 | p41 | p42 | p43 | p44 | p45 | p46 | p47 | p48 | p49 | p50 | p51 | p52 | p53 | p54 | p55 | p56.
 
Inductive ind_line : Set := l0 | l1 | l2 | l3 | l4 | l5 | l6 | l7 | l8 | l9 | l10 | l11 | l12 | l13 | l14 | l15 | l16 | l17 | l18 | l19 | l20 | l21 | l22 | l23 | l24 | l25 | l26 | l27 | l28 | l29 | l30 | l31 | l32 | l33 | l34 | l35 | l36 | l37 | l38 | l39 | l40 | l41 | l42 | l43 | l44 | l45 | l46 | l47 | l48 | l49 | l50 | l51 | l52 | l53 | l54 | l55 | l56.
 
Definition Point : Set := ind_Point.
Definition Line : Set := ind_line.
 
Definition Incid_bool : Point -> Line -> bool := fun P l =>
 match P with
| p0 =>
	match l with
	| l4| l13| l20| l24| l43| l53| l55| l56=> true
	| _ => false
	end
| p1 =>
	match l with
	| l0| l5| l14| l21| l25| l44| l54| l56=> true
	| _ => false
	end
| p2 =>
	match l with
	| l0| l1| l6| l15| l22| l26| l45| l55=> true
	| _ => false
	end
| p3 =>
	match l with
	| l1| l2| l7| l16| l23| l27| l46| l56=> true
	| _ => false
	end
| p4 =>
	match l with
	| l0| l2| l3| l8| l17| l24| l28| l47=> true
	| _ => false
	end
| p5 =>
	match l with
	| l1| l3| l4| l9| l18| l25| l29| l48=> true
	| _ => false
	end
| p6 =>
	match l with
	| l2| l4| l5| l10| l19| l26| l30| l49=> true
	| _ => false
	end
| p7 =>
	match l with
	| l3| l5| l6| l11| l20| l27| l31| l50=> true
	| _ => false
	end
| p8 =>
	match l with
	| l4| l6| l7| l12| l21| l28| l32| l51=> true
	| _ => false
	end
| p9 =>
	match l with
	| l5| l7| l8| l13| l22| l29| l33| l52=> true
	| _ => false
	end
| p10 =>
	match l with
	| l6| l8| l9| l14| l23| l30| l34| l53=> true
	| _ => false
	end
| p11 =>
	match l with
	| l7| l9| l10| l15| l24| l31| l35| l54=> true
	| _ => false
	end
| p12 =>
	match l with
	| l8| l10| l11| l16| l25| l32| l36| l55=> true
	| _ => false
	end
| p13 =>
	match l with
	| l9| l11| l12| l17| l26| l33| l37| l56=> true
	| _ => false
	end
| p14 =>
	match l with
	| l0| l10| l12| l13| l18| l27| l34| l38=> true
	| _ => false
	end
| p15 =>
	match l with
	| l1| l11| l13| l14| l19| l28| l35| l39=> true
	| _ => false
	end
| p16 =>
	match l with
	| l2| l12| l14| l15| l20| l29| l36| l40=> true
	| _ => false
	end
| p17 =>
	match l with
	| l3| l13| l15| l16| l21| l30| l37| l41=> true
	| _ => false
	end
| p18 =>
	match l with
	| l4| l14| l16| l17| l22| l31| l38| l42=> true
	| _ => false
	end
| p19 =>
	match l with
	| l5| l15| l17| l18| l23| l32| l39| l43=> true
	| _ => false
	end
| p20 =>
	match l with
	| l6| l16| l18| l19| l24| l33| l40| l44=> true
	| _ => false
	end
| p21 =>
	match l with
	| l7| l17| l19| l20| l25| l34| l41| l45=> true
	| _ => false
	end
| p22 =>
	match l with
	| l8| l18| l20| l21| l26| l35| l42| l46=> true
	| _ => false
	end
| p23 =>
	match l with
	| l9| l19| l21| l22| l27| l36| l43| l47=> true
	| _ => false
	end
| p24 =>
	match l with
	| l10| l20| l22| l23| l28| l37| l44| l48=> true
	| _ => false
	end
| p25 =>
	match l with
	| l11| l21| l23| l24| l29| l38| l45| l49=> true
	| _ => false
	end
| p26 =>
	match l with
	| l12| l22| l24| l25| l30| l39| l46| l50=> true
	| _ => false
	end
| p27 =>
	match l with
	| l13| l23| l25| l26| l31| l40| l47| l51=> true
	| _ => false
	end
| p28 =>
	match l with
	| l14| l24| l26| l27| l32| l41| l48| l52=> true
	| _ => false
	end
| p29 =>
	match l with
	| l15| l25| l27| l28| l33| l42| l49| l53=> true
	| _ => false
	end
| p30 =>
	match l with
	| l16| l26| l28| l29| l34| l43| l50| l54=> true
	| _ => false
	end
| p31 =>
	match l with
	| l17| l27| l29| l30| l35| l44| l51| l55=> true
	| _ => false
	end
| p32 =>
	match l with
	| l18| l28| l30| l31| l36| l45| l52| l56=> true
	| _ => false
	end
| p33 =>
	match l with
	| l0| l19| l29| l31| l32| l37| l46| l53=> true
	| _ => false
	end
| p34 =>
	match l with
	| l1| l20| l30| l32| l33| l38| l47| l54=> true
	| _ => false
	end
| p35 =>
	match l with
	| l2| l21| l31| l33| l34| l39| l48| l55=> true
	| _ => false
	end
| p36 =>
	match l with
	| l3| l22| l32| l34| l35| l40| l49| l56=> true
	| _ => false
	end
| p37 =>
	match l with
	| l0| l4| l23| l33| l35| l36| l41| l50=> true
	| _ => false
	end
| p38 =>
	match l with
	| l1| l5| l24| l34| l36| l37| l42| l51=> true
	| _ => false
	end
| p39 =>
	match l with
	| l2| l6| l25| l35| l37| l38| l43| l52=> true
	| _ => false
	end
| p40 =>
	match l with
	| l3| l7| l26| l36| l38| l39| l44| l53=> true
	| _ => false
	end
| p41 =>
	match l with
	| l4| l8| l27| l37| l39| l40| l45| l54=> true
	| _ => false
	end
| p42 =>
	match l with
	| l5| l9| l28| l38| l40| l41| l46| l55=> true
	| _ => false
	end
| p43 =>
	match l with
	| l6| l10| l29| l39| l41| l42| l47| l56=> true
	| _ => false
	end
| p44 =>
	match l with
	| l0| l7| l11| l30| l40| l42| l43| l48=> true
	| _ => false
	end
| p45 =>
	match l with
	| l1| l8| l12| l31| l41| l43| l44| l49=> true
	| _ => false
	end
| p46 =>
	match l with
	| l2| l9| l13| l32| l42| l44| l45| l50=> true
	| _ => false
	end
| p47 =>
	match l with
	| l3| l10| l14| l33| l43| l45| l46| l51=> true
	| _ => false
	end
| p48 =>
	match l with
	| l4| l11| l15| l34| l44| l46| l47| l52=> true
	| _ => false
	end
| p49 =>
	match l with
	| l5| l12| l16| l35| l45| l47| l48| l53=> true
	| _ => false
	end
| p50 =>
	match l with
	| l6| l13| l17| l36| l46| l48| l49| l54=> true
	| _ => false
	end
| p51 =>
	match l with
	| l7| l14| l18| l37| l47| l49| l50| l55=> true
	| _ => false
	end
| p52 =>
	match l with
	| l8| l15| l19| l38| l48| l50| l51| l56=> true
	| _ => false
	end
| p53 =>
	match l with
	| l0| l9| l16| l20| l39| l49| l51| l52=> true
	| _ => false
	end
| p54 =>
	match l with
	| l1| l10| l17| l21| l40| l50| l52| l53=> true
	| _ => false
	end
| p55 =>
	match l with
	| l2| l11| l18| l22| l41| l51| l53| l54=> true
	| _ => false
	end
| p56 =>
	match l with
	| l3| l12| l19| l23| l42| l52| l54| l55=> true
	| _ => false
	end
end.

Definition Incid : Point -> Line -> Prop := fun P L => (Incid_bool P L = true).

Hint Unfold Incid Incid_bool.

Lemma incid_dec : forall (A:Point) (l:Line), {Incid A l} + {~Incid A l}.
Proof.
intros.
unfold Incid.
elim l;elim A;unfold Incid_bool;simpl;auto;right;discriminate.
Qed.

Ltac solve_ex L := solve [exists L;auto].

(** A tactic which tries all possible lines **)
Ltac solve_ex_l := first [
        solve_ex l0
     |  solve_ex l1
     |  solve_ex l2
     |  solve_ex l3
     |  solve_ex l4
     |  solve_ex l5
     |  solve_ex l6
     |  solve_ex l7
     |  solve_ex l8
     |  solve_ex l9
     |  solve_ex l10
     |  solve_ex l11
     |  solve_ex l12
     |  solve_ex l13
     |  solve_ex l14
     |  solve_ex l15
     |  solve_ex l16
     |  solve_ex l17
     |  solve_ex l18
     |  solve_ex l19
     |  solve_ex l20
     |  solve_ex l21
     |  solve_ex l22
     |  solve_ex l23
     |  solve_ex l24
     |  solve_ex l25
     |  solve_ex l26
     |  solve_ex l27
     |  solve_ex l28
     |  solve_ex l29
     |  solve_ex l30
     |  solve_ex l31
     |  solve_ex l32
     |  solve_ex l33
     |  solve_ex l34
     |  solve_ex l35
     |  solve_ex l36
     |  solve_ex l37
     |  solve_ex l38
     |  solve_ex l39
     |  solve_ex l40
     |  solve_ex l41
     |  solve_ex l42
     |  solve_ex l43
     |  solve_ex l44
     |  solve_ex l45
     |  solve_ex l46
     |  solve_ex l47
     |  solve_ex l48
     |  solve_ex l49
     |  solve_ex l50
     |  solve_ex l51
     |  solve_ex l52
     |  solve_ex l53
     |  solve_ex l54
     |  solve_ex l55
     |  solve_ex l56
 ].

(** A tactic which tries all possible points **)
Ltac solve_ex_p := first [
        solve_ex p0
     |  solve_ex p1
     |  solve_ex p2
     |  solve_ex p3
     |  solve_ex p4
     |  solve_ex p5
     |  solve_ex p6
     |  solve_ex p7
     |  solve_ex p8
     |  solve_ex p9
     |  solve_ex p10
     |  solve_ex p11
     |  solve_ex p12
     |  solve_ex p13
     |  solve_ex p14
     |  solve_ex p15
     |  solve_ex p16
     |  solve_ex p17
     |  solve_ex p18
     |  solve_ex p19
     |  solve_ex p20
     |  solve_ex p21
     |  solve_ex p22
     |  solve_ex p23
     |  solve_ex p24
     |  solve_ex p25
     |  solve_ex p26
     |  solve_ex p27
     |  solve_ex p28
     |  solve_ex p29
     |  solve_ex p30
     |  solve_ex p31
     |  solve_ex p32
     |  solve_ex p33
     |  solve_ex p34
     |  solve_ex p35
     |  solve_ex p36
     |  solve_ex p37
     |  solve_ex p38
     |  solve_ex p39
     |  solve_ex p40
     |  solve_ex p41
     |  solve_ex p42
     |  solve_ex p43
     |  solve_ex p44
     |  solve_ex p45
     |  solve_ex p46
     |  solve_ex p47
     |  solve_ex p48
     |  solve_ex p49
     |  solve_ex p50
     |  solve_ex p51
     |  solve_ex p52
     |  solve_ex p53
     |  solve_ex p54
     |  solve_ex p55
     |  solve_ex p56
 ].


(** A1 : any two points lie on a unique line **) 
Lemma a1_exist : forall ( A B :Point) ,{l:Line | Incid A l /\ Incid B l}.
Proof with auto.
intros.
elim A;elim B;solve_ex_l.
Qed.

Lemma degen_point: forall A:Point, forall P: Prop, ~A=A -> P.
Proof.
intuition.
Qed.

Lemma degen_line: forall A:Line, forall P: Prop, A<>A -> P.
Proof.
intuition.
Qed.

Ltac remove_degen := match goal with
| H: ~ ?A=?A |- ?G => apply (degen_point A G H)
| H: ?A<>?A |- ?G => apply (degen_line A G H)
end.

Lemma uniqueness : forall A B :Point, forall l m : Line,
 Incid A l -> Incid B l  -> Incid A m -> Incid B m -> A=B\/l=m.
Proof.
intros P Q l m H1 H2 H3 H4.
 induction P; induction Q; try (left;reflexivity);
 induction l; try discriminate;
 induction m; try discriminate;try (left; reflexivity);try (right; reflexivity).
Qed.

Lemma a1_unique:forall (A B :Point)(l1 l2:Line), 
  ~A=B -> Incid A l1 -> Incid B l1 -> Incid A l2 -> Incid B l2 -> l1=l2.
Proof.
intros X Y l1 l2 HXY H1 H2 H3 H4.
induction X;induction Y; try remove_degen;
induction l1;try discriminate; induction l2; discriminate || reflexivity.
Qed.

Lemma a2_unique : forall(l1 l2 :Line)(A B :Point), 
  ~l1=l2 -> Incid A l1 -> Incid A l2 -> Incid B l1 -> Incid B l2 -> A=B.
Proof.
intros l1 l2 X Y H H1 H2 H3 H4.
 induction X;induction Y;try reflexivity;
 induction l1;try discriminate;
 induction l2;try discriminate;try remove_degen.
Qed.

(** A2 : any two lines meet in a unique point **)
Lemma a2_exist : forall (l1 l2:Line), {A:Point | Incid A l1 /\ Incid A l2}.
Proof.
intros l1 l2.
induction l1;induction l2;solve_ex_p.
Qed.

(** A3 : there exist four points with no three collinear **)
Lemma a3 : {A:Point & {B :Point & {C:Point & {D :Point |
  (forall l :Line, ~A = B /\ ~A = C /\ ~A = D /\ ~B = C /\ ~B = D /\ ~C = D /\ 
    (Incid A l /\ Incid B l -> ~Incid C l /\ ~Incid D l)
    /\ (Incid A l /\ Incid C l -> ~Incid B l /\ ~Incid D l)
    /\  (Incid A l /\ Incid D l -> ~Incid C l /\ ~Incid B l)
    /\  (Incid C l /\ Incid B l -> ~Incid A l /\ ~Incid D l)
    /\ (Incid D l /\ Incid B l -> ~Incid C l /\ ~Incid A l)
    /\  (Incid C l /\ Incid D l -> ~Incid B l /\ ~Incid A l))}}}}.
Proof.
exists p1.
exists p2.
exists p6.
exists p11.
intros.
elim l;unfold Incid, Incid_bool;intuition;try discriminate.
Qed.

Instance ObjectPointFano : ObjectPoint := {
Point := Point
}.

Instance ProjectiveStructureFano : ProjectiveStructure ObjectPointFano := {
Line := Line;
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

End s_fanoPlaneModelPG27Generated.