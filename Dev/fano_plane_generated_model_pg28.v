Require Export ProjectiveGeometry.Dev.projective_plane_axioms.

(**  PG(2,8). **)

(** To show that our axiom system is consistent we build a finite model. **)

Section s_fanoPlaneModelPG28Generated.

(** We can not use directly the inductive type for a technical reason related to Coq's implementation. **)

Inductive ind_Point : Set := p0 | p1 | p2 | p3 | p4 | p5 | p6 | p7 | p8 | p9 | p10 | p11 | p12 | p13 | p14 | p15 | p16 | p17 | p18 | p19 | p20 | p21 | p22 | p23 | p24 | p25 | p26 | p27 | p28 | p29 | p30 | p31 | p32 | p33 | p34 | p35 | p36 | p37 | p38 | p39 | p40 | p41 | p42 | p43 | p44 | p45 | p46 | p47 | p48 | p49 | p50 | p51 | p52 | p53 | p54 | p55 | p56 | p57 | p58 | p59 | p60 | p61 | p62 | p63 | p64 | p65 | p66 | p67 | p68 | p69 | p70 | p71 | p72.
 
Inductive ind_line : Set := l0 | l1 | l2 | l3 | l4 | l5 | l6 | l7 | l8 | l9 | l10 | l11 | l12 | l13 | l14 | l15 | l16 | l17 | l18 | l19 | l20 | l21 | l22 | l23 | l24 | l25 | l26 | l27 | l28 | l29 | l30 | l31 | l32 | l33 | l34 | l35 | l36 | l37 | l38 | l39 | l40 | l41 | l42 | l43 | l44 | l45 | l46 | l47 | l48 | l49 | l50 | l51 | l52 | l53 | l54 | l55 | l56 | l57 | l58 | l59 | l60 | l61 | l62 | l63 | l64 | l65 | l66 | l67 | l68 | l69 | l70 | l71 | l72.
 
Definition Point : Set := ind_Point.
Definition Line : Set := ind_line.
 
Definition Incid_bool : Point -> Line -> bool := fun P l =>
 match P with
| p0 =>
	match l with
	| l9| l18| l36| l41| l57| l65| l69| l71| l72=> true
	| _ => false
	end
| p1 =>
	match l with
	| l0| l10| l19| l37| l42| l58| l66| l70| l72=> true
	| _ => false
	end
| p2 =>
	match l with
	| l0| l1| l11| l20| l38| l43| l59| l67| l71=> true
	| _ => false
	end
| p3 =>
	match l with
	| l1| l2| l12| l21| l39| l44| l60| l68| l72=> true
	| _ => false
	end
| p4 =>
	match l with
	| l0| l2| l3| l13| l22| l40| l45| l61| l69=> true
	| _ => false
	end
| p5 =>
	match l with
	| l1| l3| l4| l14| l23| l41| l46| l62| l70=> true
	| _ => false
	end
| p6 =>
	match l with
	| l2| l4| l5| l15| l24| l42| l47| l63| l71=> true
	| _ => false
	end
| p7 =>
	match l with
	| l3| l5| l6| l16| l25| l43| l48| l64| l72=> true
	| _ => false
	end
| p8 =>
	match l with
	| l0| l4| l6| l7| l17| l26| l44| l49| l65=> true
	| _ => false
	end
| p9 =>
	match l with
	| l1| l5| l7| l8| l18| l27| l45| l50| l66=> true
	| _ => false
	end
| p10 =>
	match l with
	| l2| l6| l8| l9| l19| l28| l46| l51| l67=> true
	| _ => false
	end
| p11 =>
	match l with
	| l3| l7| l9| l10| l20| l29| l47| l52| l68=> true
	| _ => false
	end
| p12 =>
	match l with
	| l4| l8| l10| l11| l21| l30| l48| l53| l69=> true
	| _ => false
	end
| p13 =>
	match l with
	| l5| l9| l11| l12| l22| l31| l49| l54| l70=> true
	| _ => false
	end
| p14 =>
	match l with
	| l6| l10| l12| l13| l23| l32| l50| l55| l71=> true
	| _ => false
	end
| p15 =>
	match l with
	| l7| l11| l13| l14| l24| l33| l51| l56| l72=> true
	| _ => false
	end
| p16 =>
	match l with
	| l0| l8| l12| l14| l15| l25| l34| l52| l57=> true
	| _ => false
	end
| p17 =>
	match l with
	| l1| l9| l13| l15| l16| l26| l35| l53| l58=> true
	| _ => false
	end
| p18 =>
	match l with
	| l2| l10| l14| l16| l17| l27| l36| l54| l59=> true
	| _ => false
	end
| p19 =>
	match l with
	| l3| l11| l15| l17| l18| l28| l37| l55| l60=> true
	| _ => false
	end
| p20 =>
	match l with
	| l4| l12| l16| l18| l19| l29| l38| l56| l61=> true
	| _ => false
	end
| p21 =>
	match l with
	| l5| l13| l17| l19| l20| l30| l39| l57| l62=> true
	| _ => false
	end
| p22 =>
	match l with
	| l6| l14| l18| l20| l21| l31| l40| l58| l63=> true
	| _ => false
	end
| p23 =>
	match l with
	| l7| l15| l19| l21| l22| l32| l41| l59| l64=> true
	| _ => false
	end
| p24 =>
	match l with
	| l8| l16| l20| l22| l23| l33| l42| l60| l65=> true
	| _ => false
	end
| p25 =>
	match l with
	| l9| l17| l21| l23| l24| l34| l43| l61| l66=> true
	| _ => false
	end
| p26 =>
	match l with
	| l10| l18| l22| l24| l25| l35| l44| l62| l67=> true
	| _ => false
	end
| p27 =>
	match l with
	| l11| l19| l23| l25| l26| l36| l45| l63| l68=> true
	| _ => false
	end
| p28 =>
	match l with
	| l12| l20| l24| l26| l27| l37| l46| l64| l69=> true
	| _ => false
	end
| p29 =>
	match l with
	| l13| l21| l25| l27| l28| l38| l47| l65| l70=> true
	| _ => false
	end
| p30 =>
	match l with
	| l14| l22| l26| l28| l29| l39| l48| l66| l71=> true
	| _ => false
	end
| p31 =>
	match l with
	| l15| l23| l27| l29| l30| l40| l49| l67| l72=> true
	| _ => false
	end
| p32 =>
	match l with
	| l0| l16| l24| l28| l30| l31| l41| l50| l68=> true
	| _ => false
	end
| p33 =>
	match l with
	| l1| l17| l25| l29| l31| l32| l42| l51| l69=> true
	| _ => false
	end
| p34 =>
	match l with
	| l2| l18| l26| l30| l32| l33| l43| l52| l70=> true
	| _ => false
	end
| p35 =>
	match l with
	| l3| l19| l27| l31| l33| l34| l44| l53| l71=> true
	| _ => false
	end
| p36 =>
	match l with
	| l4| l20| l28| l32| l34| l35| l45| l54| l72=> true
	| _ => false
	end
| p37 =>
	match l with
	| l0| l5| l21| l29| l33| l35| l36| l46| l55=> true
	| _ => false
	end
| p38 =>
	match l with
	| l1| l6| l22| l30| l34| l36| l37| l47| l56=> true
	| _ => false
	end
| p39 =>
	match l with
	| l2| l7| l23| l31| l35| l37| l38| l48| l57=> true
	| _ => false
	end
| p40 =>
	match l with
	| l3| l8| l24| l32| l36| l38| l39| l49| l58=> true
	| _ => false
	end
| p41 =>
	match l with
	| l4| l9| l25| l33| l37| l39| l40| l50| l59=> true
	| _ => false
	end
| p42 =>
	match l with
	| l5| l10| l26| l34| l38| l40| l41| l51| l60=> true
	| _ => false
	end
| p43 =>
	match l with
	| l6| l11| l27| l35| l39| l41| l42| l52| l61=> true
	| _ => false
	end
| p44 =>
	match l with
	| l7| l12| l28| l36| l40| l42| l43| l53| l62=> true
	| _ => false
	end
| p45 =>
	match l with
	| l8| l13| l29| l37| l41| l43| l44| l54| l63=> true
	| _ => false
	end
| p46 =>
	match l with
	| l9| l14| l30| l38| l42| l44| l45| l55| l64=> true
	| _ => false
	end
| p47 =>
	match l with
	| l10| l15| l31| l39| l43| l45| l46| l56| l65=> true
	| _ => false
	end
| p48 =>
	match l with
	| l11| l16| l32| l40| l44| l46| l47| l57| l66=> true
	| _ => false
	end
| p49 =>
	match l with
	| l12| l17| l33| l41| l45| l47| l48| l58| l67=> true
	| _ => false
	end
| p50 =>
	match l with
	| l13| l18| l34| l42| l46| l48| l49| l59| l68=> true
	| _ => false
	end
| p51 =>
	match l with
	| l14| l19| l35| l43| l47| l49| l50| l60| l69=> true
	| _ => false
	end
| p52 =>
	match l with
	| l15| l20| l36| l44| l48| l50| l51| l61| l70=> true
	| _ => false
	end
| p53 =>
	match l with
	| l16| l21| l37| l45| l49| l51| l52| l62| l71=> true
	| _ => false
	end
| p54 =>
	match l with
	| l17| l22| l38| l46| l50| l52| l53| l63| l72=> true
	| _ => false
	end
| p55 =>
	match l with
	| l0| l18| l23| l39| l47| l51| l53| l54| l64=> true
	| _ => false
	end
| p56 =>
	match l with
	| l1| l19| l24| l40| l48| l52| l54| l55| l65=> true
	| _ => false
	end
| p57 =>
	match l with
	| l2| l20| l25| l41| l49| l53| l55| l56| l66=> true
	| _ => false
	end
| p58 =>
	match l with
	| l3| l21| l26| l42| l50| l54| l56| l57| l67=> true
	| _ => false
	end
| p59 =>
	match l with
	| l4| l22| l27| l43| l51| l55| l57| l58| l68=> true
	| _ => false
	end
| p60 =>
	match l with
	| l5| l23| l28| l44| l52| l56| l58| l59| l69=> true
	| _ => false
	end
| p61 =>
	match l with
	| l6| l24| l29| l45| l53| l57| l59| l60| l70=> true
	| _ => false
	end
| p62 =>
	match l with
	| l7| l25| l30| l46| l54| l58| l60| l61| l71=> true
	| _ => false
	end
| p63 =>
	match l with
	| l8| l26| l31| l47| l55| l59| l61| l62| l72=> true
	| _ => false
	end
| p64 =>
	match l with
	| l0| l9| l27| l32| l48| l56| l60| l62| l63=> true
	| _ => false
	end
| p65 =>
	match l with
	| l1| l10| l28| l33| l49| l57| l61| l63| l64=> true
	| _ => false
	end
| p66 =>
	match l with
	| l2| l11| l29| l34| l50| l58| l62| l64| l65=> true
	| _ => false
	end
| p67 =>
	match l with
	| l3| l12| l30| l35| l51| l59| l63| l65| l66=> true
	| _ => false
	end
| p68 =>
	match l with
	| l4| l13| l31| l36| l52| l60| l64| l66| l67=> true
	| _ => false
	end
| p69 =>
	match l with
	| l5| l14| l32| l37| l53| l61| l65| l67| l68=> true
	| _ => false
	end
| p70 =>
	match l with
	| l6| l15| l33| l38| l54| l62| l66| l68| l69=> true
	| _ => false
	end
| p71 =>
	match l with
	| l7| l16| l34| l39| l55| l63| l67| l69| l70=> true
	| _ => false
	end
| p72 =>
	match l with
	| l8| l17| l35| l40| l56| l64| l68| l70| l71=> true
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

Ltac solve_ex_p := first [
		solve_ex p0
	|	solve_ex p1
	|	solve_ex p2
	|	solve_ex p3
	|	solve_ex p4
	|	solve_ex p5
	|	solve_ex p6
	|	solve_ex p7
	|	solve_ex p8
	|	solve_ex p9
	|	solve_ex p10
	|	solve_ex p11
	|	solve_ex p12
	|	solve_ex p13
	|	solve_ex p14
	|	solve_ex p15
	|	solve_ex p16
	|	solve_ex p17
	|	solve_ex p18
	|	solve_ex p19
	|	solve_ex p20
	|	solve_ex p21
	|	solve_ex p22
	|	solve_ex p23
	|	solve_ex p24
	|	solve_ex p25
	|	solve_ex p26
	|	solve_ex p27
	|	solve_ex p28
	|	solve_ex p29
	|	solve_ex p30
	|	solve_ex p31
	|	solve_ex p32
	|	solve_ex p33
	|	solve_ex p34
	|	solve_ex p35
	|	solve_ex p36
	|	solve_ex p37
	|	solve_ex p38
	|	solve_ex p39
	|	solve_ex p40
	|	solve_ex p41
	|	solve_ex p42
	|	solve_ex p43
	|	solve_ex p44
	|	solve_ex p45
	|	solve_ex p46
	|	solve_ex p47
	|	solve_ex p48
	|	solve_ex p49
	|	solve_ex p50
	|	solve_ex p51
	|	solve_ex p52
	|	solve_ex p53
	|	solve_ex p54
	|	solve_ex p55
	|	solve_ex p56
	|	solve_ex p57
	|	solve_ex p58
	|	solve_ex p59
	|	solve_ex p60
	|	solve_ex p61
	|	solve_ex p62
	|	solve_ex p63
	|	solve_ex p64
	|	solve_ex p65
	|	solve_ex p66
	|	solve_ex p67
	|	solve_ex p68
	|	solve_ex p69
	|	solve_ex p70
	|	solve_ex p71
	|	solve_ex p72
].

Ltac solve_ex_l := first [
		solve_ex l0
	|	solve_ex l1
	|	solve_ex l2
	|	solve_ex l3
	|	solve_ex l4
	|	solve_ex l5
	|	solve_ex l6
	|	solve_ex l7
	|	solve_ex l8
	|	solve_ex l9
	|	solve_ex l10
	|	solve_ex l11
	|	solve_ex l12
	|	solve_ex l13
	|	solve_ex l14
	|	solve_ex l15
	|	solve_ex l16
	|	solve_ex l17
	|	solve_ex l18
	|	solve_ex l19
	|	solve_ex l20
	|	solve_ex l21
	|	solve_ex l22
	|	solve_ex l23
	|	solve_ex l24
	|	solve_ex l25
	|	solve_ex l26
	|	solve_ex l27
	|	solve_ex l28
	|	solve_ex l29
	|	solve_ex l30
	|	solve_ex l31
	|	solve_ex l32
	|	solve_ex l33
	|	solve_ex l34
	|	solve_ex l35
	|	solve_ex l36
	|	solve_ex l37
	|	solve_ex l38
	|	solve_ex l39
	|	solve_ex l40
	|	solve_ex l41
	|	solve_ex l42
	|	solve_ex l43
	|	solve_ex l44
	|	solve_ex l45
	|	solve_ex l46
	|	solve_ex l47
	|	solve_ex l48
	|	solve_ex l49
	|	solve_ex l50
	|	solve_ex l51
	|	solve_ex l52
	|	solve_ex l53
	|	solve_ex l54
	|	solve_ex l55
	|	solve_ex l56
	|	solve_ex l57
	|	solve_ex l58
	|	solve_ex l59
	|	solve_ex l60
	|	solve_ex l61
	|	solve_ex l62
	|	solve_ex l63
	|	solve_ex l64
	|	solve_ex l65
	|	solve_ex l66
	|	solve_ex l67
	|	solve_ex l68
	|	solve_ex l69
	|	solve_ex l70
	|	solve_ex l71
	|	solve_ex l72
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
exists p19.
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

End s_fanoPlaneModelPG28Generated.