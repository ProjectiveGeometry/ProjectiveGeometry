Require Export ProjectiveGeometry.Dev.projective_plane_axioms.

(**  PG(2,4). **)

(** To show that our axiom system is consistent we build a finite model. **)

Section s_fanoPlaneModelPG24Generated.

(** We define point and line by an inductive type representing the thirteen possibilities. **)
(** We can not use directly the inductive type for a technical reason related to Coq's implementation. **)

Inductive ind_Point : Set := p0 | p1 | p2 | p3 | p4 | p5 | p6 | p7 | p8 | p9 | p10 | p11 | p12 | p13 | p14 | p15 | p16 | p17 | p18 | p19 | p20.
 
Inductive ind_line : Set := l0 | l1 | l2 | l3 | l4 | l5 | l6 | l7 | l8 | l9 | l10 | l11 | l12 | l13 | l14 | l15 | l16 | l17 | l18 | l19 | l20.
 
Definition Point : Set := ind_Point.
Definition Line : Set := ind_line.
 
Definition Incid_bool : Point -> Line -> bool := fun P l =>
 match P with
| p0 =>
	match l with
	| l4| l6| l16| l19| l20=> true
	| _ => false
	end
| p1 =>
	match l with
	| l0| l5| l7| l17| l20=> true
	| _ => false
	end
| p2 =>
	match l with
	| l0| l1| l6| l8| l18=> true
	| _ => false
	end
| p3 =>
	match l with
	| l1| l2| l7| l9| l19=> true
	| _ => false
	end
| p4 =>
	match l with
	| l2| l3| l8| l10| l20=> true
	| _ => false
	end
| p5 =>
	match l with
	| l0| l3| l4| l9| l11=> true
	| _ => false
	end
| p6 =>
	match l with
	| l1| l4| l5| l10| l12=> true
	| _ => false
	end
| p7 =>
	match l with
	| l2| l5| l6| l11| l13=> true
	| _ => false
	end
| p8 =>
	match l with
	| l3| l6| l7| l12| l14=> true
	| _ => false
	end
| p9 =>
	match l with
	| l4| l7| l8| l13| l15=> true
	| _ => false
	end
| p10 =>
	match l with
	| l5| l8| l9| l14| l16=> true
	| _ => false
	end
| p11 =>
	match l with
	| l6| l9| l10| l15| l17=> true
	| _ => false
	end
| p12 =>
	match l with
	| l7| l10| l11| l16| l18=> true
	| _ => false
	end
| p13 =>
	match l with
	| l8| l11| l12| l17| l19=> true
	| _ => false
	end
| p14 =>
	match l with
	| l9| l12| l13| l18| l20=> true
	| _ => false
	end
| p15 =>
	match l with
	| l0| l10| l13| l14| l19=> true
	| _ => false
	end
| p16 =>
	match l with
	| l1| l11| l14| l15| l20=> true
	| _ => false
	end
| p17 =>
	match l with
	| l0| l2| l12| l15| l16=> true
	| _ => false
	end
| p18 =>
	match l with
	| l1| l3| l13| l16| l17=> true
	| _ => false
	end
| p19 =>
	match l with
	| l2| l4| l14| l17| l18=> true
	| _ => false
	end
| p20 =>
	match l with
	| l3| l5| l15| l18| l19=> true
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

End s_fanoPlaneModelPG24Generated.