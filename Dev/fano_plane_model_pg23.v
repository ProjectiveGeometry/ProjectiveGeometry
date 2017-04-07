Require Export ProjectiveGeometry.Dev.projective_plane_axioms.

(**  PG(2,3). **)

(** To show that our axiom system is consistent we build a finite model. **)

Section s_fanoPlaneModelPG23.

(** We define point and line by an inductive type representing the thirteen possibilities. **)
(** We can not use directly the inductive type for a technical reason related to Coq's implementation. **)

Inductive ind_Point : Set := A | B | C | D | E | F | G | H | I | J | K | L | M.
Inductive ind_line : Set := ABCD | AEFG | AIJM | AHKL | BEHI | BGJL | BFKM | CELM | CFHJ | CGIK | DEJK | DGHM | DFIL.

Definition Point : Set := ind_Point.
Definition Line : Set := ind_line.

Definition Incid_bool : Point -> Line -> bool := fun P l =>
 match P with
| A =>
    match l with
    | ABCD | AEFG | AIJM | AHKL => true
    | _ => false
    end
| B =>
    match l with
    | ABCD | BEHI | BGJL | BFKM => true
    | _ => false
    end
| C =>
    match l with
    | ABCD | CELM | CFHJ | CGIK => true
    | _ => false
    end
| D =>
    match l with
    | ABCD | DEJK | DGHM | DFIL=> true
    | _ => false
    end
| E =>
    match l with
    | AEFG | BEHI | CELM | DEJK => true
    | _ => false
    end
| F =>
    match l with
    | AEFG | BFKM | CFHJ | DFIL => true
    | _ => false
    end
| G =>
    match l with
    | AEFG | BGJL | CGIK | DGHM => true
    | _ => false
    end
| H =>
    match l with
    | AHKL | BEHI | CFHJ | DGHM => true
    | _ => false
    end
| I =>
    match l with
    | AIJM | BEHI | CGIK | DFIL => true
    | _ => false
    end
| J =>
    match l with
    | AIJM | BGJL | CFHJ | DEJK => true
    | _ => false
    end
| K =>
    match l with
    | AHKL | BFKM | CGIK | DEJK => true
    | _ => false
    end
| L =>
    match l with
    | AHKL | BGJL | CELM | DFIL => true
    | _ => false
    end
| M =>
    match l with
    | AIJM | BFKM | CELM | DGHM => true
    | _ => false
    end
end.

Definition Incid : Point -> Line -> Prop := fun P L => (Incid_bool P L = true).

Hint Unfold Incid Incid_bool.

Lemma incid_dec : forall (A:Point) (l:Line), {Incid A l} + {~Incid A l}.
Proof.
intros.
unfold Incid.
elim l;elim A0;unfold Incid_bool;simpl;auto;right;discriminate.
Qed.

Ltac solve_ex L := solve [exists L;auto].

(** A tactic which tries all possible lines **)
Ltac solve_ex_l := first [solve_ex ABCD
     |  solve_ex AEFG
     |  solve_ex AIJM
     |  solve_ex AHKL
     |  solve_ex BEHI
     |  solve_ex BGJL
     |  solve_ex BFKM
     |  solve_ex CELM
     |  solve_ex CFHJ
     |  solve_ex CGIK
     |  solve_ex DEJK
     |  solve_ex DGHM
     |  solve_ex DFIL
 ].

(** A tactic which tries all possible points **)
Ltac solve_ex_p := first [
        solve_ex A
     |  solve_ex B
     |  solve_ex C
     |  solve_ex D
     |  solve_ex E
     |  solve_ex F
     |  solve_ex G
     |  solve_ex H
     |  solve_ex I
     |  solve_ex J
     |  solve_ex K
     |  solve_ex L
     |  solve_ex M
 ].

(** A1 : any two points lie on a unique line **) 
Lemma a1_exist : forall ( A B :Point) ,{l:Line | Incid A l /\ Incid B l}.
Proof with auto.
intros.
elim A0;elim B0;solve_ex_l.
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
 induction l;try discriminate;
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
intros.
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
exists A.
exists E.
exists I.
exists K.
intros.
split.
intuition;discriminate.
elim l;unfold Incid, Incid_bool;intuition;discriminate.
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

End s_fanoPlaneModelPG23.