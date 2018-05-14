Require Export ProjectiveGeometry.Dev.projective_plane_axioms.
Require Export ProjectiveGeometry.Dev.fano_plane.

(** Fano's plane **)
(** also known as PG(2,2). **)

(** To show that our axiom system is consistent we build a finite model. **)

Section s_fanoPlaneModel.

(** We define point and line by an inductive type representing the seven possibilities. **)
(** We can not use directly the inductive type for a technical reason related to Coq's implementation. **)

Inductive ind_Point : Set := A | B | C | D | E | F | G.
Inductive ind_line : Set := ABF | BCD | CAE | ADG | BEG | CFG | DEF.

Definition Point : Set := ind_Point.
Definition Line : Set := ind_line.

Definition Incid_bool : Point -> Line -> bool := fun P l =>
 match P with
| A =>
    match l with
    | ABF => true
    | BCD => false
    | CAE => true
    | ADG => true
    | BEG => false
    | CFG => false
    | DEF => false
    end
| B =>
    match l with
    | ABF => true
    | BCD => true
    | CAE => false
    | ADG => false
    | BEG => true
    | CFG => false
    | DEF => false
    end
| C =>
    match l with
    | ABF => false
    | BCD => true
    | CAE => true
    | ADG => false
    | BEG => false
    | CFG => true
    | DEF => false
    end
| D =>
    match l with
    | ABF => false
    | BCD => true
    | CAE => false
    | ADG => true
    | BEG => false
    | CFG => false
    | DEF => true
    end
| E =>
    match l with
    | ABF => false
    | BCD => false
    | CAE => true
    | ADG => false
    | BEG => true
    | CFG => false
    | DEF => true
    end
| F =>
    match l with
    | ABF => true
    | BCD => false
    | CAE => false
    | ADG => false
    | BEG => false
    | CFG => true
    | DEF => true
    end
| G =>
    match l with
    | ABF => false
    | BCD => false
    | CAE => false
    | ADG => true
    | BEG => true
    | CFG => true
    | DEF => false
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
Ltac solve_ex_l := first [solve_ex ABF
     |  solve_ex BCD
     |  solve_ex CAE
     |  solve_ex ADG
     |  solve_ex BEG
     |  solve_ex CFG
     |  solve_ex DEF
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
 ].

(** A1 : any two points lie on a unique line **) 
Lemma a1_exist : forall ( A B :Point) ,{l:Line | Incid A l /\ Incid B l}.
Proof.
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
induction l; try discriminate;
induction m; try discriminate; try (left; reflexivity) ; try (right; reflexivity); try remove_degen.
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
induction l1;induction l2;
solve_ex_p.
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
exists B.
exists C.
exists G.
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

End s_fanoPlaneModel.



Module fano_plane_inst : fano_plane

with Definition Point:= Point
with Definition A:= A
with Definition B:= B
with Definition C:= C
with Definition D:= D
with Definition E:= E
with Definition F:= F
with Definition G := G

with Definition Line:= Line

with Definition ABF := ABF
with Definition BCD := BCD
with Definition CAE := CAE
with Definition ADG := ADG
with Definition BEG := BEG
with Definition CFG := CFG
with Definition DEF := DEF
with Definition Incid := Incid
.

Definition Point:= Point.

Definition A:= A.
Definition B:= B.
Definition C:= C.
Definition D:= D.
Definition E:= E.
Definition F:= F.
Definition G := G.

Definition Line:= Line.

Definition ABF := ABF.
Definition BCD := BCD.
Definition CAE := CAE.
Definition ADG := ADG.
Definition BEG := BEG.
Definition CFG := CFG.
Definition DEF := DEF.

Definition Incid := Incid.

Lemma is_only_7_pts : forall P:Point, {P=A}+{P=B}+{P=C}+{P=D}+{P=E}+{P=F}+{P=G}.
Proof.
intros.
elim P;
intuition.
Qed.

Lemma is_only_7_lines : forall P:Line, {P=ABF}+{P=BCD}+{P=CAE}+{P=ADG}+{P=BEG}+{P=CFG}+{P=DEF}.
Proof.
intros.
elim P;
intuition.
Qed.

Definition is_fano_plane A B C D E F G ABF BCD CAE ADG BEG CFG DEF :=
(~A=B /\ ~A=C /\ ~A=D /\ ~A=E /\ ~A=F /\ ~A=G /\
~B=C /\ ~B=D /\ ~B=E /\ ~B=F /\ ~B=G /\
~C=D /\ ~C=E /\ ~C=F /\ ~C=G /\
~D=E /\ ~D=F /\ ~D=G /\
~E=F /\ ~E=G /\
~F=G) /\
(ABF<>BCD /\ ABF <>CAE /\ ABF <>ADG /\ ABF<>BEG /\ ABF<>CFG /\ ABF<>DEF /\ 
BCD<>CAE /\ BCD<>ADG /\ BCD<>BEG /\ BCD<>CFG /\ BCD<>DEF /\
CAE<>ADG /\ CAE<>BEG /\ CAE<>CFG /\ CAE<>DEF /\
ADG<>BEG /\ ADG<>CFG /\ADG<>DEF /\
BEG<>CFG /\ BEG<>DEF /\
CFG<>DEF )/\ 

( Incid A ABF /\ Incid B ABF /\ ~ Incid C ABF /\ ~ Incid D ABF /\ ~ Incid E ABF /\ Incid F ABF /\ ~ Incid G  ABF /\
 ~ Incid A BCD /\ Incid B BCD /\ Incid C BCD /\ Incid D BCD /\ ~ Incid E BCD /\ ~ Incid F BCD /\ ~ Incid G  BCD /\
 Incid A CAE /\ ~ Incid B CAE /\ Incid C CAE /\ ~ Incid D CAE /\ Incid E CAE /\ ~ Incid F CAE /\ ~ Incid G  CAE /\
 Incid A ADG /\ ~ Incid B ADG /\ ~ Incid C ADG /\ Incid D ADG /\ ~ Incid E ADG /\ ~ Incid F ADG /\ Incid G  ADG /\
 ~ Incid A BEG /\ Incid B BEG /\ ~ Incid C BEG /\ ~ Incid D BEG /\  Incid E BEG /\ ~ Incid F BEG /\ Incid G  BEG /\
 ~ Incid A CFG /\ ~ Incid B CFG /\ Incid C CFG /\ ~ Incid D CFG /\ ~ Incid E CFG /\ Incid F CFG /\ Incid G  CFG /\
 ~ Incid A DEF /\ ~ Incid B DEF /\ ~ Incid C DEF /\ Incid D DEF /\ Incid E DEF /\ Incid F DEF /\ ~ Incid G  DEF).

Lemma is_fano_plane_inst :  is_fano_plane A B C D E F G ABF BCD CAE ADG BEG CFG DEF.
Proof.
unfold is_fano_plane.
repeat split; try discriminate.
Qed.

End fano_plane_inst.


Module Import Desargues := Desargues fano_plane_inst.

Definition on_line := fun A B C l => Incid A l /\ Incid B l /\ Incid C l.
Definition collinear A B C :=  exists l, Incid A l /\ Incid B l /\ Incid C l.


Theorem Desargues_fano :  
forall O P Q R P' Q' R' alpha beta gamma lP lQ lR lPQ lPR lQR lP'Q' lP'R' lQ'R',
((on_line P Q gamma lPQ) /\ (on_line P' Q' gamma lP'Q')) /\
((on_line P R beta lPR) /\ (on_line P' R' beta lP'R')) /\
((on_line Q R alpha lQR) /\ (on_line Q' R' alpha lQ'R')) /\
((on_line O P P' lP) /\ (on_line O Q Q' lQ) /\(on_line O R R' lR)) /\ 
~collinear O P Q /\  ~collinear O P R /\ ~collinear O Q R /\ 
~collinear P Q R /\ ~collinear P' Q' R' /\ ((P<>P')\/(Q<>Q')\/(R<>R')) ->
collinear alpha beta gamma.
Proof.
intros.
unfold on_line in *; decompose [and] H;clear H.
assert (T:=Desargues.Desargues).
unfold M2.collinear, M2.on_line in *.
unfold fano_plane_inst.Incid,  fano_plane_inst.Line, fano_plane_inst.Point 
in *.
apply (T O P Q R P' Q' R' alpha beta gamma lP lQ lR lPQ lPR lQR lP'Q' lP'R' lQ'R').
repeat split;auto.
Qed.
