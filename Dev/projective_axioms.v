Require Export ProjectiveGeometry.Dev.decidability.

(*****************************************************************************)
(** Projective structure **)


Section s_ProjectiveStructure.

Class ProjectiveStructure `(Op : ObjectPoint) := {
Line : Set;
Incid : Point -> Line -> Prop;

incid_dec : forall (A : Point)(l : Line), {Incid A l} + {~Incid A l}
}.


End s_ProjectiveStructure.


(*****************************************************************************)
(** Projective structure with line existence **)


Section s_ProjectiveStructureLE.


Class ProjectiveStructureLE `(PS : ProjectiveStructure) := {
a1_exist : forall (A B : Point) , {l : Line | Incid A l /\ Incid B l}
}.


End s_ProjectiveStructureLE.


(*****************************************************************************)
(** Projective structure with line existence and uniqueness **)


Section s_ProjectiveStructureLEU.


Class ProjectiveStructureLEU `(PS : ProjectiveStructureLE) := {
uniqueness : forall (A B : Point)(l1 l2 : Line),
  Incid A l1 -> Incid B l1  -> Incid A l2 -> Incid B l2 -> A [==] B \/ l1 = l2
}.


End s_ProjectiveStructureLEU.


(*****************************************************************************)
(** Projective structure with useful version of unicity **)


Section s_ProjectiveStructureLEU'.


Class ProjectiveStructureLEU' `(PSLE : ProjectiveStructureLE) := {
a1_unique:forall (A B : Point)(l1 l2 : Line),
  ~ A [==] B -> Incid A l1 -> Incid B l1  -> Incid A l2 -> Incid B l2 -> l1 = l2;
a2_unique : forall(l1 l2 : Line)(A B : Point), 
  ~ l1 = l2 -> Incid A l1 -> Incid B l1 -> Incid A l2 -> Incid B l2 -> A [==] B
}.


End s_ProjectiveStructureLEU'.
