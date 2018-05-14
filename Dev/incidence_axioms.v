Require Export ProjectiveGeometry.Dev.decidability.

(*****************************************************************************)
(** Incidence structure **)


Section s_IncidenceStructure.

(** We need a notion of point and line. *)
(** line_existence : for every pair of distinct points there is a line containing them. *)
(** unicity : there is only one line going through two points *)
(** two_points_on_line : every line contains at least two points *)
(** plan : There exists three non collinear points *)

Class IncidenceStructure `(Op : ObjectPoint) := {
Line : Set;
Incid : Point -> Line -> Prop;

line_existence : forall A B, {l:Line | Incid A l /\ Incid B l};
unicity : forall A B l m, Incid A l -> Incid B l -> Incid A m -> Incid B m -> l = m \/ A [==] B;
two_points_on_line : forall l, {A : Point & {B : Point | Incid B l /\ Incid A l /\ ~ A [==] B}};

Col (A B C : Point) := exists l : Line,  Incid A l /\ Incid B l /\ Incid C l;

plan : {A : Point & {B : Point & {C : Point | ~ Col A B C}}}
}.

End s_IncidenceStructure.
