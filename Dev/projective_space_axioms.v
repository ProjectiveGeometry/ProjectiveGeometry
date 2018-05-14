Require Export ProjectiveGeometry.Dev.general_tactics.

(*****************************************************************************)
(** PreProjective space **)


Section s_PreProjectiveSpace.


Class PreProjectiveSpace `(PSLE : ProjectiveStructureLEU) := {
Intersect (l1 l2 : Line) := exists P : Point, Incid P l1 /\ (Incid P l2);
Intersect_In (l1 l2 : Line) (P : Point) := Incid P l1 /\ Incid P l2;
a2 : forall A B C D : Point, forall lAB lCD lAC lBD : Line, 
  ~ A [==] B /\ ~ A [==] C /\ ~ A [==] D /\ ~ B [==] C /\ ~ B [==] D /\ ~ C [==] D ->
  Incid A lAB /\ Incid B lAB ->  
  Incid C lCD /\ Incid D lCD -> 
  Incid A lAC /\ Incid C lAC -> 
  Incid B lBD /\ Incid D lBD ->
  (exists I : Point, (Incid I lAB /\ Incid I lCD)) -> exists J : Point, (Incid J lAC /\ Incid J lBD)
}.


End s_PreProjectiveSpace.


(*****************************************************************************)
(** PreProjective' space **)


Section s_PreProjectiveSpace'.


Class PreProjectiveSpace' `(PSLE : ProjectiveStructureLEU') := {
Intersect_alt (l1 l2 : Line) := exists P : Point, Incid P l1 /\ (Incid P l2);
Intersect_In_alt (l1 l2 : Line) (P : Point) := Incid P l1 /\ Incid P l2;
a2_alt : forall A B C D : Point, forall lAB lCD lAC lBD : Line, 
  ~ A [==] B /\ ~ A [==] C /\ ~ A [==] D /\ ~ B [==] C /\ ~ B [==] D /\ ~ C [==] D ->
  Incid A lAB /\ Incid B lAB ->  
  Incid C lCD /\ Incid D lCD -> 
  Incid A lAC /\ Incid C lAC -> 
  Incid B lBD /\ Incid D lBD ->
  (exists I : Point, (Incid I lAB /\ Incid I lCD)) -> exists J : Point, (Incid J lAC /\ Incid J lBD)
}.


End s_PreProjectiveSpace'.



(*****************************************************************************)
(** Projective space or higher **)


Section s_ProjectiveSpaceOrHigher.


Class ProjectiveSpaceOrHigher `(PPS : PreProjectiveSpace) := {
a3_1 : forall l : Line, {A : Point & {B : Point & {C : Point |
  (~ A [==] B /\ ~ A [==] C /\ ~ B [==] C /\ Incid A l /\ Incid B l /\ Incid C l)}}};
a3_2 : {l1 : Line & {l2 : Line | forall p : Point, ~(Incid p l1 /\ Incid p l2)}}
}.


End s_ProjectiveSpaceOrHigher.


(*****************************************************************************)
(** Projective space **)


Section s_ProjectiveSpace.


Class ProjectiveSpace `(PSH : ProjectiveSpaceOrHigher) := {
a3_3 : forall l1 l2 l3 : Line, ~ l1 = l2 /\ ~ l1 = l3 /\ ~ l2 = l3 -> 
  exists l4 : Line, exists J1 : Point, exists J2 : Point, exists J3 : Point,
  (Intersect_In l1 l4 J1) /\ (Intersect_In l2 l4 J2) /\ (Intersect_In l3 l4 J3)
}.


End s_ProjectiveSpace.


(*****************************************************************************)
(** VeblenYoung projective space **)


Section s_VeblenYoungProjectiveSpace.


(* TO DO 

Parameter Point: Set.
Parameter Line: Set.
Parameter Incid : Point -> Line -> Prop.

(* A1 line existence *)
Axiom A1 : forall A B, A <> B -> {l:Line | Incid A l /\ Incid B l}.

(* A2 line unicity *)
Axiom A2 : forall (A B :Point)(l1 l2:Line), A<>B ->
   Incid A l1 -> Incid B l1  -> Incid A l2 -> Incid B l2 -> l1=l2.

Definition collinear A B C := exists l, Incid A l /\ Incid B l /\ Incid C l.

Axiom A3: forall A B C D E, ~ collinear A B C -> D<>E -> collinear B C D -> collinear C A E ->
 {F:Point | collinear A B F /\ collinear D E F}.

Axiom E0: forall l, {A:Point & {B:Point & {C:Point | (dist_3 Point A B C/\Incid A l /\Incid B l /\ Incid C l)}}}.

(* E1 *)
Axiom l0 : Line.

Axiom E2: ~ exists l, forall A, Incid A l.

(* E3 all points are not on the same plane *) 

(* E3' if S3 is a three space, every point is on S3 *)


(* E3' is equivalent to any two distinct planes have a line in common *)
(* E3' is equivalent to every set of five points lie on the same three-space *)

*)


End s_VeblenYoungProjectiveSpace.


(*****************************************************************************)
(** Projective space to rank **)


Section s_ProjectiveSpaceToRank.


Class ProjectiveSpaceOrHigherRank `(PSH : ProjectiveSpaceOrHigher).

Class ProjectiveSpaceRank `(PSH : ProjectiveSpace).

End s_ProjectiveSpaceToRank.