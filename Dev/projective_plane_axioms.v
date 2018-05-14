Require Export ProjectiveGeometry.Dev.general_tactics.

(*****************************************************************************)
(** PreProjective plan **)


Section s_PreProjectivePlane.


Class PreProjectivePlane `(PSLE : ProjectiveStructureLEU)  := {
a2_exist : forall (l1 l2 : Line), {A : Point | Incid A l1 /\ Incid A l2}
}.


End s_PreProjectivePlane.



(*****************************************************************************)
(** A variant of PreProjective plan **)


Section s_PreProjectivePlane'.


Class PreProjectivePlane' `(PSLE : ProjectiveStructureLEU') := {
a2_exist_alt : forall (l1 l2 : Line), {A : Point | Incid A l1 /\ Incid A l2}
}.


End s_PreProjectivePlane'.


(*****************************************************************************)
(** Projective plane **)


Section s_ProjectivePlane.


Class ProjectivePlane `(PPP : PreProjectivePlane) := {
a3 : {A : Point & {B : Point & {C : Point & {D : Point |
  (forall l : Line, ~A [==] B /\ ~A [==] C /\ ~A [==] D /\ ~B [==] C /\ ~B [==] D /\ ~C [==] D
  /\ (Incid A l /\ Incid B l -> ~Incid C l /\ ~Incid D l)
  /\ (Incid A l /\ Incid C l -> ~Incid B l /\ ~Incid D l)
  /\ (Incid A l /\ Incid D l -> ~Incid C l /\ ~Incid B l)
  /\ (Incid C l /\ Incid B l -> ~Incid A l /\ ~Incid D l)
  /\ (Incid D l /\ Incid B l -> ~Incid C l /\ ~Incid A l)
  /\ (Incid C l /\ Incid D l -> ~Incid B l /\ ~Incid A l))}}}}
}.


End s_ProjectivePlane.


(*****************************************************************************)
(** A variant of projective geometry **)


Section s_ProjectivePlane'.


Class ProjectivePlane' `(PPP : PreProjectivePlane) := {
a3_1 : forall l : Line, {A : Point & {B : Point & {C : Point |
  (~ A [==] B /\ ~ A [==] C /\ ~ B [==] C /\ Incid A l /\ Incid B l /\ Incid C l)}}};
a3_2 : {l1 : Line & {l2 : Line | l1 <> l2}}
}.


End s_ProjectivePlane'.


(*****************************************************************************)
(** Another variant of projective geometry **)


Section s_ProjectivePlane''.


Class ProjectivePlane'' `(PPP : PreProjectivePlane') := {
a3_1_alt : forall l : Line, {A : Point & {B : Point & {C : Point |
  (~ A [==] B /\ ~ A [==] C /\ ~ B [==] C /\ Incid A l /\ Incid B l /\ Incid C l)}}}; (* Similar to ProjectivePlane' *)
a3_2_alt : {A : Point & {l : Line | ~ Incid A l}}
}.


End s_ProjectivePlane''.


(*****************************************************************************)
(** Bezem & Hendriks' axioms for projective geometry **)


Section s_CoherentProjectivePlane.


Class CoherentProjectivePlane `(PPP : PreProjectivePlane) := {
l1 : Line;
l2 : Line;
a3_1_coh : forall l : Line, {A : Point & {B : Point & {C : Point |
  (~ A [==] B /\ ~ A [==] C /\ ~ B [==] C /\ Incid A l /\ Incid B l /\ Incid C l)}}}; (* Similar to ProjectivePlane' *)
a3_2_coh : l1 <> l2
}.


End s_CoherentProjectivePlane.


(*****************************************************************************)
(** Coxeter projective plane **)


Section s_CoxeterProjectivePlane.


(* TO DO *)


End s_CoxeterProjectivePlane.


(*****************************************************************************)
(** Projective plane to rank **)


Section s_ProjectivePlaneToRank.


Class ProjectivePlaneRank `(PP : ProjectivePlane').


End s_ProjectivePlaneToRank.

