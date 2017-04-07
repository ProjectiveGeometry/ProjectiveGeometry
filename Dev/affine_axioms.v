Require Export ProjectiveGeometry.Dev.decidability.

(*****************************************************************************)
(** Affine **)

Section s_Affine.

Class Affine := {
Point : Set;
Line : Set;
Incid : Point -> Line -> Prop;

eq_point_dec : forall A B : Point, {A[==]B} + {~A[==]B};
incid_dec : forall (A : Point)(l : Line), {Incid A l} + {~Incid A l};
eq_line_dec : forall l m : Line, {l = m} + {l <> m};

line_existence : forall A B, {l:Line | Incid A l /\ Incid B l};
unicity : forall A B l m, Incid A l -> Incid B l -> Incid A m -> Incid B m -> l = m \/ A [==] B;
two_points_on_line : forall l, {A : Point & {B : Point | Incid B l /\ Incid A l /\ ~ A [==] B}};

Col (A B C : Point) := exists l : Line,  Incid A l /\ Incid B l /\ Incid C l;

plan : {A : Point & {B : Point & {C : Point | ~ Col A B C}}};

intersect l1 l2 := exists  P : Point,Incid P l1 /\ Incid P l2 /\ l1 <> l2;
intersect_exists l1 l2 : {P : Point | Incid P l1 /\ Incid P l2 /\ l1 <> l2};

parallel l1 l2 := if (eq_line_dec l1 l2) then True else ~intersect l1 l2;

euclid_exists : forall P l, ~ Incid P l -> {m | parallel m l /\ Incid P m};
euclid_uniq : forall P l m1 m2, ~ Incid P l -> 
parallel m1 l -> Incid P m1 ->
parallel m2 l -> Incid P m2 -> m1 = m2;

parallel_dec : forall l1 l2, {parallel l1 l2} + {intersect l1 l2}
}.

End s_Affine.
