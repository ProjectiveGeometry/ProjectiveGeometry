Require Export ProjectiveGeometry.Dev.sets_of_points.

(*****************************************************************************)
(** Matroid **)


Section s_matroid.


Class Matroid `(MR : MatroidRk) := {
matroid1_a  : forall X, rk X >= 0;
matroid1_b : forall X, rk X <= cardinal X;
matroid2 : forall X Y, Subset X Y -> rk X <= rk Y;
matroid3 : forall X Y, rk(union X Y) + rk(inter X Y) <= rk X + rk Y
}.


End s_matroid.


Section s_matroid'.


Class Matroid' `(MR : MatroidRk) := {
rk_compat : forall x x', Equal x x' -> rk x = rk x';
matroid1' : rk empty = 0;
matroid2' : forall X, forall x, rk X <= rk (add x X) <= rk X + 1;
matroid3' : forall X, forall y z, 
  rk (add y X) = rk (add z X) -> rk (add z X) = rk X ->
  rk X = rk (union X (couple y z))
}.


End s_matroid'.




