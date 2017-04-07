Require Export ProjectiveGeometry.Dev.matroid_axioms.

(*****************************************************************************)
(** Rank **)


Section s_rankProjective.


Class RankProjective `(M : Matroid) := {
rk_singleton_ge : forall P, rk (singleton P) >= 1;
rk_couple_ge : forall P Q, ~ P [==] Q -> rk(couple P Q) >= 2;
rk_three_points_on_lines : forall A B, exists C, rk (triple A B C) = 2 /\ rk (couple B C) = 2 /\ rk (couple A C) = 2
}.


End s_rankProjective.