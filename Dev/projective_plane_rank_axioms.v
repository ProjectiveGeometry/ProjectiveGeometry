Require Export ProjectiveGeometry.Dev.projective_rank_axioms.

(*****************************************************************************)
(** Rank **)


Section s_rankProjectivePlane.


Class RankProjectivePlane `(RP : RankProjective) := {
rk_inter : forall A B C D, exists J, rk (triple A B J) = 2 /\ rk (triple C D J) = 2;

P0 : Point;
P1 : Point;
P2 : Point;
rk_lower_dim : rk (triple P0 P1 P2) >= 3
}.


End s_rankProjectivePlane.