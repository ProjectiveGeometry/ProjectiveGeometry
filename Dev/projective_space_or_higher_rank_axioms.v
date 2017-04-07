Require Export ProjectiveGeometry.Dev.projective_rank_axioms.

(*****************************************************************************)
(** Rank **)


Section s_rankProjectiveSpaceOrHigher.


Class RankProjectiveSpaceOrHigher `(RP : RankProjective) := {
rk_pasch : forall A B C D, rk (quadruple A B C D) <= 3 -> exists J, rk (triple A B J) = 2 /\ rk (triple C D J) = 2;

P0 : Point;
P1 : Point;
P2 : Point;
P3 : Point;
rk_lower_dim : rk (quadruple P0 P1 P2 P3) >= 4
}.


End s_rankProjectiveSpaceOrHigher.