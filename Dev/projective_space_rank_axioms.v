Require Export ProjectiveGeometry.Dev.projective_rank_axioms.

(*****************************************************************************)
(** Rank **)


Section s_rankProjectiveSpace.


Class RankProjectiveSpace `(RP : RankProjective) := {
rk_pasch : forall A B C D, rk (quadruple A B C D) <= 3 -> exists J : Point, rk (triple A B J) = 2 /\ rk (triple C D J) = 2;

P0 : Point;
P1 : Point;
P2 : Point;
P3 : Point;
rk_lower_dim : rk (quadruple P0 P1 P2 P3) = 4;

rk_upper_dim : forall A B C D E F,
rk (couple A B) = 2 /\ rk (couple C D) = 2 /\ rk (couple E F) = 2 /\
rk (quadruple A B C D) >= 3 /\ rk (quadruple A B E F) >= 3 /\ rk (quadruple C D E F) >= 3 ->
exists J1 : Point, exists J2 : Point, exists J3 : Point, 
rk(triple A B J1) = 2 /\ rk(triple C D J2) = 2 /\ rk(triple E F J3) = 2 /\ rk(triple J1 J2 J3) <= 2
}.


End s_rankProjectiveSpace.