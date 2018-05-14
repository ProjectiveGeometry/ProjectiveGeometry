Require Export ProjectiveGeometry.Dev.desargues_2D.

(*****************************************************************************)
(** More proof of Desargues in 2D **)


Section s_desargues2DMore.

Context `{RPSOH : RankProjectiveSpaceOrHigher}.
Context `{EP : EqDecidability Point}.

Lemma new_scheme : forall
(A' : Point)
(B' : Point)
(C' : Point)
(A : Point)
(B : Point)
(C : Point)
(O : Point)
(rABC : rk (triple A B C) = 3)
(rA'B'C' : rk (triple A' B' C') = 3)
(rABO : rk (triple A B O) = 3)
(rACO : rk (triple A C O) = 3)

(rBB'O : rk (triple B B' O) = 2)
(rCC'O : rk (triple C C' O) = 2)

(alpha : Point)
(beta : Point)
(gamma : Point)
(rABgamma : rk (triple A B gamma) = 2)
(rA'B'gamma : rk (triple A' B' gamma) = 2)
(rACbeta : rk (triple A C beta) = 2)
(rA'C'beta : rk (triple A' C' beta) = 2)
(rBCalpha : rk (triple B C alpha) = 2)

(H : A' [==] O), rk (triple alpha beta gamma) <= 2. 
Proof.
intros.
rewrite H0 in *;clear H0.

assert (rk(couple B gamma)=1).
eapply (uniq_inter A B O B'). 
eapply rk_triple_ABC_couple_AB; eassumption.
eapply rk_triple_ABC_couple_AB; eassumption.
setoid_replace (triple A B B) with (couple A B) by (clear_all;fsetdecide).
assert (rk(couple A B)=2).
eapply rk_triple_ABC_couple_AB; eassumption.
omega.
setoid_replace (triple O B' B) with (triple B B' O) by (clear_all;fsetdecide); omega.
omega.
omega.
assert (rk (quadruple A B O B') >=rk(triple A B O)).
apply matroid2; (clear_all;fsetdecide).
omega.

assert (rk(couple C beta)=1).
eapply (uniq_inter A C O C'). 
eapply rk_triple_ABC_couple_AB; eassumption.
eapply rk_triple_ABC_couple_AC; eassumption.
setoid_replace (triple A C C) with (couple A C) by (clear_all;fsetdecide).
assert (rk(couple A C)=2).
eapply rk_triple_ABC_couple_AC; eassumption.
omega.
setoid_replace (triple O C' C) with (triple C C' O) by (clear_all;fsetdecide); omega.
omega.
omega.
assert (rk (quadruple A C O C') >=rk(triple A C O)).
apply matroid2; (clear_all;fsetdecide).
omega.

rewrite <- (couple_rk2 B gamma) by assumption. 
rewrite <- (couple_rk2 C beta) by assumption.
setoid_replace (triple alpha C B) with (triple B C alpha) by (clear_all;fsetdecide); omega.
Qed.



Section s_desargues2DMore_theorem.

Variables A' B' C' : Point.
Variables A B C : Point.

Variables O : Point.

Variable rABC : rk(triple A B C)=3.
Variable rA'B'C' : rk(triple A' B' C')=3.
Variable rABCA'B'C'O : rk(union (triple A B C) (union (triple A' B' C') (singleton O)))=3.

Variable rABO : rk(triple A B O)=3.
Variable rACO :rk(triple A C O)=3.
Variable rBCO : rk (triple B C O)=3.

Variable rAA'O : rk(triple A A' O)=2.
Variable rBB'O : rk(triple B B' O)=2.
Variable rCC'O : rk(triple C C' O)=2.

Variable rAA' : rk(couple A A')=2.
Variable rBB' : rk(couple B B')=2.
Variable rCC' : rk(couple C C')=2.

Variables alpha beta gamma : Point.

Variable rABgamma : rk(triple A B gamma)=2.
Variable rA'B'gamma : rk(triple A' B' gamma)=2.

Variable rACbeta : rk(triple A C beta)=2.
Variable rA'C'beta : rk(triple A' C' beta)=2.

Variable rBCalpha : rk(triple B C alpha)=2.
Variable rB'C'alpha : rk(triple B' C' alpha) =2.


Lemma Desargues_plane : rk (triple alpha beta gamma) <= 2.
Proof.
elim (eq_dec A' O); intro HA'.
apply (new_scheme A' B' C' A B C O); auto.

elim (eq_dec B' O); intro HB'.
setoid_replace (triple alpha beta gamma) with (triple beta gamma alpha) by (clear_all;fsetdecide).
apply (new_scheme B' C' A' B C A O); try assumption.
setoid_replace (triple B C A) with (triple A B C) by (clear_all;fsetdecide); auto.
setoid_replace (triple B' C' A') with (triple A' B' C') by (clear_all;fsetdecide); auto.
setoid_replace (triple B A O) with (triple A B O) by (clear_all;fsetdecide); auto.
setoid_replace (triple B A gamma) with (triple A B gamma) by (clear_all;fsetdecide); auto.
setoid_replace (triple B' A' gamma) with (triple A' B' gamma) by (clear_all;fsetdecide); auto.
setoid_replace (triple C A beta) with (triple A C beta) by (clear_all;fsetdecide); auto.

elim (eq_dec C' O); intro HC'.
setoid_replace(triple alpha beta gamma) with (triple gamma beta alpha) by (clear_all;fsetdecide).
apply (new_scheme C' B' A' C B A O); try assumption.
setoid_replace (triple C B A) with (triple A B C) by (clear_all;fsetdecide); auto.
setoid_replace (triple C' B' A') with (triple A' B' C') by (clear_all;fsetdecide); auto.
setoid_replace (triple C B O) with (triple B C O) by (clear_all;fsetdecide); auto.
setoid_replace (triple C A O) with (triple A C O) by (clear_all;fsetdecide); auto.
setoid_replace (triple C B alpha) with (triple B C alpha) by (clear_all;fsetdecide); auto.
setoid_replace (triple C' B' alpha) with (triple B' C' alpha) by (clear_all;fsetdecide); auto.
setoid_replace (triple C A beta) with (triple A C beta) by (clear_all;fsetdecide); auto.
setoid_replace (triple C' A' beta) with (triple A' C' beta) by (clear_all;fsetdecide); auto.
setoid_replace (triple B A gamma) with (triple A B gamma) by (clear_all;fsetdecide); auto.

assert(HH := rk_couple1 A' O HA').
assert(HH0 := rk_couple1 B' O HB').
assert(HH1 := rk_couple1 C' O HC').
eapply (Desargues_plane A' B' C' A B C O); eauto.
Qed.

End s_desargues2DMore_theorem.

End s_desargues2DMore.