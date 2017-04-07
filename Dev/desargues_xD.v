Require Export ProjectiveGeometry.Dev.desargues_2D_more.
Require Export ProjectiveGeometry.Dev.desargues_3D_special.

(*****************************************************************************)
(** Proof of Desargues in xD **)


Section s_desarguesxD.

Context `{RPSOH : RankProjectiveSpaceOrHigher}.
Context `{EP : EqDecidability Point}.


Section s_desarguesxD_theorem.

Variables A' B' C' : Point.
Variables A B C : Point.

Variables O : Point.

Variable rABC : rk(triple A B C)=3.
Variable rA'B'C' : rk(triple A' B' C')=3.

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

Lemma Desargues_xD : rk (triple alpha beta gamma) <= 2.
Proof.
assert  (rk(union (triple A B C) (triple A' B' C'))=3 \/
rk(union (triple A B C) (triple A' B' C'))>=4).
assert (rk(union (triple A B C) (triple A' B' C'))>=3).
rewrite <- rABC.
apply matroid2; (clear_all;fsetdecide).
omega. 
elim H0.
intro rABCA'B'C'.
assert (rk(union (triple A B C) (union (triple A' B' C') (singleton O)))=3 ).
clear H0.
apply le_antisym.
setoid_replace (union (triple A B C) (union (triple A' B' C') (singleton O))) with
(add O (union (triple A B C) (triple A' B' C'))) by (clear_all;fsetdecide).
apply (stays_in_plane (union (triple A B C) (triple A' B' C')) A A' O); auto.
omega.
(clear_all;fsetdecide).
(clear_all;fsetdecide).
rewrite <- rABC.
apply matroid2;(clear_all;fsetdecide).
rename H1 into rABCA'B'C'O.

eapply (Desargues_plane A' B' C' A B C O);assumption.

intro.
eapply (Desargues A B C A' B' C' alpha beta gamma O); auto.
setoid_replace (union (triple A' B' C') (triple A B C)) with (union (triple A B C) (triple A' B' C')) by (unfold Equal; split;(clear_all;fsetdecide)).
omega.
Qed.

End s_desarguesxD_theorem.


Lemma Desargues_xD'
     : forall A' B' C' A B C O0 : Point,
       rk (triple A B C) = 3 ->
       rk (triple A' B' C') = 3 ->
       rk (triple A B O0) = 3 ->
       rk (triple A C O0) = 3 ->
       rk (triple B C O0) = 3 ->
       rk (triple A A' O0) = 2 ->
       rk (triple B B' O0) = 2 ->
       rk (triple C C' O0) = 2 ->
       rk (couple A A') = 2 ->
       rk (couple B B') = 2 ->
       rk (couple C C') = 2 ->
       forall alpha beta gamma : Point,
       rk (triple A B gamma) = 2 ->
       rk (triple A' B' gamma) = 2 ->
       rk (triple A C beta) = 2 ->
       rk (triple A' C' beta) = 2 ->
       rk (triple B C alpha) = 2 ->
       rk (triple B' C' alpha) = 2 -> rk (triple alpha beta gamma) <= 2.
exact Desargues_xD.
Qed.

End s_desarguesxD.
