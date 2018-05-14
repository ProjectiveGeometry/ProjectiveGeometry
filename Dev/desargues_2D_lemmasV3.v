Require Export ProjectiveGeometry.Dev.desargues_2D_lemmasV2.

(*****************************************************************************)
(** Proof of 2D lemmas V3 about Desargues **)


Section s_desargues2DLemmasV3.

Context `{RPSOH : RankProjectiveSpaceOrHigher}.
Context `{EP : EqDecidability Point}.

Lemma beta_ok' : forall 
(A' : Point)
(B' : Point)
(C' : Point)
(A : Point)
(B : Point)
(C : Point)
(O : Point)
(rABC : rk (triple A B C) = 3)
(rA'B'C' : rk (triple A' B' C') = 3)
(rABCA'B'C'O : rk
                (union (triple A B C) (union (triple A' B' C') (singleton O))) =
              3)
(rABO : rk (triple A B O) = 3)
(rACO : rk (triple A C O) = 3)
(rBCO : rk (triple B C O) = 3)
(rA'B'O' : rk (triple A' B' O) = 3)
(rA'C'O' : rk (triple A' C' O) = 3)
(rB'C'O' : rk (triple B' C' O) = 3)
(rAA'O : rk (triple A A' O) = 2)
(rBB'O : rk (triple B B' O) = 2)
(rCC'O : rk (triple C C' O) = 2)
(rAA' : rk (couple A A') = 2)
(rBB' : rk (couple B B') = 2)
(rCC' : rk (couple C C') = 2)
(P : Point)
(rABOP : rk (add P (triple A B O)) >= 4)
(rOP : rk (couple O P) = 2)
(o : Point)
(rko1 : rk (triple o O P) = 2)
(rko2 : rk (couple O o) = 2)
(rko3 : rk (couple P o) = 2)
(alpha : Point)
(beta : Point)
(gamma : Point)
(rABgamma : rk (triple A B gamma) = 2)
(rA'B'gamma : rk (triple A' B' gamma) = 2)
(rACbeta : rk (triple A C beta) = 2)
(rA'C'beta : rk (triple A' C' beta) = 2)
(rBCalpha : rk (triple B C alpha) = 2)
(rB'C'alpha : rk (triple B' C' alpha) = 2)
(a : Point)

(Ha2 : rk (triple o A a) = 2)
(Ha2' : rk (triple P A' a) = 2)
(b : Point)
(Hb2 : rk (triple o B b) = 2)
(Hb2' : rk (triple P B' b) = 2)
(c : Point)
(Hc2 : rk (triple o C c) = 2)
(Hc2' : rk (triple P C' c) = 2)
(rabc3 : rk (triple a b c) = 3), 
rk (triple a c beta) = 2.
Proof.
intros.
assert (rk(union (triple a c A) (couple C beta))=3).
assert (rk(add c (triple A C a)) = 3).
apply le_antisym.
assert(rk(union (triple A C a) (couple c o))<=3).
generalize (matroid3 (triple o A a) (triple o C c)).
setoid_replace (union (triple o A a) (triple o C c)) with (union (triple A C a) (couple c o)) by (unfold Equal; split;(clear_all;fsetdecide)).
assert (rk (inter (triple o A a) (triple o C c)) >= rk(singleton o)).
apply matroid2;(clear_all;fsetdecide).
rewrite rk_singleton in H0.
omega.
assert (rk (add c (triple A C a))<=rk (union (triple A C a) (couple c o))).
apply matroid2;(clear_all;fsetdecide).
omega.
generalize (matroid3 (add c (triple A C a)) (triple P A' a)).
assert (rk(union (add c (triple A C a)) (triple P A' a))>=rk(add P (triple A A' C))).
apply matroid2;(clear_all;fsetdecide).
assert (rk(add P (triple A A' C))>=4).
setoid_replace (triple A A' C)  with (triple A C A') by (clear_all;fsetdecide).
apply (l2rABMP_scheme  A' C' B' A C B O).
setoid_replace (triple A C B) with (triple A B C) by (clear_all;fsetdecide); assumption.
setoid_replace (triple A C B) with (triple A B C) by (clear_all;fsetdecide).
setoid_replace (triple A' C' B') with (triple A' B' C') by (clear_all;fsetdecide); assumption.
assumption.
assumption.
assumption.
eapply rAO;eassumption.
eapply rCO; eassumption.
assumption.
assumption.
eapply rACOP with (B0:=B) (A'0:=A') (B'0:=B') (C'0:=C'); try eassumption.
solve [intuition].
assert (rk (inter (add c (triple A C a)) (triple P A' a)) >= rk(singleton a)).
apply matroid2;(clear_all;fsetdecide).
rewrite rk_singleton in H2.
omega.
apply le_antisym.
generalize (matroid3 (add c (triple A C a)) (triple A C beta)).
assert (rk(inter (add c (triple A C a)) (triple A C beta))>=rk(couple A C)).
apply matroid2;(clear_all;fsetdecide).
setoid_replace (union (add c (triple A C a)) (triple A C beta)) with (union (triple a c A) (couple C beta)) by (unfold Equal; split;(clear_all;fsetdecide)).
assert (rk(couple A C)=2).
apply (rk_triple_ABC_couple_AC A B C rABC).
omega.
assert (rk (add c (triple A C a)) <=rk (union (triple a c A) (couple C beta))).
apply matroid2;(clear_all;fsetdecide).
omega.

assert(rk(union (triple a c A') (couple C' beta))=3).
assert (rk(add c (triple A' C' a)) = 3).
apply le_antisym.
assert(rk(union (triple A' C' a) (couple c P))<=3).
generalize (matroid3 (triple P A' a) (triple P C' c)).
setoid_replace (union (triple P A' a) (triple P C' c)) with (union (triple A' C' a) (couple c P)) by (unfold Equal; split;(clear_all;fsetdecide)).
assert (rk (inter (triple P A' a) (triple P C' c)) >= rk(singleton P)).
apply matroid2;(clear_all;fsetdecide).
rewrite rk_singleton in H1.
omega.
assert (rk (add c (triple A' C' a))<=rk (union (triple A' C' a) (couple c P)) ).
apply matroid2;(clear_all;fsetdecide).
omega.
generalize (matroid3 (add c (triple A' C' a)) (triple o A a)).
assert (rk(union (add c (triple A' C' a)) (triple o A a))>=rk(add o (triple A' A C'))).
apply matroid2; (clear_all;fsetdecide).
assert (rk(add o (triple A' A C'))>=4).
setoid_replace (triple A' A C')  with  (triple A' C' A) by (clear_all;fsetdecide).
eapply (rA'C'Mo A' B' C' A B C);try eassumption || intuition.
assert (rk (inter (add c (triple A' C' a)) (triple o A a)) >= rk(singleton a)).
apply matroid2; (clear_all;fsetdecide).
rewrite rk_singleton in H3.
omega.
apply le_antisym.
generalize (matroid3 (add c (triple A' C' a)) (triple A' C' beta)).
assert (rk(inter (add c (triple A' C' a)) (triple A' C' beta))>=rk(couple A' C')).
apply matroid2; (clear_all;fsetdecide).
setoid_replace (union (add c (triple A' C' a)) (triple A' C' beta)) with (union (triple a c A') (couple C' beta)) by (unfold Equal; split; (clear_all;fsetdecide)).
assert (rk(couple A' C')=2).
apply (rk_triple_ABC_couple_AC A' B' C' rA'B'C').
omega.
assert (rk (add c (triple A' C' a)) <=rk (union (triple a c A') (couple C' beta))).
apply matroid2; (clear_all;fsetdecide).
omega.

generalize (matroid3 (union (triple a c A)(couple  C beta)) (union (triple a c A')  (couple C' beta))).
assert (rk (inter (union (triple a c A) (couple C beta)) (union (triple a c A') (couple C' beta)))>=rk(triple a c beta)).
apply matroid2; (clear_all;fsetdecide).
assert (rk
  (union (union (triple a c A) (couple C beta))
     (union (triple a c A') (couple C' beta)))>=4).
assert (rk(add a (triple A A' C))>=4).
generalize (rABCa A' B' C' A B C O rABC rA'B'C' rABCA'B'C'O 
            rABO rACO rBCO rA'B'O' rA'C'O' rB'C'O' rAA'O rBB'O rCC'O rAA' 
            rBB' rCC' P rABOP rOP o rko1 rko2  rko3 a Ha2 Ha2'); intros rABCa'.
setoid_replace (triple A A' C) with (triple A' A C) by (clear_all;fsetdecide). 
apply (rk3_4 B A C A' a).
apply le_antisym.
rewrite <- rABCA'B'C'O.
apply matroid2;(clear_all;fsetdecide).
rewrite <- rABC.
apply matroid2;(clear_all;fsetdecide).
apply le_antisym.
rewrite <- rABCA'B'C'O.
apply matroid2;(clear_all;fsetdecide).
generalize (matroid3 (triple A A' O) (triple A C A')).
assert (rk (union (triple A A' O) (triple A C A'))>=rk(triple A C O)).
apply matroid2;(clear_all;fsetdecide). 
assert (rk (inter (triple A A' O) (triple A C A')) >= rk (couple A A')).
apply matroid2;(clear_all;fsetdecide).
omega.
setoid_replace (triple B A C) with  (triple A B C) by (clear_all;fsetdecide); assumption.
assert (rk
  (union (union (triple a c A) (couple C beta))
     (union (triple a c A') (couple C' beta)))>=rk(add a (triple A A' C))).
apply matroid2;(clear_all;fsetdecide).
intros;omega.
assert (rk(couple a c)=2).
eapply rk_triple_ABC_couple_AC; eassumption.
assert (rk(triple a c beta)>=rk(couple a c)).
apply matroid2;(clear_all;fsetdecide).
omega.
Qed.

End s_desargues2DLemmasV3.