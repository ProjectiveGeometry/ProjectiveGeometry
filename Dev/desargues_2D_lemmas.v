Require Export ProjectiveGeometry.Dev.rank_space_or_higher_properties.

(*****************************************************************************)
(** Proof of 2D lemmas about Desargues **)


Section s_desargues2DLemmas.

Context `{RPSOH : RankProjectiveSpaceOrHigher}.
Context `{EP : EqDecidability Point}.

Lemma rABCO
     : forall A' B' C' A B C O : Point,
       rk (triple A B C) = 3 ->
       rk (union (triple A B C) (union (triple A' B' C') (singleton O))) = 3 ->
       rk (add O (triple A B C)) = 3.
Proof.
intros.
apply le_antisym.
assert (rk(add O (triple A B C))<=rk
                (union (triple A B C) (union (triple A' B' C') (singleton O)))).
apply matroid2; clear_all;fsetdecide.
omega.
assert (rk (add O (triple A B C))>=rk(triple A B C)).
apply matroid2; clear_all;fsetdecide.
omega.
Qed.

Lemma l1_scheme : forall A' B' : Point,
       forall A B : Point,
       forall O : Point,
       rk (triple A B O) = 3 ->
       rk (triple A A' O) = 2 ->
       rk (triple B B' O) = 2 ->
       rk (couple A' O) = 2 ->
       rk (couple B' O) = 2  ->  rk (triple A' B' O) = 3.
Proof.
intros A' B' A B O rABO rAA'O rBB'O rA'O rB'O.
apply le_antisym.
apply rk_triple_le.
assert (rk (union (couple A B) (triple A' B' O))>=3).
assert (Subset (triple A B O) (union (couple A B) (triple A' B' O))).
clear_all;fsetdecide.
generalize (matroid2 (triple A B O) (union (couple A B) (triple A' B' O)) H0).
intros Hsubset.
assert (Subset (triple A B O) (union (couple A B) (triple A' B' O))).
fsetdecide.
omega.
assert (rk(union (triple A A' B') (singleton O))>=3).
generalize (matroid3 (union (triple A A' B') (singleton O)) (triple B B' O)).
setoid_replace (union (union (triple A A' B') (singleton O)) (triple B B' O)) with
(union (couple A B) (triple A' B' O)) by (unfold Equal; split; clear_all;fsetdecide). 
rewrite rBB'O.
assert (rk(inter (union (triple A A' B') (singleton O)) (triple B B' O))>=rk (couple B' O)).
apply matroid2; clear_all;fsetdecide.
omega.
generalize (matroid3 (triple A' B' O) (triple A A' O)).
setoid_replace (union (triple A' B' O) (triple A A' O)) 
  with (union (triple A A' B') (singleton O)) by (clear_all;fsetdecide).
rewrite rAA'O.
assert (rk(inter (triple A' B' O) (triple A A' O))>=rk(couple A' O)).
apply matroid2; clear_all;fsetdecide.
omega.
Qed.

Lemma subl2rABMP_scheme
     : forall A' B' C' A B C O0 : Point,
       rk (union (triple A B C) (union (triple A' B' C') (singleton O0))) = 3 ->
       rk (triple A B O0) = 3 ->
       forall M : Point,
       M = C \/ M = A' \/ M = B' \/ M = C' ->
       rk (add M (triple A B O0)) = 3.
Proof.
intros A' B' C' A B C O rABCA'B'C'O rABO.
intros M0 HM0.
assert (rk(add M0 (triple A B O))=3).
assert (Hsubset:(Subset (add M0 (triple A B O))
   (union (triple A B C) (union (triple A' B' C') (singleton O))))).
decompose [or] HM0; subst; clear_all;fsetdecide.
generalize (matroid2 (add M0 (triple A B O )) (union (triple A B C) (union (triple A' B' C') (singleton O))) Hsubset).
rewrite rABCA'B'C'O.
assert (Hs2:(Subset (triple A B O) (add M0 (triple A B O)))).
clear_all;fsetdecide.
generalize (matroid2 (triple A B O) (add M0 (triple A B O )) Hs2).
rewrite rABO.
omega.
assumption.
Qed.

Lemma l2rABMP_scheme
     : forall A' B' C' A B C O0 : Point,
       rk (triple A B C) = 3 ->
       rk (union (triple A B C) (union (triple A' B' C') (singleton O0))) = 3 ->
       rk (triple A B O0) = 3 ->
       rk (triple A A' O0) = 2 ->
       rk (triple B B' O0) = 2 ->
       rk (couple A O0) = 2 ->
       rk (couple B O0) = 2 ->
       rk (couple A A') = 2 ->
       rk (couple B B') = 2 ->
       forall P : Point,
       rk (add P (triple A B O0)) >= 4 ->
       forall M : Point,
       M = C \/ M = A' \/ M = B' -> rk (add P (triple A B M)) >= 4.
Proof.
intros A' B' C' A B C O rABC rABCA'B'C'O rABO rAA'O rBB'O rAO rBO rAA' rBB' P rABOP.
intros M0 HM0.
assert (HM0':M0=C\/M0=A'\/M0=B'\/M0=C').
intuition.
generalize (subl2rABMP_scheme A' B' C' A B C O rABCA'B'C'O rABO M0 HM0'); intro hyp1; clear HM0'.
generalize (matroid3 (add P (triple A B M0)) (add M0 (triple A B O))).
setoid_replace (union (add P (triple A B M0)) (add M0 (triple A B O)))
with (union (triple A B M0) (couple O P)).
2:decompose [or] HM0.
2: rewrite H0 in *;clear H0;unfold Equal; split;clear_all;fsetdecide.
rewrite hyp1.
assert (rk(inter (add P (triple A B M0)) (add M0 (triple A B O)))>=rk(triple A B M0)).
apply matroid2; clear_all;fsetdecide.
assert (rk(union (triple A B M0) (couple O P))>=4).
assert (Hs:(Subset (add P (triple A B O)) (union (triple A B M0) (couple O P)))).
clear_all;fsetdecide.
generalize (matroid2 (add P (triple A B O)) (union (triple A B M0) (couple O P)) Hs).
omega.
assert (HABM:(rk(triple A B M0)=3)).
decompose [or] HM0.
rewrite H2 in *;clear H2.
intuition.
rewrite H3 in *;clear H3.
setoid_replace (triple A B A') with (triple A A' B) by (clear_all;fsetdecide).
apply (rk2_3 A A' O B).
setoid_replace (add B (triple A A' O)) with  (add A' (triple A B O)) by (clear HM0;clear_all;fsetdecide).
assumption.
apply rAA'O.
apply rAA'.
setoid_replace (couple O B) with (couple B O) by (clear_all;fsetdecide).
apply rBO.
rewrite H3 in *;clear H3.
setoid_replace (triple A B B') with (triple B B' A) by (clear_all;fsetdecide).
apply (rk2_3 B B' O A).
setoid_replace (add A (triple B B' O)) with  (add B' (triple A B O)) by (clear_all;fsetdecide).
assumption.
apply rBB'O.
apply rBB'.
setoid_replace (couple O A) with (couple A O) by (clear_all;fsetdecide).
apply rAO.
omega.
rewrite H1 in *;clear H1.
decompose [or] HM0; subst; unfold Equal; split; clear_all;fsetdecide.
rewrite H1 in *;clear H1.
unfold Equal; split; clear_all;fsetdecide.
Qed.

Lemma rABOo_scheme : 
       forall A B : Point,
       forall O P : Point,
       rk (add P (triple A B O)) >= 4 ->
       forall o : Point,
       rk (triple o O P) = 2 ->
       rk (couple O o) = 2 -> rk (add o (triple A B O)) >= 4.
Proof.
intros A B O P rABOP o roOP rOo.
generalize (matroid3 (add o (triple A B O)) (triple o O P)).
assert (rk(union (add o (triple A B O)) (triple o O P)) >= rk (add P (triple A B O))).
apply matroid2;clear_all;fsetdecide.
assert (rk (inter (add o (triple A B O)) (triple o O P))>=rk(couple O o)).
apply matroid2;clear_all;fsetdecide.
omega.
Qed.

Lemma rCC'oPc_scheme
     : forall A' B' C' A B C O : Point,
       rk (union (triple A B C) (union (triple A' B' C') (singleton O))) = 3 ->
       rk (couple C C') = 2 ->
       forall P : Point,
       rk (add P (triple A B O)) >= 4 ->
       forall o : Point,
       rk (triple o O P) = 2 ->
       rk (couple O o) = 2 ->
       forall c : Point,
       rk (triple o C c) = 2 ->
       rk (triple P C' c) = 2 -> rk (union (triple C C' o) (couple P c)) = 3.
Proof.
intros A' B' C' A B C O rABCA'B'C'O rCC' P rABOP o roOP rOo c roCc rPC'c.
apply le_antisym.
generalize (matroid3 (triple o C c) (triple P C' c)).
setoid_replace (union (triple o C c) (triple P C' c))
with (union (triple C C' o) (couple P c)) by (unfold Equal; split;clear_all;fsetdecide).
assert (rk(inter (triple o C c) (triple P C' c))>=rk(singleton c)).
apply matroid2;clear_all;fsetdecide.
rewrite rk_singleton in H0.
omega.
assert (rk(triple C C' o)>=3).
generalize (matroid3 (triple C C' o) (union (triple A B C) (couple C' O))).
assert (rk (inter (triple C C' o) (union (triple A B C) (couple C' O)))>=rk(couple C C')).
apply matroid2;clear_all;fsetdecide.
assert (rk(union (triple C C' o) (union (triple A B C) (couple C' O)))>=
rk(add o (triple  A B O))).
apply matroid2;clear_all;fsetdecide.
assert (rk(inter (triple C C' o) (union (triple A B C) (couple C' O)))>=rk(couple C C')).
apply matroid2;clear_all;fsetdecide.
generalize (rABOo_scheme A B O P rABOP o roOP rOo).
assert (rk(union(triple A B C) (couple C' O))<=3).
assert (rk (union (triple A B C) (union (triple A' B' C') (singleton O)))>=rk (union (triple A B C) (couple C' O))).
apply matroid2;clear_all;fsetdecide.
omega.
omega.
assert (rk (union (triple C C' o) (couple P c))>=rk(triple C C' o)).
apply matroid2;clear_all;fsetdecide.
omega.
Qed.

Lemma rCC'oc_scheme : forall A' B' C' A B C O : Point,
       rk (triple A B C) = 3 ->
       rk (union (triple A B C) (union (triple A' B' C') (singleton O))) = 3 ->
       rk (triple A C O) = 3 ->
       rk (triple C C' O) = 2 ->
       rk (couple C C') = 2 ->
       forall P : Point,
       rk (add P (triple A B O)) >= 4 ->
       forall o : Point,
       rk (triple o O P) = 2 ->
       rk (couple O o) = 2 ->
       forall c : Point,
       rk (triple o C c) = 2 ->
       rk (triple P C' c) = 2 -> rk (add c (triple C C' o)) = 3.
Proof.
intros A' B' C' A B C O rABC rABCA'B'C'O rACO rCC'O rCC' P rABOP o roOP rOo c roCc rPC'c.
apply le_antisym.
assert (rk(union (triple C C' o) (couple P c))>=rk(add c (triple C C' o))).
apply matroid2;clear_all;fsetdecide.
generalize (rCC'oPc_scheme A' B' C' A B C O rABCA'B'C'O rCC' P rABOP o roOP rOo c roCc rPC'c).
omega.
assert (rk(union (triple A C C') (couple O o))>=4).
generalize (matroid3 (union (triple A C C') (couple O o)) (add O (triple A B C))).
assert (rk(union (triple A B C) (triple O C' o))>=4).
assert (rk(union (triple A B C) (triple O C' o))>=(rk(add o (triple A B O)))).
apply matroid2;clear_all;fsetdecide.
generalize (rABOo_scheme A B O P rABOP o roOP rOo).
omega.
setoid_replace (union (union (triple A C C') (couple O o)) (add O (triple A B C)))
with (union (triple A B C) (triple O C' o)) by (unfold Equal; split;clear_all;fsetdecide).
assert (rk (inter (union (triple A C C') (couple O o))
     (add O (triple A B C)))>=rk(triple A C O)).
apply matroid2;clear_all;fsetdecide.
generalize (rABCO A' B' C' A B C O rABC rABCA'B'C'O) ; intro.
omega.
assert (rk(add o (triple A C C'))>=4).
generalize (matroid3 (add o (triple A C C')) (triple C C' O)).
setoid_replace (union (add o (triple A C C')) (triple C C' O)) with
(union (triple A C C') (couple O o)) by (unfold Equal; split;clear_all;fsetdecide).
assert (rk  (inter (add o (triple A C C')) (triple C C' O)) >= rk(couple C C')).
apply matroid2;clear_all;fsetdecide.
omega.
setoid_replace (add o (triple A C C')) with (add A (triple C C' o)) 
in H1 by (clear_all;fsetdecide).
generalize (rk_quadruple_ABCD_triple_ABC C C' o A H1).
intros rcC'o.
assert (rk(triple C C' o)<=rk (add c (triple C C' o))).
apply matroid2;clear_all;fsetdecide.
omega.
Qed.

Lemma rcC'_scheme
     : forall A' B' C' A B C O : Point,
       rk (triple A B C) = 3 ->
       rk (union (triple A B C) (union (triple A' B' C') (singleton O))) = 3 ->
       rk (triple A C O) = 3 ->
       rk (triple C C' O) = 2 ->
       rk (couple C C') = 2 ->
       forall P : Point,
       rk (add P (triple A B O)) >= 4 ->
       forall o : Point,
       rk (triple o O P) = 2 ->
       rk (couple O o) = 2 ->
       forall c : Point,
       rk (triple o C c) = 2 ->
       rk (triple P C' c) = 2 -> rk (couple c C') = 2.
Proof.
intros A' B' C' A B C O rABC rABCA'B'C'O rACO rCC'O rCC' P rABOP o roOP rOo c roCc rPC'c.
apply le_antisym.
apply rk_couple_2.
generalize (matroid3 (couple c C') (triple o C c)).
setoid_replace (union (couple c C') (triple o C c)) with (add c (triple C C' o)) by (clear_all;fsetdecide).
assert (rk(inter (couple c C') (triple o C c))>=rk(singleton c)).
apply matroid2;clear_all;fsetdecide.
rewrite rk_singleton in H0.
generalize (rCC'oc_scheme A' B' C' A B C O rABC rABCA'B'C'O rACO rCC'O rCC' P rABOP o roOP rOo c roCc rPC'c); omega.
Qed.

Lemma rcC_scheme
     : forall A' B' C' A B C O : Point,
       rk (triple A B C) = 3 ->
       rk (union (triple A B C) (union (triple A' B' C') (singleton O))) = 3 ->
       rk (couple C C') = 2 ->  rk (triple A C O) = 3 ->
       rk (triple C C' O) = 2 ->
       forall P : Point,
       rk (add P (triple A B O)) >= 4 ->
       forall o : Point,
       rk (triple o O P) = 2 ->
       rk (couple O o) = 2 ->
       forall c : Point, rk (triple o C c) = 2 ->rk (triple P C' c) = 2 -> rk (couple c C) = 2.
Proof.
intros A' B' C' A B C O rABC rABCA'B'C'O rCC' rACO rCC'O P rABOP o roOP rOo c roCc rPC'c.
apply le_antisym.
apply rk_couple_2.
assert (rk(add c (triple C C' P)) >=3).
generalize (matroid3 (add c (triple C C' P)) (add C' (triple A B C))).
assert (rk (inter (add c (triple C C' P)) (add C' (triple A B C))) >= rk (couple C C')).
apply matroid2;clear_all;fsetdecide.
setoid_replace (union (add c (triple C C' P)) (add C' (triple A B C))) with
(union (triple A B C) (triple C' P c)) by (unfold Equal; split;clear_all;fsetdecide).
assert (rk(add C' (triple A B C))<=3).
assert (rk(add C' (triple A B C))<=rk
                (union (triple A B C) (union (triple A' B' C') (singleton O)))).
apply matroid2;clear_all;fsetdecide.
omega.
assert (rk(union (triple A B C) (triple C' P c))>=4).
assert (rk (union (triple A B C) (triple C' P c)) >= rk (add P (triple A B C))).
apply matroid2;clear_all;fsetdecide.
assert (rk (add P (triple A B C)) >= 4).
setoid_replace (add P (triple A B C)) with (add P (triple C B A)) by (clear_all;fsetdecide).
apply (rk3_4 O B A C P).
apply le_antisym.
assert (rk(add C (triple O B A))<=rk
                (union (triple A B C) (union (triple A' B' C') (singleton O)))).
apply matroid2; clear_all;fsetdecide.
omega.
assert (rk (add C (triple O B A)) >= rk (triple A B C)).
apply matroid2; clear_all;fsetdecide.
omega.
setoid_replace (triple B A C) with (triple A B C) by clear_all;fsetdecide; assumption.
setoid_replace (triple O B A) with (triple A B O) by clear_all;fsetdecide;assumption.
omega.
omega.

generalize (rcC'_scheme A' B' C' A B C O rABC rABCA'B'C'O rACO rCC'O rCC' P rABOP o roOP rOo c roCc rPC'c).
intro.
generalize (matroid3 (couple c C) (triple P  c C')).
assert (rk  (inter (couple c C) (triple P c C'))>=rk(singleton c)).
apply matroid2; clear_all;fsetdecide.
setoid_replace (union (couple c C) (triple P c C')) with (add c (triple C C' P)) by (clear_all;fsetdecide).
rewrite rk_singleton in H2.
setoid_replace (triple P C' c) with (triple P c C') in rPC'c by (clear_all;fsetdecide).
omega.
Qed.

Lemma rABCc_scheme
     : forall A' B' C' A B C O : Point,
       rk (triple A B C) = 3 ->
       rk (union (triple A B C) (union (triple A' B' C') (singleton O))) = 3 ->
       rk (triple A C O) = 3 ->
       rk (triple C C' O) = 2 ->
       rk (couple C C') = 2 ->
       forall P : Point,
       rk (add P (triple A B O)) >= 4 ->
       forall o : Point,
       rk (triple o O P) = 2 ->
       rk (couple O o) = 2 ->
       forall c : Point,
       rk (triple o C c) = 2 ->
       rk (triple P C' c) = 2 -> 
       rk(add o (triple A B C))>=4 -> 
       rk (add c (triple A B C)) >= 4.
Proof.
intros A' B' C' A B C O rABC rABCA'B'C'O rACO rCC'O rCC' P rABOP o roOP rOo c roCc rPC'c rABCo.
generalize (matroid3 (add c (triple A B C)) (triple c C o)).
generalize rABCo; intro.
assert (rk (union (add c (triple A B C)) (triple c C o)) >= rk(add o (triple A B C))).
apply matroid2;(clear_all;fsetdecide).
assert (rk(inter (add  c (triple A B C)) (triple c C o))>=rk(couple c C)).
apply matroid2;(clear_all;fsetdecide).
generalize (rcC_scheme A' B' C' A B C O rABC rABCA'B'C'O rCC' rACO rCC'O P rABOP o roOP rOo c roCc rPC'c ); intro.
setoid_replace (triple o C c) with (triple c C o) in roCc by (clear_all;fsetdecide).
omega.
Qed.

Lemma rABOc_scheme
     : forall A' B' C' A B C O: Point,
       rk (triple A B C) = 3 ->
       rk (union (triple A B C) (union (triple A' B' C') (singleton O))) = 3 ->
       rk (triple A B O) = 3 ->
       rk (triple A C O) = 3 ->
       rk (triple C C' O) = 2 ->
       rk (couple C C') = 2 ->
       forall P : Point,
       rk (add P (triple A B O)) >= 4 ->
       forall o : Point,
       rk (triple o O P) = 2 ->
       rk (couple O o) = 2 ->
       forall c : Point,
       rk (triple o C c) = 2 ->
       rk (triple P C' c) = 2 -> 
       rk(add o (triple A B C))>=4 ->
       rk (add c (triple A B O)) >= 4.
Proof.
intros A' B' C' A B C O rABC rABCA'B'C'O rABO rACO rCC'O rCC' P rABOP o roOP rOo c roCc rPC'c rABCo.
setoid_replace (triple A B O) with (triple O B A) by (clear_all;fsetdecide).
apply (rk3_4  C B A O c).
apply le_antisym.
assert (rk(add O (triple C B A)) <= rk
                (union (triple A B C) (union (triple A' B' C') (singleton O)))).
apply matroid2; (clear_all;fsetdecide).
omega.
assert (rk (add  O (triple C B A)) >= rk(triple A B C)).
apply matroid2; (clear_all;fsetdecide).
omega.
setoid_replace (triple B A O) with (triple A B O) by (clear_all;fsetdecide).
assumption.
setoid_replace (triple C B A) with (triple A B C) by (clear_all;fsetdecide).
eapply rABCc_scheme; eauto.
Qed.

Lemma rPcC'oO_scheme
     : forall A' B' C' A B C O : Point,
       rk (triple A' B' C') = 3 ->
       rk (union (triple A B C) (union (triple A' B' C') (singleton O))) = 3 ->
       rk (triple A C O) = 3 ->
       rk (triple A A' O) = 2 ->
       rk (triple B B' O) = 2 ->
       rk (triple C C' O) = 2 ->
       rk (couple A' O) = 2 ->
       rk (couple B' O) = 2 ->
       rk (couple C' O) = 2 ->
       forall P : Point,
       rk (add P (triple A B O)) >= 4 ->
       forall o : Point,
       rk (triple o O P) = 2 ->
       forall c : Point,
       rk (triple P C' c) = 2 ->
       rk (add P (triple A' B' O)) >= 4 -> 
       rk (union (triple P C' c) (couple o O)) = 3.
Proof.
intros A' B' C' A B C O rA'B'C' rABCA'B'C'O rACO rAA'O rBB'O rCC'O rA'O rB'O rC'O P rABOP o roOP c rPC'c l2rA'B'OP.
apply le_antisym.
generalize (matroid3 (triple P o O) (triple P C' c)).
setoid_replace (union (triple P o O) (triple P C' c)) with (union (triple P C' c) (couple o O))  by (unfold Equal; split; clear_all;fsetdecide).
assert (rk (inter (triple P o O) (triple P C' c ))>=rk(singleton P)).
apply matroid2;clear_all;fsetdecide.
assert (rk(triple P o O)<=2).
setoid_replace (triple P o O) with (triple o O P) by (clear_all;fsetdecide).
rewrite rk_singleton in H0.
omega.
rewrite rk_singleton in H0.
omega.
assert (rk(add P (triple A' C' O)) >= 4).
assert (rk(add P (triple A' B' O)) >= 4).
apply l2rA'B'OP.
setoid_replace (triple A' C' O) with (triple C' A' O) by (clear_all;fsetdecide).
apply (rk3_4 B' A' O C' P).
apply le_antisym.
assert (rk (add C' (triple B' A' O))<=rk
                (union (triple A B C) (union (triple A' B' C') (singleton O)))).
apply matroid2;clear_all;fsetdecide.
omega.
assert (rk (add C' (triple B' A' O)) >= rk(triple A' B' C')).
apply matroid2; clear_all;fsetdecide.
omega.
setoid_replace (triple A' O C') with (triple A' C' O) by (clear_all;fsetdecide).
eapply l1_scheme with (A:=A) (B:=C); auto.
setoid_replace (triple B' A' O) with (triple A' B' O) by (clear_all;fsetdecide).
assumption.
assert (rk(triple C' O P) =3).
apply (rk_quadruple_ABCD_triple_ABC C' O P A').
setoid_replace (add  A' (triple C' O P)) with (add P (triple A' C' O)) by (clear_all;fsetdecide).
assumption.
assert (rk (triple C' O P)<=rk (union (triple P C' c) (couple o O))).
apply matroid2;clear_all;fsetdecide.
omega.
Qed.

Lemma rPC'oc_scheme
     : forall A' B' C' A B C O : Point,
       rk (triple A' B' C') = 3 ->
       rk (union (triple A B C) (union (triple A' B' C') (singleton O))) = 3 ->
       rk (triple A C O) = 3 ->
       rk (triple A A' O) = 2 ->
       rk (triple B B' O) = 2 ->
       rk (triple C C' O) = 2 ->
       rk (couple A' O) = 2 ->
       rk (couple B' O) = 2 ->
       rk (couple C' O) = 2 ->
       rk (couple C C') = 2 ->
       forall P : Point,
       rk (add P (triple A B O)) >= 4 ->
       forall o : Point,
       rk (triple o O P) = 2 ->
       rk (couple O o) = 2 ->
       rk (couple P o) = 2 ->
       forall c : Point,
       rk (triple o C c) = 2 ->
       rk (triple P C' c) = 2 -> 
       rk (add P (triple A' B' O)) >= 4 -> 
       rk (add c (triple P C' o)) = 3.
Proof.
intros A' B' C' A B C O rA'B'C' rABCA'B'C'O rACO rAA'O rBB'O rCC'O rA'O rB'O rC'O rCC' P rABOP o roOP rOo rPo c roCc rPC'c rA'B'OP.
apply le_antisym.
assert (rk (add c (triple P C' o)) <= rk(union (triple C C' o) (couple P c))).
apply matroid2;clear_all;fsetdecide.
generalize (rCC'oPc_scheme A' B' C' A  B C O rABCA'B'C'O rCC' P rABOP o roOP rOo c roCc rPC'c); omega.
generalize (matroid3 (add c (triple P C' o)) (triple P o O)).
assert (rk (inter (add c (triple P C' o)) (triple P o O))>=rk(couple P o)).
apply matroid2;clear_all;fsetdecide.
setoid_replace (union (add c (triple P C' o)) (triple P o O)) with 
(union (triple P C' c) (couple o O)) by (unfold Equal; intros;split;clear_all;fsetdecide). 
generalize (rPcC'oO_scheme A' B' C' A  B C O rA'B'C' rABCA'B'C'O rACO rAA'O rBB'O rCC'O rA'O rB'O rC'O P rABOP o roOP c rPC'c rA'B'OP).
setoid_replace (triple o O P)  with (triple P o O) in roOP by (clear_all;fsetdecide); omega.
Qed.

Lemma rco_scheme
     : forall A' B' C' A B C O : Point,
       rk (triple A' B' C') = 3 ->
       rk (union (triple A B C) (union (triple A' B' C') (singleton O))) = 3 ->
       rk (triple A C O) = 3 ->
       rk (triple A A' O) = 2 ->
       rk (triple B B' O) = 2 ->
       rk (triple C C' O) = 2 ->
       rk (couple A' O) = 2 ->
       rk (couple B' O) = 2 ->
       rk (couple C' O) = 2 ->
       rk (couple C C') = 2 ->
       forall P : Point,
       rk (add P (triple A B O)) >= 4 ->
       forall o : Point,
       rk (triple o O P) = 2 ->
       rk (couple O o) = 2 ->
       rk (couple P o) = 2 ->
       forall c : Point,
       rk (triple o C c) = 2 ->
       rk (triple P C' c) = 2 -> 
       rk (add P (triple A' B' O)) >= 4 ->
       rk (couple c o) = 2.
Proof.
intros A' B' C' A B C O rA'B'C' rABCA'B'C'O rACO rAA'O rBB'O rCC'O rA'O rB'O rC'O rCC' P rABOP o roOP rOo rPo c roCc rPC'c rA'B'OP.
apply le_antisym.
apply rk_couple_2.
generalize (matroid3 (couple c o) (triple c C' P)).
assert (rk(inter (couple c o) (triple c C' P))>=rk(singleton c)).
apply matroid2;clear_all;fsetdecide.
rewrite rk_singleton in H0.
setoid_replace (union (couple c o) (triple c C' P)) with (add c (triple P C' o)) by (clear_all;fsetdecide).
rewrite (rPC'oc_scheme A' B' C' A B C O rA'B'C' rABCA'B'C'O rACO rAA'O rBB'O rCC'O rA'O rB'O rC'O rCC' P rABOP o roOP rOo rPo c roCc rPC'c rA'B'OP). 
setoid_replace (triple P C' c) with (triple c C' P) in rPC'c by (clear_all;fsetdecide).
omega.
Qed.

End s_desargues2DLemmas.