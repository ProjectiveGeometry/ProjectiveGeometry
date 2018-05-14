Require Export ProjectiveGeometry.Dev.rank_space_or_higher_properties.

(*****************************************************************************)
(** Proof of 3D lemmas about Desargues **)

Ltac my_classical_left :=
match goal with
| H : _ |- _ \/ ?c = ?d => destruct (Nat.eq_dec c d); [right; assumption | left]
end.

Section s_desargues3DLemmas.

Context `{RPSOH : RankProjectiveSpaceOrHigher}.
Context `{EP : EqDecidability Point}.

Lemma rbA_scheme
     : forall a b c A B C alpha : Point,
       forall gamma O0 : Point,
       rk (triple a A O0) = 2 ->
       rk (triple b B O0) = 2 ->
       rk (triple c C O0) = 2 ->
       rk (triple a b c) = 3 ->
       rk (union (triple A B C) (triple a b c)) >= 4 ->
       rk (triple a b gamma) = 2 ->
       rk (triple b c alpha) = 2 ->
       rk (couple A O0) = 2 -> rk (couple b A) = 2.
intros a b c A B C alpha gamma O raAO rbBO rcCO rabc rABCabc rabgamma rbcalpha rAO.
apply rk_couple1.
intros HbA.
assert (rk(union (triple A B C) (triple a b c))<=3).
assert (rk(add O (union (triple A a B) (triple b C c)))<=3).
assert (rk(union(triple A a B) (couple b O))<=2).
generalize (matroid3 (triple a A O) (triple B b O)).
setoid_replace (union (triple a A O) (triple B b O)) 
                 with (union (triple A a B) (couple b O)) 
                 by (unfold Equal; split; clear_all;fsetdecide).
rewrite HbA in *.
rewrite raAO.
setoid_replace (triple A B O) with (triple B A O) in rbBO by (clear_all;fsetdecide).
rewrite rbBO.
assert (rk(inter (triple a A O) (triple B A O))>=rk(couple A O)).
apply matroid2.
fsetdecide.
rewrite rAO in H0.
omega.
generalize (matroid3 (union(triple A a B) (couple b O)) (triple c C O)).
setoid_replace (union (union (triple A a B) (couple b O)) (triple c C O))
with (add O (union (triple A a B) (triple b C c))) by (clear_all;fsetdecide).
rewrite rcCO.
assert (rk(inter (union (triple A a B) (couple b O)) (triple c C O))>=rk(singleton O)).
apply matroid2;clear_all;fsetdecide.
rewrite rk_singleton in H1.
omega.
assert (rk(union (triple A B C) (triple a b c))<=rk(add O (union (triple  A a B) (triple b C c)))).
apply matroid2;clear_all;fsetdecide.
omega.
omega.
Qed.

Lemma sublemma : forall
(b : Point)
(c : Point)
(A : Point)
(B : Point)
(C : Point)
(alpha : Point)
(beta : Point)
(gamma : Point)
(O : Point)
(rbBO : rk (triple b B O) = 2)
(rcCO : rk (triple c C O) = 2)
(rABC : rk (triple A B C) = 3)
(rABgamma : rk (triple A B gamma) = 2)
(rACbeta : rk (triple A C beta) = 2)
(rBCalpha : rk (triple B C alpha) = 2)
(rbcalpha : rk (triple b c alpha) = 2)
(rAO : rk (couple A O) = 2)
(rBO : rk (couple B O) = 2)
(rCO : rk (couple C O) = 2)
(raAO : rk (triple A A O) = 2)
(rabc : rk (triple A b c) = 3)
(rABCabc : rk (union (triple A B C) (triple A b c)) >= 4)
(rabgamma : rk (triple A b gamma) = 2)
(racbeta : rk (triple A c beta) = 2)
(rcC : rk (couple c C) = 2),
rk (couple A beta) = 1.
Proof.
intros.
eapply (uniq_inter A c A C) with (P:=A) (Q:=beta); try eassumption.
setoid_replace (couple A c) with (couple c A) by (clear_all;fsetdecide).
eapply (rbA_scheme A c b A C B alpha beta O); try eassumption.
setoid_replace (triple A c b) with (triple A b c) by (clear_all;fsetdecide); assumption.
setoid_replace (triple A C B) with (triple A B C) by (clear_all;fsetdecide).
setoid_replace (triple A c b) with (triple A b c) by (clear_all;fsetdecide); assumption.
setoid_replace (triple c b alpha) with (triple b c alpha) by (clear_all;fsetdecide); assumption.
eapply rk_triple_ABC_couple_AC; eassumption.
setoid_replace (triple A c A) with (couple c A) by (clear_all;fsetdecide).
assert (rk (couple c A)=2).
eapply (rbA_scheme A c b A C B alpha); try eassumption.
setoid_replace (triple A c b) with (triple A b c) by (clear_all;fsetdecide); assumption.
setoid_replace (triple A C B) with (triple A B C) by (clear_all;fsetdecide).
setoid_replace (triple A c b) with (triple A b c) by (clear_all;fsetdecide); assumption.
setoid_replace (triple c b alpha) with (triple b c alpha) by (clear_all;fsetdecide); assumption. 
omega.
setoid_replace (triple A C A) with (couple A C) by (clear_all;fsetdecide).
assert (rk(couple A C)=2).
eapply rk_triple_ABC_couple_AC; eassumption.
omega.
omega.
omega.
setoid_replace (quadruple A c A C) with (triple A c C) by (clear_all;fsetdecide).
assert (rk (union (triple A C c) (couple O beta))>=3).
generalize (matroid3 (union (triple A C c) (couple O beta)) (triple b B O)).
assert (rk (union (union (triple A C c) (couple O beta)) (triple b B O)) >= rk (union (triple A B C) (triple A b c))).
apply matroid2; (clear_all;fsetdecide).
assert (rk (inter (union (triple A C c) (couple O beta)) (triple b B O))>= rk (singleton O)).
apply matroid2; (clear_all;fsetdecide).
rewrite rk_singleton in H1.
omega.
assert (rk (add beta (triple A c C))>=3).
generalize (matroid3 (add beta (triple A c C)) (triple c C O)).
assert (rk (union (add beta (triple A c C)) (triple c C O)) >= rk (union (triple A C c) (couple O beta)) ).
apply matroid2; (clear_all;fsetdecide).
assert (rk (inter (add  beta (triple A c C)) (triple c C O))>=rk(couple c C)).
apply matroid2; (clear_all;fsetdecide).
omega.
generalize (matroid3 (triple A c C) (triple A c beta)).
assert (rk (union (triple A c C) (triple A c beta)) >=rk(add beta (triple A c C))).
apply matroid2; (clear_all;fsetdecide).
assert (rk  (inter (triple A c C) (triple A c beta)) >= rk (couple c A)).
apply matroid2; (clear_all;fsetdecide).
assert (Hrew:(rk(couple c A)=2)).
apply (rbA_scheme A c b A C B alpha beta O).
setoid_replace (triple A A O) with (couple A O) by (clear_all;fsetdecide); assumption.
assumption.
assumption.
setoid_replace (triple A c b) with (triple A b c) by (clear_all;fsetdecide); assumption.
setoid_replace (triple A C B) with (triple A B C) by (clear_all;fsetdecide).
setoid_replace  (triple A c b)  with  (triple A b c)  by (clear_all;fsetdecide); assumption.
assumption.
setoid_replace (triple c b alpha) with (triple b c alpha) by (clear_all;fsetdecide); assumption.
assumption.
rewrite Hrew in H3 by assumption.
omega.
Qed.

Lemma sublemma'' : forall
(a : Point)
(b : Point)
(c : Point)
(A : Point)
(B : Point)
(C : Point)
(alpha : Point)
(beta : Point)
(gamma : Point)
(O : Point)
(raAO : rk (triple a A O) = 2)
(rbBO : rk (triple b B O) = 2)
(rcCO : rk (triple c C O) = 2)
(rABC : rk (triple A B C) = 3)
(rabc : rk (triple a b c) = 3)
(rABCabc : rk (union (triple A B C) (triple a b c)) >= 4)
(rABgamma : rk (triple A B gamma) = 2)
(rabgamma : rk (triple a b gamma) = 2)
(rACbeta : rk (triple A C beta) = 2)
(racbeta : rk (triple a c beta) = 2)
(rBCalpha : rk (triple B C alpha) = 2)
(rbcalpha : rk (triple b c alpha) = 2)
(rAO : rk (couple A O) = 2)
(rBO : rk (couple B O) = 2)
(rCO : rk (couple C O) = 2)
(a0 : a = A)
(a1 : c = C),
rk (couple A gamma) = 1.
Proof.
intros; subst.
eapply (uniq_inter A B A b) with (P:=A) (Q:=gamma).
apply (rk_triple_ABC_couple_AB A B C rABC).
setoid_replace (couple A b) with (couple b A) by (clear_all;fsetdecide).
apply (rbA_scheme A b C A B C alpha gamma O).
setoid_replace (triple A A O) with (couple A O) by (clear_all;fsetdecide); assumption.
assumption.
setoid_replace (triple C C O) with (couple C O) by (clear_all;fsetdecide); assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
setoid_replace (triple A B A) with (couple A B) by (clear_all;fsetdecide).
assert (rk (couple A B)=2).
eapply rk_triple_ABC_couple_AB; eassumption.
omega.
setoid_replace (triple A b A) with (couple b A) by (clear_all;fsetdecide).
assert (rk (couple b A) =2).
apply (rbA_scheme A b C A B C alpha gamma O).
setoid_replace (triple A A O) with (couple A O) by (clear_all;fsetdecide); assumption.
assumption.
setoid_replace (triple C C O) with (couple C O) by (clear_all;fsetdecide); assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
omega.
omega.
omega.

setoid_replace (quadruple A B A b) with (triple A B b) by (clear_all;fsetdecide).
generalize (matroid3 (triple A B b) (triple A B C)).
assert ( rk (union (triple A B C) (triple A b C)) <= rk (union (triple A B b) (triple A B C))).
apply matroid2; (clear_all;fsetdecide).
assert (rk (inter (triple A B b) (triple A B C))>= rk(couple A B)).
apply matroid2; (clear_all;fsetdecide).
assert (rk(couple A B)=2).
eapply rk_triple_ABC_couple_AB; eassumption.
rewrite H2 in H1.
omega.
Qed.

Lemma a_not_gamma_scheme : forall
(a : Point)
(b : Point)
(c : Point)
(A : Point)
(B : Point)
(C : Point)
(alpha : Point)
(beta : Point)
(gamma : Point)
(O : Point)
(raAO : rk (triple a A O) = 2)
(rbBO : rk (triple b B O) = 2)
(rcCO : rk (triple c C O) = 2)
(rABC : rk (triple A B C) = 3)
(rabc : rk (triple a b c) = 3)
(rABCabc : rk (union (triple A B C) (triple a b c)) >= 4)
(rABgamma : rk (triple A B gamma) = 2)
(rabgamma : rk (triple a b gamma) = 2)
(rACbeta : rk (triple A C beta) = 2)
(racbeta : rk (triple a c beta) = 2)
(rBCalpha : rk (triple B C alpha) = 2)
(rbcalpha : rk (triple b c alpha) = 2)
(raA : rk (couple a A) = 2)
(rcC : rk (couple c C) = 2)
(rbB : rk (couple b B) = 2),
rk (couple a gamma) = 2 \/ rk (triple gamma alpha beta) = 2.
Proof.
intros.
my_classical_left.
rename n into HnotDes.
apply rk_couple1.
intro.
rewrite H0 in *;clear H0.

assert (rk (couple gamma A) = 1 \/ rk (triple gamma B O) <= 2).
apply (uniq_inter_spec_bis A gamma B O).

setoid_replace (triple gamma B A) with (triple A B gamma) by (clear_all;fsetdecide);omega.
setoid_replace (triple gamma O A) with (triple gamma A O)   by (clear_all;fsetdecide);omega.
elim H0;intro;clear H0.
intuition.

elim (eq_dec B O);intro.
rewrite H0 in *; clear H0.

assert (   rk (union (triple c C O) (triple O C alpha)) + rk (couple O C) <=
       rk (triple c C O) + rk (triple O C alpha)).
apply (matroid3_useful); auto.
(clear_all;fsetdecide).
assert (rk (couple O C) = 2).
eapply (rk_triple_ABC_couple_BC);eauto.
assert ( rk (union (triple c C O) (triple O C alpha)) <= 2).
omega.

elim (eq_dec c alpha);intro.
rewrite H4 in *; clear H4.
intuition.

assert(H5 := rk_couple1 c alpha H4).
assert (  rk
         (union (union (triple c C O) (triple O C alpha)) (triple b c alpha)) + rk (couple c alpha) <=
       rk (union (triple c C O) (triple O C alpha)) + rk (triple b c alpha)  ).
apply (matroid3_useful); auto.
(clear_all;fsetdecide).
assert ( rk (union (union (triple c C O) (triple O C alpha)) (triple b c alpha)) <= 2).
omega.
setoid_replace (union (union (triple c C O) (triple O C alpha)) (triple b c alpha))  
                 with (add O (quadruple c C  alpha b)) in H6 by (unfold Equal; split;clear_all;fsetdecide).
setoid_replace (triple gamma A O) with (add O (couple gamma A)) in raAO by (clear_all;fsetdecide).
assert ( rk (add O (union (quadruple c C alpha b) (couple gamma A))) <= 3).
apply double_flag;omega.
assert (rk (union (triple A O C) (triple gamma b c)) <= 
           rk (add O (union (quadruple c C alpha b) (couple gamma A))) ).
apply matroid2;(clear_all;fsetdecide).
omega.

assert(H2 := rk_couple1 B O H0).
assert (rk (union (triple gamma B O) (triple b B O)) + rk (couple B O) <=
       rk (triple gamma B O) + rk (triple b B O)).
apply (matroid3_useful); auto.
(clear_all;fsetdecide).
assert (rk (union (triple gamma B O) (triple b B O)) <= 2).
omega.
elim (eq_dec gamma O);intro.
rewrite H5 in *;clear H5.

assert (rk (union (triple A B O) (triple b B O)) + rk (couple B O) <=
       rk (triple A B O) + rk (triple b B O)).

apply (matroid3_useful);(clear_all;fsetdecide).
assert ( rk (union (triple A B O) (triple b B O)) <= 2) by omega.

setoid_replace (union (triple A B O) (triple b B O)) with (add O (triple A B b)) in H5 by (clear_all;fsetdecide).
setoid_replace (triple c C O) with (add O (couple c C)) in rcCO by (clear_all;fsetdecide).

assert (  rk (add O (union (triple A B b) (couple c C))) <= 3).
apply (double_flag O (triple A B b)  (couple c C));omega.
setoid_replace (add O (union (triple A B b) (couple c C))) 
with (union (triple A B C) (triple O b c)) in H7 by (clear_all;fsetdecide).
omega.

assert(H6 := rk_couple1 gamma O H5).
assert ( rk (union (triple gamma B O) (triple gamma A O)) + rk (couple gamma O) <=
       rk (triple gamma B O) + rk (triple gamma A O)).
apply matroid3_useful;auto.
(clear_all;fsetdecide).
assert ( rk (union (triple gamma B O) (triple gamma A O))<= 2).
omega.

assert (
  rk
         (union (union (triple gamma B O) (triple b B O))
            (union (triple gamma B O) (triple gamma A O))) +
       rk (triple gamma B O) <=
       rk (union (triple gamma B O) (triple b B O)) +
       rk (union (triple gamma B O) (triple gamma A O))).
apply matroid3_useful;auto.
(clear_all;fsetdecide).
assert (rk (union (union (triple gamma B O) (triple b B O))
          (union (triple gamma B O) (triple gamma A O))) <= 2).
omega.
setoid_replace (union (union (triple gamma B O) (triple b B O))
          (union (triple gamma B O) (triple gamma A O)))  with (add O (quadruple A B gamma b)) in H10 
          by (unfold Equal; split;clear_all;fsetdecide).
setoid_replace (triple c C O) with (add O (couple c C)) in rcCO by (clear_all;fsetdecide).
assert (rk (add O (union (quadruple A B gamma b) (couple c C))) <= 3).
apply double_flag;omega.
assert (rk (union (triple A B C) (triple gamma b c)) <= 
rk (add O (union (quadruple A B gamma b) (couple c C)))).
apply matroid2.
clear_all;fsetdecide.
omega.
Qed.

Lemma A_not_beta_scheme : forall 
(a : Point)
(b : Point)
(c : Point)
(A : Point)
(B : Point)
(C : Point)
(alpha : Point)
(beta : Point)
(gamma : Point)
(O : Point)
(raAO : rk (triple a A O) = 2)
(rbBO : rk (triple b B O) = 2)
(rcCO : rk (triple c C O) = 2)
(rABC : rk (triple A B C) = 3)
(rabc : rk (triple a b c) = 3)
(rABCabc : rk (union (triple A B C) (triple a b c)) >= 4)
(rABgamma : rk (triple A B gamma) = 2)
(rabgamma : rk (triple a b gamma) = 2)
(rACbeta : rk (triple A C beta) = 2)
(racbeta : rk (triple a c beta) = 2)
(rBCalpha : rk (triple B C alpha) = 2)
(rbcalpha : rk (triple b c alpha) = 2)
(raA : rk (couple a A) = 2)
(rcC : rk (couple c C) = 2)
(rbB : rk (couple b B) = 2),
rk (couple A beta) = 2 \/ rk (triple alpha beta gamma) = 2.
Proof.
intros.
my_classical_left.
rename n into HnotDes.
apply rk_couple1.
intro.
rewrite H0 in *;clear H0.

assert (   rk (union (triple a beta O) (triple a c beta)) + rk (couple a beta) <=
       rk (triple a beta O) + rk (triple a c beta)).
apply  (matroid3_useful (triple a beta O) (triple a c beta) (couple a beta));clear_all;fsetdecide.
assert (rk (union (triple a beta O) (triple a c beta)) <=  2) by omega.
setoid_replace (union (triple a beta O) (triple a c beta)) with (quadruple a c beta O) in H1 by (clear_all;fsetdecide).

elim (eq_dec c O).
intro.
rewrite H2 in * ;clear H2.

elim (eq_dec B alpha); intro.
rewrite H2 in *;clear H2.

setoid_replace (triple beta alpha gamma) with (triple alpha beta gamma) in rABgamma by (clear_all;fsetdecide).
intuition.

assert(HH := rk_couple1 B alpha H2).
assert (rk (union (triple b O alpha) (triple b B O)) + rk (couple b O) <=
       rk (triple b O alpha) + rk (triple b B O)).
apply matroid3_useful.
clear_all;fsetdecide.
assert (rk (union (triple b O alpha) (triple b B O)) <=2).
assert (rk(couple b O)=2).
eapply rk_triple_ABC_couple_BC; eassumption.
omega.
assert (rk
         (union (union (triple b O alpha) (triple b B O)) (triple B C alpha)) +
       rk (couple B alpha) <=
       rk (union (triple b O alpha) (triple b B O)) + rk (triple B C alpha)).
apply matroid3_useful.
clear_all;fsetdecide.
assert ( rk (union (union (triple b O alpha) (triple b B O)) (triple B C alpha))<=2).
omega.
setoid_replace (union (union (triple b O alpha) (triple b B O)) (triple B C alpha)) 
                 with (add O (quadruple b C alpha B)) in H6 by (unfold Equal; split;clear_all;fsetdecide).
setoid_replace (triple a beta O) with (add O (couple a beta)) in raAO by (clear_all;fsetdecide).
assert ( rk (add O (union (quadruple b C alpha B) (couple a beta))) <= 3).
apply double_flag; auto.
omega.
assert (rk (add O (union (quadruple b C alpha B) (couple a beta)))>=
           rk (union (triple beta B C) (triple a b O))).
apply matroid2;clear_all;fsetdecide.
omega.

intro.
cut (rk (add C (quadruple a c beta O)) <= 2).
intro.
assert ( rk (union (add C (quadruple a c beta O)) (triple b B O)) +
       rk (singleton O) <=
       rk (add C (quadruple a c beta O)) + rk (triple b B O)).
apply matroid3_useful.
clear_all;fsetdecide.
rewrite rk_singleton in H4.
assert ( rk (union (add C (quadruple a c beta O)) (triple b B O)) <= 3) by omega.

assert (rk (union (triple beta B C) (triple a b c)) <=  
rk (union (add C (quadruple a c beta O)) (triple b B O))).
apply matroid2.
clear_all;fsetdecide.
omega.

assert (HH := rk_couple1 c O H2).
assert ( rk (union (triple c C O) (quadruple a c beta O)) + rk (couple c O) <=
       rk (triple c C O) + rk (quadruple a c beta O)).
apply (matroid3_useful).
clear_all;fsetdecide.
setoid_replace (add C (quadruple a c beta O)) with (union (triple c C O) (quadruple a c beta O)) by (unfold Equal; split; clear_all;fsetdecide).
omega.
Qed.

End s_desargues3DLemmas.