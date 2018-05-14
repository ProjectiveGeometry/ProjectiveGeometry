Require Export ProjectiveGeometry.Dev.desargues_3D.

(*****************************************************************************)
(** Proof of Desargues in 3D special **)

  
Section s_desargues3DSpecial.

Context `{RPSOH : RankProjectiveSpaceOrHigher}.
Context `{EP : EqDecidability Point}.

(* Hypotheses *)

Variables a b c : Point.
Variables A B C : Point.
Variables alpha beta gamma : Point.
Variables O : Point.

Variable raAO : rk(triple a A O)=2. (* a, A et O alignés et non tous égaux *)
Variable rbBO : rk(triple b B O)=2. (* b, B et O alignés et non tous égaux *)
Variable rcCO : rk(triple c C O)=2. (* c, C et O alignés  et non tous égaux*)
Variable rABC : rk(triple A B C)=3. (* A, B et C non alignés *)
Variable rabc : rk(triple a b c)=3. (* a,b et c non alignés *)

Variable rABCabc : rk(union (triple A B C) (triple a b c))>=4. (* non coplanaires *)

Variable rABgamma : rk(triple A B gamma)=2.
Variable rabgamma : rk(triple a b gamma)=2.

Variable rACbeta : rk(triple A C beta)=2.
Variable racbeta : rk(triple a c beta)=2.

Variable rBCalpha : rk(triple B C alpha)=2.
Variable rbcalpha : rk(triple b c alpha) =2.


Theorem Desargues : rk (triple alpha beta gamma) <= 2.
Proof.
elim (eq_dec A O);intro rAO.
rewrite rAO in *;clear rAO.
elim (eq_dec B O); intro rBO.
rewrite rBO in *;clear rBO.
setoid_replace (triple O O C) with (couple O C) in rABC by (clear_all;fsetdecide).
assert (rk (couple O C)<=2).
apply rk_couple_2.
omega.
assert(HH := rk_couple1 B O rBO).
assert (rk (couple b gamma) = 1 \/ rk (triple b B O) <= 2).
apply (uniq_inter_spec_bis gamma b B O).
assert (rk (union (triple O B gamma) (triple b B O)) + rk (couple B O) <=
       rk (triple O B gamma) + rk (triple b B O)).
apply matroid3_useful.
(clear_all;fsetdecide).
assert (rk (union (triple O B gamma) (triple b B O)) <=2).
omega.

assert (rk (couple B O) = 1 \/ rk (triple B gamma b) <= 2).
apply  (uniq_inter_spec_bis O B gamma b).
setoid_replace  (triple B gamma O) with (triple O B gamma) by (clear_all;fsetdecide); omega.
setoid_replace (triple B b O) with (triple b B O) by (clear_all;fsetdecide); omega.
elim H2.
intros; omega.
intros Hrk.
setoid_replace (triple b B gamma) with (triple B gamma b) by (clear_all;fsetdecide); omega.
assert (rk (union (triple b B O) (triple O B gamma)) + rk (couple B O) <=
       rk (triple b B O) + rk (triple O B gamma)).
apply matroid3_useful; (clear_all;fsetdecide).
assert (rk (union (triple b B O) (triple O B gamma))>= rk (triple b O gamma)). 
apply matroid2;(clear_all;fsetdecide).
omega.
(* B <> O and A=O *)
assert (rk(couple b gamma)=1).
apply (uniq_inter B O a b b gamma); try (assumption || omega).
eapply rk_triple_ABC_couple_AB; eauto.
setoid_replace (triple B O b) with (triple b B O) by (clear_all;fsetdecide); omega.
setoid_replace (triple a b  b) with (couple a b) by (clear_all;fsetdecide); apply rk_couple_2.
setoid_replace (triple B O gamma) with (triple O B gamma) by (clear_all;fsetdecide); omega.
assert (rk (union (quadruple B O a b) (triple c C O)) +
       rk (singleton O) <= rk (quadruple B O a b) + rk (triple c C O)).
apply matroid3_useful; (clear_all;fsetdecide).
rewrite rk_singleton in H1.
assert (rk (union (quadruple B O a b) (triple c C O)) >=rk (union (triple O B C) (triple a b c)) ).
apply matroid2;(clear_all;fsetdecide).
omega.

elim (eq_dec C O); intros rCO.
rewrite rCO in *;clear rCO.
setoid_replace (triple O B O) with (couple O B) in rABC by (clear_all;fsetdecide).
assert (rk (couple O B)<=2).
apply rk_couple_2.
omega.

assert(HH0 := rk_couple1 C O rCO).
assert (rk(couple c beta)=1).
apply (uniq_inter C O a c c beta); try (assumption || omega).
eapply rk_triple_ABC_couple_AC; eauto.
setoid_replace (triple C O c) with (triple c C O) by (clear_all;fsetdecide); omega.
setoid_replace (triple a c c) with (couple a c) by (clear_all;fsetdecide); apply rk_couple_2.
setoid_replace (triple C O beta) with (triple O C beta) by (clear_all;fsetdecide); omega.
assert (rk (union (quadruple C O a c) (triple b B O)) +
       rk (singleton O) <= rk (quadruple C O a c) + rk (triple b B O)).
apply matroid3_useful; (clear_all;fsetdecide).
rewrite rk_singleton in H2.
assert (rk (union (quadruple C O a c) (triple b B O)) >=rk (union (triple O B C) (triple a b c)) ).
apply matroid2; (clear_all;fsetdecide).
omega.
rewrite <- (couple_rk2 b gamma) by assumption.
rewrite <- (couple_rk2 c beta) by assumption.
setoid_replace (triple alpha c b) with (triple b c alpha) by (clear_all;fsetdecide); omega.

assert(HH := rk_couple1 A O rAO).
elim (eq_dec B O); intro rBO.
rewrite rBO in *;clear rBO.
elim (eq_dec C O);intro rCO.
rewrite rCO in *;clear rCO .
setoid_replace (triple A O O) with (couple A O) in rABC by (clear_all;fsetdecide).
assert (rk (couple A O)<=2).
apply rk_couple_2.
omega.

assert (rk(couple a gamma)=1).
apply (uniq_inter A O a b a gamma); try (assumption || omega).
eapply rk_triple_ABC_couple_AB; eauto.
setoid_replace (triple A O a) with (triple a A O) by (clear_all;fsetdecide); omega.
setoid_replace (triple a b  a) with (couple a b) by (clear_all;fsetdecide); apply rk_couple_2.
assert (rk (union (quadruple A O a b) (triple c C O)) +
       rk (singleton O) <= rk (quadruple A O a b) + rk (triple c C O)).
apply matroid3_useful; (clear_all;fsetdecide).
rewrite rk_singleton in H0.
assert (rk (union (quadruple A O a b) (triple c C O)) >=rk (union (triple A O C) (triple a b c)) ).
apply matroid2; (clear_all;fsetdecide).
omega.

assert(HH0 := rk_couple1 C O rCO).
assert (rk(couple c alpha)=1).
apply (uniq_inter C O b c c alpha); try (assumption || omega).
eapply rk_triple_ABC_couple_BC; eauto.
setoid_replace (triple C O c) with (triple c C O) by (clear_all;fsetdecide); omega.
setoid_replace (triple b c c) with (couple b c) by (clear_all;fsetdecide); apply rk_couple_2.
setoid_replace (triple C O alpha) with (triple O C alpha) by (clear_all;fsetdecide); omega.
assert (rk (union (quadruple C O b c) (triple a A O)) +
       rk (singleton O) <= rk (quadruple C O b c) + rk (triple a A O)).
apply matroid3_useful; (clear_all;fsetdecide).
rewrite rk_singleton in H1.
assert (rk (union (quadruple C O b c) (triple a A O)) >=rk (union (triple A O C) (triple a b c)) ).
apply matroid2; (clear_all;fsetdecide).
omega.
rewrite  <- (couple_rk2 a gamma) by assumption.
rewrite <- (couple_rk2 c alpha) by assumption.
setoid_replace (triple c beta a) with (triple a c beta) by (clear_all;fsetdecide); omega.

assert(HH0 := rk_couple1 B O rBO).
elim (eq_dec C O); intro rCO.
rewrite rCO in *;clear rCO.
assert (rk(couple a beta)=1).
apply (uniq_inter A O a c a beta); try (assumption || omega).
eapply rk_triple_ABC_couple_AC; eauto.
setoid_replace (triple A O a) with (triple a A O) by (clear_all;fsetdecide); omega.
setoid_replace (triple a c a) with (couple a c) by (clear_all;fsetdecide); apply rk_couple_2.
assert (rk (union (quadruple A O a c) (triple b B O)) +
       rk (singleton O) <= rk (quadruple A O a c) + rk (triple b B O)).
apply matroid3_useful; (clear_all;fsetdecide).
rewrite rk_singleton in H0.
assert (rk (union (quadruple A O a c) (triple b B O)) >=rk (union (triple A B O) (triple a b c)) ).
apply matroid2;(clear_all;fsetdecide).
omega.
assert (rk(couple b alpha)=1).
apply (uniq_inter B O b c b alpha); try (assumption || omega).
eapply rk_triple_ABC_couple_BC; eauto.
setoid_replace (triple B O b) with (triple b B O) by (clear_all;fsetdecide); omega.
setoid_replace (triple b c b) with (couple b c) by (clear_all;fsetdecide); apply rk_couple_2.
assert (rk (union (quadruple B O b c) (triple a A O)) +
       rk (singleton O) <= rk (quadruple B O b c) + rk (triple a A O)).
apply matroid3_useful; (clear_all;fsetdecide).
rewrite rk_singleton in H1.
assert (rk (union (quadruple B O b c) (triple a A O)) >=rk (union (triple A B O) (triple a b c)) ).
apply matroid2;(clear_all;fsetdecide).
omega.
rewrite  <- (couple_rk2 a beta) by assumption.
rewrite <- (couple_rk2 b alpha) by assumption.
setoid_replace (triple b a gamma) with (triple a b gamma) by (clear_all;fsetdecide); omega.
assert(HH1 := rk_couple1 C O rCO).
(* end of cases A,B,C with respect to O *)
elim (eq_dec a A);intro.
rewrite H0 in *;clear H0.
elim (eq_dec c C); intro.
rewrite H0 in *;clear H0.
assert (rk(couple A gamma)=1).
apply (sublemma'' A b C A B C alpha beta gamma O); try assumption; trivial.
assert (rk(couple C alpha)=1).
eapply (sublemma'' C b A C B A gamma beta alpha O); try assumption.
setoid_replace (triple C B A) with (triple A B C) by (clear_all;fsetdecide); assumption.
setoid_replace (triple C b A) with (triple A b C) by (clear_all;fsetdecide); assumption.
setoid_replace (triple C B A) with (triple A B C) by (clear_all;fsetdecide).
setoid_replace (triple C b A) with (triple A b C)  by (clear_all;fsetdecide); assumption.
setoid_replace (triple C B alpha) with (triple B C alpha) by (clear_all;fsetdecide); assumption.
setoid_replace (triple C b alpha) with (triple b C alpha) by (clear_all;fsetdecide); assumption.
setoid_replace (triple C A beta) with (triple A C beta) by (clear_all;fsetdecide); assumption.
setoid_replace (triple C A beta) with (triple A C beta) by (clear_all;fsetdecide); assumption.
setoid_replace (triple B A gamma) with (triple A B gamma) by (clear_all;fsetdecide); assumption.
setoid_replace (triple b A gamma) with (triple A b gamma) by (clear_all;fsetdecide); assumption.
trivial.
trivial.
rewrite <- (couple_rk2 A gamma) by assumption.
rewrite <- (couple_rk2 C alpha); try assumption.
setoid_replace (triple C beta A) with (triple A C beta) by (clear_all;fsetdecide); omega.
(* c <> C *)
generalize (rk_couple1 c C H0); clear H0; intros rcC.
assert (rk(couple A beta)=1).
eapply (sublemma b c A B C alpha beta gamma O); eassumption.
subst.
elim (eq_dec b B); intro.
rewrite H1 in *;clear H1.
assert (rk(couple B alpha)=1).
eapply (sublemma'' B c A  B C A beta gamma) with (O0:=O); try eassumption.
setoid_replace (triple B C A) with (triple A B C) by (clear_all;fsetdecide); assumption.
setoid_replace (triple B c A) with (triple A B c) by (clear_all;fsetdecide); assumption.
setoid_replace (triple B C A) with (triple A B C) by (clear_all;fsetdecide).
setoid_replace  (triple B c A)  with  (triple A B c) by (clear_all;fsetdecide); assumption.
setoid_replace (triple B A gamma) with (triple A B gamma) by (clear_all;fsetdecide); assumption.
setoid_replace (triple B A gamma) with (triple A B gamma) by (clear_all;fsetdecide); assumption.
setoid_replace (triple C A beta) with (triple A C beta) by (clear_all;fsetdecide); assumption.
setoid_replace (triple c A beta) with (triple A c beta) by (clear_all;fsetdecide); assumption.
trivial.
trivial.
rewrite <- (couple_rk2 A beta); [idtac |  assumption].
rewrite <- (couple_rk2 B alpha); [idtac | assumption].
setoid_replace (triple B A gamma) with (triple A B gamma) by (clear_all;fsetdecide); omega.
(* B <> b *)
assert (rk (couple A gamma)=1).
eapply (sublemma c b  A C B alpha gamma beta O) ; try eassumption.
setoid_replace (triple A C B) with (triple A B C) by (clear_all;fsetdecide); assumption.
setoid_replace (triple C B alpha) with (triple B C alpha) by (clear_all;fsetdecide); assumption.
setoid_replace (triple c b alpha) with (triple b c alpha) by (clear_all;fsetdecide); assumption.
setoid_replace (triple A c b) with (triple A b c) by (clear_all;fsetdecide); assumption.
setoid_replace (triple A C B) with (triple A B C) by (clear_all;fsetdecide).
setoid_replace (triple A c b) with (triple A b c) by (clear_all;fsetdecide); assumption.
apply rk_couple1; assumption.
assert (gamma [==] beta).
rewrite <- (couple_rk2 A beta); try assumption.
rewrite <- (couple_rk2 A gamma); try assumption.
reflexivity. 
rewrite H3.
setoid_replace (triple alpha beta beta) with (couple alpha beta) by (clear_all;fsetdecide).
apply rk_couple_2. 

assert (raA : rk (couple a A) = 2).
apply rk_couple1.
auto.
elim (eq_dec c C);intro.
rewrite H1 in *;clear H1.
assert (rk(couple C beta)=1).
eapply (sublemma  b a C B A gamma beta alpha O); try assumption.
setoid_replace (triple C B A) with (triple A B C) by (clear_all;fsetdecide); assumption.
setoid_replace (triple C B alpha) with (triple B C alpha) by (clear_all;fsetdecide); assumption.
setoid_replace (triple C A beta) with (triple A C beta) by (clear_all;fsetdecide); assumption.
setoid_replace (triple B A gamma) with (triple A B gamma) by (clear_all;fsetdecide); assumption.
setoid_replace (triple b a gamma) with (triple a b gamma) by (clear_all;fsetdecide); assumption.
setoid_replace (triple C b a) with (triple a b C) by (clear_all;fsetdecide); assumption.
setoid_replace (triple C B A) with (triple A B C) by (clear_all;fsetdecide).
setoid_replace (triple C b a)  with (triple a b C)  by (clear_all;fsetdecide); assumption.
setoid_replace (triple C b alpha) with (triple b C alpha) by (clear_all;fsetdecide); assumption.
setoid_replace (triple C a beta) with (triple a C beta) by (clear_all;fsetdecide); assumption.
elim (eq_dec b B); intro.
rewrite H2 in *;clear H2.
assert (rk(couple B gamma)=1).
eapply (sublemma'' B a C B A C beta alpha) with (O0:=O); try assumption; try trivial.
setoid_replace (triple B A C) with (triple A B C) by (clear_all;fsetdecide); assumption.
setoid_replace (triple B a C) with (triple a B C) by (clear_all;fsetdecide); assumption.
setoid_replace (triple B A C) with (triple A B C) by (clear_all;fsetdecide).
setoid_replace (triple B a C)  with (triple a B C) by (clear_all;fsetdecide); assumption.
setoid_replace (triple B A gamma) with (triple A B gamma) by (clear_all;fsetdecide); assumption.
setoid_replace (triple B a gamma) with (triple a B gamma) by (clear_all;fsetdecide); assumption.
rewrite <- (couple_rk2 B gamma); [idtac |  assumption].
rewrite <- (couple_rk2 C beta); [idtac | assumption].
setoid_replace (triple alpha C B) with (triple B C alpha) by (clear_all;fsetdecide); omega.
assert (rk(couple C alpha)=1).
eapply (sublemma a b  C A B gamma alpha beta) ; try eassumption.
setoid_replace (triple C A B) with (triple A B C) by (clear_all;fsetdecide); assumption.
setoid_replace (triple C A beta) with (triple A C beta) by (clear_all;fsetdecide); assumption.
setoid_replace (triple C B alpha) with (triple B C alpha) by (clear_all;fsetdecide); assumption.
setoid_replace (triple C a b) with (triple a b C) by (clear_all;fsetdecide); assumption.
setoid_replace (triple C A B) with (triple A B C) by (clear_all;fsetdecide).
setoid_replace (triple C a b)  with (triple a b C)  by (clear_all;fsetdecide); assumption.
setoid_replace (triple C a beta) with (triple a C beta) by (clear_all;fsetdecide); assumption.
setoid_replace (triple C b alpha) with (triple b C alpha) by (clear_all;fsetdecide); assumption.
apply rk_couple1; assumption.
rewrite <- (couple_rk2 C alpha); [idtac |  assumption].
rewrite <- (couple_rk2 C beta); [idtac | assumption].
setoid_replace (triple C C gamma) with (couple C gamma) by (clear_all;fsetdecide).
apply rk_couple_2.
assert (rcC : rk (couple c C) = 2).
apply rk_couple1; auto.
elim (eq_dec b B);intro.
rewrite H2 in *;clear H2.
assert (rk(couple B alpha)=1).
eapply (sublemma a c B A C beta alpha gamma) with (O0:= O); try assumption.
setoid_replace (triple B A C) with (triple A B C) by (clear_all;fsetdecide); assumption.
setoid_replace (triple B A gamma) with (triple A B gamma) by (clear_all;fsetdecide); assumption.
setoid_replace (triple B a c) with (triple a B c) by (clear_all;fsetdecide); assumption.
setoid_replace (triple B A C) with (triple A B C) by (clear_all;fsetdecide).
setoid_replace (triple B a c) with (triple a B c) by (clear_all;fsetdecide); assumption.
setoid_replace (triple B a gamma) with (triple a B gamma) by (clear_all;fsetdecide); assumption.
assert (rk(couple B gamma)=1).
eapply (sublemma c a B C A beta gamma alpha) with (O0:=O); try assumption.
setoid_replace (triple B C A) with (triple A B C) by (clear_all;fsetdecide); assumption.
setoid_replace (triple B A gamma) with (triple A B gamma) by (clear_all;fsetdecide); assumption.
setoid_replace (triple C A beta) with (triple A C beta) by (clear_all;fsetdecide); assumption.
setoid_replace (triple c a beta) with (triple a c beta) by (clear_all;fsetdecide); assumption.
setoid_replace (triple B c a) with (triple a B c) by (clear_all;fsetdecide); assumption.
setoid_replace (triple B C A) with (triple A B C) by (clear_all;fsetdecide).
setoid_replace (triple B c a) with (triple a B c)  by (clear_all;fsetdecide); assumption.
setoid_replace (triple B a gamma) with (triple a B gamma) by (clear_all;fsetdecide); assumption.
rewrite <- (couple_rk2 B alpha); [idtac |  assumption].
rewrite <- (couple_rk2 B gamma); [idtac | assumption].
setoid_replace (triple B beta B) with (couple B beta) by (clear_all;fsetdecide).
apply rk_couple_2.

assert (rbB : rk (couple b B) = 2).
apply rk_couple1;auto.
eapply (Desargues_general a b c A B C alpha beta gamma O); auto.
Qed.

End s_desargues3DSpecial.