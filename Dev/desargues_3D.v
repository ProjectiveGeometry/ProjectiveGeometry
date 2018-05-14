Require Export ProjectiveGeometry.Dev.desargues_3D_lemmas.

(*****************************************************************************)
(** Proof of Desargues in 3D **)

  
Section s_desargues3D.

Context `{RPSOH : RankProjectiveSpaceOrHigher}.
Context `{EP : EqDecidability Point}.

Variables a b c : Point.
Variables A B C : Point.
Variables alpha beta gamma : Point.
Variables O : Point.

Variable raAO : rk(triple a A O)=2. 
Variable rbBO : rk(triple b B O)=2. 
Variable rcCO : rk(triple c C O)=2. 
Variable rABC : rk(triple A B C)=3. 
Variable rabc : rk(triple a b c)=3. 

Variable rABCabc : rk(union (triple A B C) (triple a b c))>=4. (* not coplanar *)

Variable rABgamma : rk(triple A B gamma)=2.
Variable rabgamma : rk(triple a b gamma)=2.

Variable rACbeta : rk(triple A C beta)=2.
Variable racbeta : rk(triple a c beta)=2.

Variable rBCalpha : rk(triple B C alpha)=2.
Variable rbcalpha : rk(triple b c alpha)=2.

Definition ps : set Point := triple a b c.
Definition Ps : set Point := triple A B C.

Variable raA : rk(couple a A)=2.
Variable rcC : rk(couple c C)=2.
Variable rbB : rk(couple b B)=2.

Hint Resolve rk_singleton rk_couple1 rk_couple2 couple_rk1 couple_rk2 couple_rk_degen rk_couple_1 rk_couple_2 : rk_base.
Hint Resolve rk_triple_ABC_couple_AB rk_triple_ABC_couple_BC rk_triple_ABC_couple_AC : rk_base.
Hint Resolve  rk_triple_singleton : rk_base.
Hint Resolve rk_couple_not_zero : rk_base.

Lemma a_not_alpha :rk(couple a alpha) =2. (* contradicts hyp rabc *)
Proof.
apply rk_couple1.
intro H0;rewrite H0 in *;clear H0.
setoid_replace (triple alpha b c) with (triple b c alpha) in rabc by (clear_all;fsetdecide).
rewrite rabc in rbcalpha; omega.
Qed.

Lemma a_not_gamma :rk(couple a gamma) =2 \/ rk (triple gamma alpha beta) = 2.
Proof.
apply (a_not_gamma_scheme a b c A B C alpha beta gamma O); try assumption.
Qed.

Lemma c_not_beta : rk(couple c beta) = 2 \/ rk (triple beta gamma alpha)=2.
Proof.
apply (a_not_gamma_scheme c a b C A B gamma alpha beta O); try assumption.
setoid_replace (triple C A B) with (triple A B C) by (clear_all;fsetdecide); assumption.
setoid_replace (triple c a b) with (triple a b c) by (clear_all;fsetdecide); assumption.
setoid_replace (triple C A B) with (triple A B C) by (clear_all;fsetdecide).
setoid_replace (triple c a b) with (triple a b c) by (clear_all;fsetdecide); assumption.
setoid_replace (triple C A beta) with (triple A C beta) by (clear_all;fsetdecide); assumption.
setoid_replace (triple c a beta) with (triple a c beta) by (clear_all;fsetdecide); assumption.
setoid_replace (triple C B alpha) with (triple B C alpha) by (clear_all;fsetdecide); assumption.
setoid_replace (triple c b alpha) with (triple b c alpha) by (clear_all;fsetdecide); assumption.
Qed.

Lemma b_not_gamma : rk(couple b gamma) = 2 \/ rk (triple gamma beta alpha)=2.
Proof.
apply (a_not_gamma_scheme b a c B A C beta alpha gamma O); try assumption.
setoid_replace (triple B A C) with (triple A B C) by (clear_all;fsetdecide); assumption.
setoid_replace (triple b a c) with (triple a b c) by (clear_all;fsetdecide); assumption.
setoid_replace (triple B A C) with (triple A B C) by (clear_all;fsetdecide).
setoid_replace (triple b a c) with  (triple a b c) by (clear_all;fsetdecide); assumption.
setoid_replace (triple B A gamma) with (triple A B gamma) by (clear_all;fsetdecide); assumption.
setoid_replace (triple b a gamma) with( triple a b gamma) by (clear_all;fsetdecide); assumption.
Qed.

Hint Resolve  a_not_alpha a_not_gamma c_not_beta b_not_gamma : rk_base.

Lemma A_not_alpha  : rk(couple A alpha) =2.
Proof.
apply rk_couple1.
intro H0;rewrite H0 in *;clear H0.
setoid_replace (triple alpha B C) with (triple B C alpha) in rABC by (clear_all;fsetdecide).
rewrite rABC in rBCalpha; omega.
Qed.

Lemma B_not_beta :rk(couple B beta) =2.
Proof.
apply rk_couple1.
intro H0;rewrite H0 in *;clear H0.
setoid_replace (triple A beta C) with (triple A C beta) in rABC by (clear_all;fsetdecide).
rewrite rABC in rACbeta; omega.
Qed.

Lemma C_not_gamma :rk(couple C gamma) =2.
Proof.
apply rk_couple1.
intro H0;rewrite H0 in *;clear H0.
omega.
Qed.

Lemma A_not_beta  : rk(couple A beta)=2 \/ rk(triple alpha beta gamma)=2.
Proof.
eapply (A_not_beta_scheme a b c A B C alpha beta gamma O); try assumption.
Qed.

Lemma A_not_gamma :rk(couple A gamma) =2\/rk(triple alpha beta gamma)=2.
Proof.
setoid_replace (triple alpha beta gamma) with (triple alpha gamma beta) by (clear_all;fsetdecide).
apply (A_not_beta_scheme a c b A C B alpha gamma beta O); try assumption.
setoid_replace (triple A C B) with (triple A B C) by (clear_all;fsetdecide); assumption.
setoid_replace (triple a c b) with (triple  a b c) by (clear_all;fsetdecide); assumption.
setoid_replace (triple A C B) with (triple A B C) by (clear_all;fsetdecide).
setoid_replace  (triple a c b) with (triple a b c)  by (clear_all;fsetdecide); assumption.
setoid_replace (triple C B alpha) with (triple B C alpha) by (clear_all;fsetdecide);assumption.
setoid_replace (triple c b alpha) with (triple b c alpha) by (clear_all;fsetdecide); assumption.
Qed.

Lemma B_not_alpha :rk(couple B alpha)=2 \/ rk(triple alpha beta gamma)=2.
Proof.
setoid_replace (triple alpha beta gamma) with (triple beta alpha gamma)  by (clear_all;fsetdecide).
apply (A_not_beta_scheme b a c B A C beta alpha gamma O); try assumption.
setoid_replace (triple B A C) with (triple A B C) by (clear_all;fsetdecide); assumption.
setoid_replace (triple b a c) with (triple  a b c) by (clear_all;fsetdecide); assumption.
setoid_replace (triple B A C) with (triple A B C) by (clear_all;fsetdecide).
setoid_replace (triple b a c) with (triple a b c) by (clear_all;fsetdecide); assumption.
setoid_replace (triple B A gamma) with (triple A B gamma) by (clear_all;fsetdecide); assumption.
setoid_replace (triple b a gamma) with (triple a b gamma) by (clear_all;fsetdecide); assumption.
Qed.

Lemma B_not_gamma:rk(couple B gamma)=2 \/ rk(triple alpha beta gamma)=2.
Proof.
setoid_replace (triple alpha beta gamma) with (triple beta gamma alpha) by (clear_all;fsetdecide).
apply (A_not_beta_scheme b c a B C A beta gamma alpha O); try assumption.
setoid_replace (triple B C A) with (triple A B C) by (clear_all;fsetdecide); assumption.
setoid_replace (triple b c a) with (triple a b c) by (clear_all;fsetdecide); assumption.
setoid_replace (triple B C A) with (triple A B C) by (clear_all;fsetdecide).
setoid_replace (triple b c a)  with  (triple a b c)  by (clear_all;fsetdecide); assumption.
setoid_replace (triple B A gamma) with (triple A B gamma) by (clear_all;fsetdecide); assumption.
setoid_replace (triple b a gamma) with (triple a b gamma) by (clear_all;fsetdecide); assumption.
setoid_replace (triple C A beta) with (triple A C beta) by (clear_all;fsetdecide); assumption.
setoid_replace (triple c a beta) with (triple a c beta) by (clear_all;fsetdecide); assumption.
Qed.

Lemma C_not_alpha :rk(couple C alpha) =2\/rk(triple alpha beta gamma)=2.
Proof.
setoid_replace (triple alpha beta gamma) with (triple gamma alpha beta) by (clear_all;fsetdecide).
apply (A_not_beta_scheme c a b C A B gamma alpha beta O); try assumption.
setoid_replace (triple C A B) with (triple A B C) by (clear_all;fsetdecide); assumption.
setoid_replace (triple c a b) with (triple a b c) by (clear_all;fsetdecide); assumption.
setoid_replace (triple C A B) with (triple A B C) by (clear_all;fsetdecide).
setoid_replace (triple c a b) with (triple a b c)  by (clear_all;fsetdecide); assumption.
setoid_replace (triple C A beta) with (triple A C beta) by (clear_all;fsetdecide);assumption.
setoid_replace (triple c a beta) with (triple a c beta) by (clear_all;fsetdecide);assumption.
setoid_replace (triple C B alpha) with (triple B C alpha) by (clear_all;fsetdecide);assumption.
setoid_replace (triple c b alpha) with (triple b c alpha) by (clear_all;fsetdecide);assumption.
Qed.

Lemma C_not_beta :rk(couple C beta) =2\/rk(triple alpha beta gamma)=2.
Proof.
setoid_replace (triple alpha beta gamma) with (triple gamma beta alpha) by (clear_all;fsetdecide).
apply (A_not_beta_scheme c b a C B A gamma beta alpha O) ; try assumption.
setoid_replace (triple C B A) with (triple A B C) by (clear_all;fsetdecide); assumption.
setoid_replace (triple c b a) with (triple a b c) by (clear_all;fsetdecide); assumption.
setoid_replace (triple C B A) with (triple A B C) by (clear_all;fsetdecide).
setoid_replace  (triple c b a) with (triple a b c)  by (clear_all;fsetdecide); assumption.
setoid_replace (triple C B alpha) with (triple B C alpha) by (clear_all;fsetdecide);assumption.
setoid_replace (triple c b alpha) with (triple b c alpha) by (clear_all;fsetdecide);assumption.
setoid_replace (triple C A beta) with (triple A C beta) by (clear_all;fsetdecide);assumption.
setoid_replace (triple c a beta) with (triple a c beta) by (clear_all;fsetdecide);assumption.
setoid_replace (triple B A gamma) with (triple A B gamma) by (clear_all;fsetdecide);assumption.
setoid_replace (triple b a gamma) with (triple a b gamma) by (clear_all;fsetdecide);assumption.
Qed.

(* these 6 lemmas (above) contradict coplanarity hyp rABCabc or lead to rk(alpha,beta,gamma)=2 *)

Hint Resolve A_not_alpha B_not_beta C_not_gamma
 A_not_beta A_not_gamma B_not_alpha B_not_gamma 
C_not_alpha C_not_beta.

Lemma rAB :  rk(couple A B)=2.
Proof.
eauto with rk_base.
Qed.

Lemma rBC : rk(couple B C)=2.
Proof.
eauto with rk_base.
Qed.

Lemma rAC : rk(couple A C)=2.
Proof.
eauto with rk_base.
Qed.

Lemma rab : rk(couple a b)=2.
Proof.
eauto with rk_base.
Qed.

Lemma rac : rk(couple a c)=2.
Proof.
eauto with rk_base.
Qed.

Lemma rbc : rk(couple b c)=2.
Proof.
eauto with rk_base.
Qed.

Lemma L1alpha : rk(union Ps (singleton alpha))=3.
Proof.
unfold Ps.
eapply (rk_triple_singleton).
intuition.
Qed.

Lemma L1palpha:rk(union ps (singleton alpha)) = 3.
Proof.
unfold ps.
eapply (rk_triple_singleton).
intuition.
Qed.

Lemma L1Pbeta : rk(union Ps (singleton beta))=3.
Proof.
apply  L1beta_gen;auto.
Qed.

Lemma L1pbeta : rk(union ps (singleton beta))=3.
Proof.
apply  L1beta_gen;auto.
Qed.

Lemma L1Pgamma : rk(union Ps (singleton gamma))=3.
Proof.
apply  L1gamma_gen;auto.
Qed.

Lemma L1pgamma : rk(union ps (singleton gamma))=3.
Proof.
apply  L1gamma_gen;auto.
Qed.


Lemma ralphabeta : rk(couple alpha beta)=2 \/ rk(triple alpha beta gamma)=2.
Proof.
my_classical_left.
rename n into HnotDes.
apply le_antisym.
auto with rk_base.
assert (rk (couple alpha beta) = 0 \/ rk (couple alpha beta) =1 \/ rk (couple alpha beta) >= 2).
omega.
elim H0;intro.
apply False_ind.
assert(HH := rk_couple_not_zero alpha beta H1).
assumption.

elim H1;intro.
assert (rk (couple c beta) = 2 \/ rk (triple beta gamma alpha) = 2).
apply c_not_beta.
elim H3;intro c_not_beta_local.
2:setoid_replace (triple beta gamma alpha)  with (triple alpha beta gamma) 
in c_not_beta_local by (clear_all;fsetdecide);omega.
assert(HH : alpha [==] beta).
apply couple_rk2;assumption.
rewrite HH in *; clear HH.
assert  (T:= (col_trans a b c beta racbeta rbcalpha c_not_beta_local)).
omega.
omega.
Qed.

Lemma ralphagamma : rk(couple alpha gamma)=2\/rk(triple alpha beta gamma)=2.
Proof.
my_classical_left.
rename n into HnotDes.
apply le_antisym.
auto with rk_base.
assert (rk (couple alpha gamma) = 0 \/ rk (couple alpha gamma) =1 \/ rk (couple alpha gamma) >= 2).
omega.

elim H0;intro.
apply False_ind.
assert(HH := rk_couple_not_zero alpha gamma H1).
assumption.

elim H1;intro.
assert (rk (couple b gamma) = 2 \/ rk (triple gamma beta alpha) = 2).
apply b_not_gamma.
elim H3;intro b_not_gamma_local.
2:setoid_replace (triple gamma beta alpha)  with (triple alpha beta gamma) 
in b_not_gamma_local by (clear_all;fsetdecide);omega.
assert(HH : alpha [==] gamma).
apply couple_rk2;assumption.
rewrite HH in *; clear HH.
setoid_replace (triple b c gamma) with (triple c b gamma) in rbcalpha by (clear_all;fsetdecide).
assert  (T:= (col_trans a c b gamma rabgamma rbcalpha b_not_gamma_local)).
setoid_replace (triple a b c) with (triple a c b) in rabc by (clear_all;fsetdecide). 
omega.
omega.
Qed.

Lemma rbetagamma : rk(couple beta gamma)= 2 \/ rk (triple alpha beta gamma) = 2.
Proof.
my_classical_left.
rename n into HnotDes.
apply le_antisym.
auto with rk_base.
assert (rk (couple beta gamma) = 0 \/ rk (couple beta gamma) =1 \/ rk (couple beta gamma) >= 2).
omega.

elim H0;intro.
apply False_ind.
assert(HH := rk_couple_not_zero beta gamma H1).
assumption.
elim H1;intro.

assert (rk (couple a gamma) = 2 \/ rk (triple gamma alpha beta) = 2).
apply a_not_gamma.
elim H3;intro a_not_gamma_local.
2:setoid_replace (triple gamma alpha beta) with (triple alpha beta gamma) 
in a_not_gamma_local by (clear_all;fsetdecide);omega.
assert(HH : beta [==] gamma).
apply couple_rk2;assumption.
rewrite HH in *; clear HH.
setoid_replace (triple a c gamma) with (triple c a gamma) in racbeta by (clear_all;fsetdecide).
setoid_replace (triple a b gamma) with (triple b a gamma) in rabgamma by (clear_all;fsetdecide).
assert (rk (triple c b a) <= 2) by (apply (col_trans  c b a gamma racbeta rabgamma a_not_gamma_local)).
setoid_replace (triple a b c) with (triple c b a) in rabc by (clear_all;fsetdecide).
omega.
omega.
Qed.

Lemma L2P : rk(union Ps (triple alpha beta gamma))= 3 \/  rk (triple alpha beta gamma) = 2.
Proof.
my_classical_left.
rename n into HnotDes.
apply le_antisym.

(* >= *)
assert (rk (union Ps (couple alpha beta)) <= 3).

generalize (matroid3 (union Ps (singleton alpha)) (union Ps (singleton beta))).
rewrite L1alpha.
rewrite L1Pbeta.
setoid_replace (inter (union Ps (singleton alpha)) (union Ps (singleton beta))) with Ps.
unfold Ps at 3; rewrite rABC.

setoid_replace (union (union Ps (singleton alpha)) (union Ps (singleton beta))) with (union Ps (couple alpha beta)).
omega.
(clear_all;fsetdecide).
unfold Ps.
assert (~ alpha [==] beta).
generalize ralphabeta.
intro.
elim H0;intros;clear H0.
apply couple_rk1;auto.
intuition.
(clear_all;fsetdecide).

generalize (matroid3 (union Ps (couple alpha beta)) (union Ps (singleton gamma))).

setoid_replace (union (union Ps (couple alpha beta)) (union Ps (singleton gamma))) with
                        (union Ps (triple alpha beta gamma)) by (clear_all;fsetdecide).

setoid_replace (inter (union Ps (couple alpha beta)) (union Ps (singleton gamma))) with Ps.
rewrite L1Pgamma.
unfold Ps at 2.
rewrite rABC.
omega.
unfold Ps.
assert (~ alpha [==] gamma).
generalize ralphagamma.
intro.
elim H1;intro; clear H1.
apply couple_rk1;auto.
intuition.
assert (~ beta [==] gamma).
generalize rbetagamma.
intro.
elim H2;intro; clear H2.
apply couple_rk1;auto.
intuition.
(clear_all;fsetdecide).
(* <= *)
assert (Hsubset : (Subset (union Ps (couple alpha beta)) (union Ps (triple alpha beta gamma))))
by (clear_all;fsetdecide).
apply le_trans with (rk (union Ps (couple alpha beta))).
2:apply (matroid2 (union Ps (couple alpha beta)) (union Ps (triple alpha beta gamma)) Hsubset).
assert (Hsubset' : Subset (union Ps (singleton alpha)) (union Ps (couple alpha beta))) by (clear_all;fsetdecide).
apply le_trans with (rk (union Ps (singleton alpha))).
2: apply (matroid2 (union Ps (singleton alpha)) (union Ps (couple alpha beta)) Hsubset').
rewrite L1alpha.
solve[intuition].
Qed.

Lemma  L2p : rk(union ps (triple alpha beta gamma))=3 \/ rk (triple alpha beta gamma) = 2.
Proof.
my_classical_left.
rename n into HnotDes.
apply le_antisym.
(*<=*)
assert (rk(union ps (couple alpha beta)) <=3).
generalize (matroid3 (union ps (singleton alpha)) (union ps (singleton beta))).
rewrite L1palpha.
rewrite L1pbeta.
setoid_replace (union(union ps (singleton alpha))(union ps (singleton beta))) 
with (union ps (couple alpha beta)).
2:(clear_all;fsetdecide).
setoid_replace (inter (union ps (singleton alpha))(union ps (singleton beta)))
                        with ps.
unfold ps.
rewrite rabc.
omega.
assert (~ alpha [==] beta).
generalize (ralphabeta).
intros.
elim H0; intros;clear H0.
apply couple_rk1;auto.
intuition.
(clear_all;fsetdecide).

generalize (matroid3 (union ps(couple alpha beta))(union ps(singleton gamma))).
rewrite L1pgamma.
setoid_replace (union(union ps (couple alpha beta))(union ps (singleton gamma))) 
                with (union ps(triple alpha beta gamma)) by (clear_all;fsetdecide).

assert (~ alpha [==] gamma).
  generalize (ralphagamma).
  intros.
  elim H1; intros;clear H1.
  apply couple_rk1;auto.
  intuition.
  auto.

assert (~ beta [==] gamma).
   generalize (rbetagamma).
   intros.
   elim H2; intros;clear H2.
   apply couple_rk1;auto.
   intuition.
   auto.

setoid_replace (inter (union ps(couple alpha beta))(union ps (singleton gamma)))
                        with ps by (clear_all;fsetdecide). 

unfold ps at 2.
rewrite rabc.
omega.

(*>=*)

assert (Hsubset : (Subset (union ps (couple alpha beta)) (union ps (triple alpha beta gamma))) )
by (clear_all;fsetdecide).
apply le_trans with (rk(union ps (couple alpha beta))).
2:apply (matroid2 (union ps (couple alpha beta))(union ps (triple alpha beta gamma)));
assumption.

assert (Hsubset' : (Subset (union ps (singleton alpha)) (union ps (couple alpha beta))) )
by (clear_all;fsetdecide).
generalize (matroid2 (union ps (singleton alpha)) (union ps (couple alpha beta))).
rewrite L1palpha.
solve[intuition].
Qed.


Lemma rPpalbega :  
  rk (union Ps (union ps (triple alpha beta gamma))) >= 4 \/ rk (triple alpha beta gamma) = 2.
Proof.
my_classical_left.
rename n into HnotDes.
assert(Hsubset:Subset (union Ps ps) (union Ps(union ps(triple alpha beta gamma))) )
by (unfold Ps, ps;(clear_all;fsetdecide)).
generalize (matroid2 (union Ps ps) (union Ps(union ps (triple alpha beta gamma))) Hsubset).
unfold Ps,ps.
omega.
Qed.

Ltac unfold_p := unfold Ps, ps.

Theorem Desargues_general : rk (triple alpha beta gamma) <= 2.
Proof.
assert (T: rk
         (union (union Ps (triple alpha beta gamma))
            (union ps (triple alpha beta gamma))) +
       rk (triple alpha beta gamma) <=
       rk (union Ps (triple alpha beta gamma)) +
       rk (union ps (triple alpha beta gamma))).
apply (matroid3_useful (union Ps (triple alpha beta gamma)) 
                                    (union ps (triple alpha beta gamma))
                                    (triple alpha beta gamma)).
(clear_all;fsetdecide).
setoid_replace (union (union Ps (triple alpha beta gamma))
     (union ps (triple alpha beta gamma))) with (union Ps (union ps (triple alpha beta gamma))) 
     in T by (unfold Equal; split; (clear_all;fsetdecide)).
assert (rk (union Ps (union ps (triple alpha beta gamma))) >= 4 \/
       rk (triple alpha beta gamma) = 2).
apply rPpalbega.
elim H0;intro.
rename H1 into HrPpalbega.
2:omega.
assert (rk (union ps (triple alpha beta gamma)) = 3 \/
       rk (triple alpha beta gamma) = 2).
apply L2p.
elim H1;intro.
rename H2 into HL2p.
2:omega.
rewrite HL2p in T.
assert ( rk (union Ps (triple alpha beta gamma)) = 3 \/
       rk (triple alpha beta gamma) = 2).
apply L2P.
elim H2;intro.
rename H3 into HL2P.
2:omega.
rewrite HL2P in T.
omega.
Qed.

End s_desargues3D.
