Require Export ProjectiveGeometry.Dev.matroid_properties.
Require Export ProjectiveGeometry.Dev.projective_space_or_higher_rank_axioms.

(*****************************************************************************)
(** Rank space or higher properties **)


Section s_rankProperties_1.

Context `{M : RankProjectiveSpaceOrHigher}.
Context `{EP : EqDecidability Point}.


Lemma rk_singleton : forall p : Point, rk (singleton p) = 1.
Proof.
intros.
assert (rk (singleton p)<= 1).
apply (rk_singleton_le);auto.
assert (rk (singleton p)>= 1).
apply (rk_singleton_ge);auto.
omega.
Qed.

Lemma rk_couple1 : forall p q : Point,~ p [==] q -> rk(couple p q)=2.
Proof.
intros.
assert (rk(couple p q)<=2).
apply (rk_couple_2).
assert (rk(couple p q)>=2).
apply (rk_couple_ge);auto.
omega.
Qed.

Lemma couple_rk1 : forall p q : Point, rk(couple p q) = 2 -> ~ p [==] q.
Proof.
intros.
unfold not;intro.
assert (rk (couple p q) = 1).
setoid_replace (couple p q) with (singleton p).
apply rk_singleton.
rewrite H1.
clear H0 H1.
fsetdecide.
rewrite H0 in H2.
inversion H2.
Qed.

Lemma couple_rk2 : forall p q : Point, rk (couple p q) = 1 -> p [==] q.
Proof.
intros.
case_eq(eq_dec p q).
intros.
assumption.
intro.
assert (rk(couple p q)=2).
apply rk_couple1;assumption.
rewrite H0 in H1.
assert False.
intuition.
intuition.
Qed.

Lemma rk_couple2 : forall p q : Point, p [==] q -> rk(couple p q) = 1.
Proof.
intros.
setoid_replace (couple p q) with (singleton p).
apply (rk_singleton).
rewrite H0.
fsetdecide.
Qed.

Lemma rk_couple_1 : forall p q, 1 <= rk (couple p q).
Proof.
intros.
case_eq(eq_dec p q).
intro.
rewrite rk_couple2.
omega.
assumption.
intro.
rewrite rk_couple1.
omega.
assumption.
Qed.

Lemma couple_rk_degen : forall p, rk (couple p p) = 2 -> False.
Proof.
intros.
assert (rk (couple p p) = 1).
setoid_replace (couple p p) with (singleton p).
apply rk_singleton.
fsetdecide.
intuition.
Qed.

Hint Resolve rk_singleton rk_couple1 rk_couple2 couple_rk1 couple_rk2 couple_rk_degen : rk.

Lemma base_points_distinct_1 : ~ P0 [==] P1.
Proof.
assert (T:= rk_lower_dim).
unfold not;intro.
rewrite H0 in T.
setoid_replace (quadruple P1 P1 P2 P3) with (triple P1 P2 P3) in T by fsetdecide.
assert (rk (triple P1 P2 P3) <= 3).
apply rk_triple_le.
omega.
Qed.

Lemma base_points_distinct_2 : ~ P2 [==] P3.
Proof.
assert (T:= rk_lower_dim).
unfold not;intro.
rewrite H0 in T.
setoid_replace (quadruple P0 P1 P3 P3) with (triple P0 P1 P3) in T by fsetdecide.
assert (rk (triple P0 P1 P3) <= 3).
apply rk_triple_le.
omega.
Qed.

Lemma rk_lemma_1 : forall A B P Q,
rk (couple A B) = 2 ->
rk (triple A B P) = 2 ->
rk (triple A B Q) = 2 ->
rk (quadruple A B P Q) = 2.
Proof.
intros.
assert (rk (union (triple A B P) (triple A B Q)) + rk (couple A B) <=
           rk (triple A B P) + rk (triple A B Q)).
apply (matroid3_useful (triple A B P) (triple A B Q) (couple A B)).
clear_all;fsetdecide.

assert (rk (union (triple A B P) (triple A B Q)) <= 2).
omega.
setoid_replace (union (triple A B P) (triple A B Q)) with (quadruple A B P Q) in H4.
apply le_antisym.
auto.
cut (rk (couple A B) <= rk (quadruple A B P Q)).
omega.
apply matroid2.
clear_all;fsetdecide.
clear_all;fsetdecide.
Qed.

End s_rankProperties_1.


Section s_rankProperties_2.

Context `{M : RankProjectiveSpaceOrHigher}.
Context `{EP : EqDecidability Point}.

Lemma col_trans : forall A B C D:Point, 
rk (triple A C D) = 2 -> rk (triple B C D) = 2 -> rk (couple C D) = 2 -> rk(triple A B C) <= 2.
Proof.
intros A B C D HACD HBCD HCD.
case_eq(eq_dec A B).
intros.
rewrite e.
setoid_replace (triple B B C) with (couple B C).
apply rk_couple_2.
clear_all;fsetdecide.

intros.
generalize (matroid3 (triple A C D) (triple B C D)).
rewrite HACD.
rewrite HBCD.
setoid_replace (inter (triple A  C D) (triple B C D)) with (couple C D).
rewrite HCD.
intros.
assert (rk (union (triple A C D) (triple B C D))<=2).
omega.
assert (Hsubset : Subset (triple A B C) (union (triple A C D) (triple B C D))).
clear_all;fsetdecide.
generalize (matroid2  (triple A B C) (union (triple A C D) (triple B C D)) Hsubset).
omega.
apply inter_fsetdecide_1.
assumption.
assumption.
Qed.

Lemma rk_triple_ABC_couple_AB : forall A B C, rk(triple A B C) = 3 -> rk(couple A B) = 2.
Proof.
intros A0 B0 C0 rABC0.
assert (rk(couple A0 B0)=1\/rk(couple A0 B0)=2).
assert (rk (couple A0 B0) <= 2).
apply (rk_couple_2 A0 B0).
assert (1 <= rk (couple A0 B0)).
apply (rk_couple_1 A0 B0).
omega.
elim H0.
2:auto.
intros H'.
rewrite (couple_rk2 A0 B0 H') in rABC0.
setoid_replace (triple B0 B0 C0) with (couple B0 C0) in rABC0.
assert (rk (couple B0 C0) <= 2).
apply (rk_couple_2 B0 C0).
omega.
clear_all;fsetdecide.
Qed.

Lemma rk_triple_ABC_couple_BC :  forall A B C, rk(triple A B C)=3 -> rk(couple B C)=2.
Proof.
intros.
eapply rk_triple_ABC_couple_AB with (C:=A).
setoid_replace (triple B C A) with (triple A B C).
assumption.
clear_all;fsetdecide.
Qed.

Lemma rk_triple_ABC_couple_AC :  forall A B C, rk(triple A B C)=3 -> rk(couple A C)=2.
Proof.
intros.
eapply rk_triple_ABC_couple_AB with (C:=B).
setoid_replace (triple A C B) with (triple A B C).
assumption.
clear_all;fsetdecide.
Qed.

Hint Resolve rk_triple_ABC_couple_AB rk_triple_ABC_couple_BC rk_triple_ABC_couple_AC : rk.

Lemma rk_triple_singleton :forall (x y z a:Point),
rk(triple x y z)=3 /\ rk(couple x a)=2 /\ rk(triple y z a)=2
-> rk(union (triple x y z) (singleton a))=3.
Proof.
intros a b c alpha H0.
elim H0;clear H0;intros rabc H0.
elim H0;clear H0;intros ranalpha rbcalpha.

assert (rab : rk (couple a b) =2).
eauto with rk.
assert (rac : rk (couple a c) =2).
eauto with rk.
assert (rbc : rk (couple b c) =2).
eauto with rk.

apply le_antisym.
(* <= *)
assert (T: rk (union (triple a b c) (triple b c alpha)) + rk (couple b c) <=
    rk (triple a b c) + rk (triple b c alpha)).
apply (matroid3_useful (triple a b c) (triple b c alpha) (couple b c)).
clear_all;fsetdecide.
setoid_replace  (union (triple a b c) (triple b c alpha))
                 with (union (triple a b c) (singleton alpha)) in T.
omega.
clear_all;fsetdecide.

(* >= *)
assert (Hsubset : (Subset (triple a b c) (union (triple a b c) (singleton alpha)))).
clear_all;fsetdecide.
generalize (matroid2 (triple a b c) (union (triple a b c) (singleton alpha)) Hsubset).
rewrite rabc.
auto.
Qed.

Hint Resolve  rk_triple_singleton : rk.

Lemma rk_couple_not_zero : forall A B, (rk (couple A B) = 0) -> False.
Proof.
unfold not; intros.
elim (eq_dec A B);intros.
generalize (rk_couple2 A B).
intuition.
generalize (rk_couple1 A B).
intuition.
Qed.

Hint Resolve rk_couple_not_zero : rk.

Lemma L1beta_gen : forall A B C beta, 
rk(triple A C beta) = 2  -> 
rk (triple A B C) = 3 -> 
rk(union (triple A B C) (singleton beta))=3.
Proof.
intros  A B C beta.
intro rACbeta.
intro rABC.
apply le_antisym.
assert (T : rk (union (triple A B C) (triple A C beta)) + rk (couple A C) <=
       rk (triple A B C) + rk (triple A C beta)).
apply (matroid3_useful (triple A B C) (triple A C beta) (couple A C)).
clear_all;fsetdecide.
setoid_replace (union(triple A B C)(triple A C beta)) with (union(triple A B C)(singleton beta)) in T.
assert (HrAC : rk (couple A C) = 2) by eauto with rk.
omega.
clear_all;fsetdecide.

(*>=*)
assert( Hsubset : (Subset (triple A B C) (union (triple A B C) (singleton beta)))).
clear_all;fsetdecide.
generalize (matroid2 (triple A B C) (union (triple A B C) (singleton beta)) Hsubset).
rewrite rABC.
auto.
Qed.

Lemma L1gamma_gen : forall A B C gamma, 
rk (triple A B C) = 3 ->
rk (triple A B gamma) = 2 ->
rk(union (triple A B C) (singleton gamma))=3.
Proof.
intros.
setoid_replace (union (triple A B C) (singleton gamma)) 
with (union (triple A C B) (singleton gamma)).
apply L1beta_gen.
assumption.
setoid_replace (triple A B C) with (triple A C B) in H0.
assumption.
clear_all;fsetdecide.
clear_all;fsetdecide.
Qed.

Lemma coplanar : forall O A B C A' B' C' : Point,
rk (triple A B C ) = 3 ->
rk (couple A' B) = 2 ->
rk (couple C' B) = 2 ->
rk (couple A B') = 2 ->
rk (couple B' C) = 2 ->
rk (triple A' B' C' ) = 3 ->
rk (triple O B B')  = 2 ->
rk (union (couple O A) (triple C A' C')) = 2 ->
rk (union (triple A B C) (triple A' B' C')) <> 4.
Proof.
intros O A B C A' B' C'.
intro rABC.
intro rA'B.
intro rC'B.
intro rAB'.
intro rB'C.
intro rA'B'C'.
intro rOBB'.
intro rOACA'C'.
unfold not.
intro.
assert (T: rk (union (triple O B B') (union (couple O A) (triple C A' C'))) +
      rk (singleton O) <=
      rk (triple O B B') + rk (union (couple O A) (triple C A' C'))).
apply (matroid3_useful  (triple O B B') (union (couple O A) (triple C A' C')) (singleton O)).
clear_all;fsetdecide.
rewrite rOBB' in T.
rewrite rOACA'C' in T.
rewrite rk_singleton in T.
assert (rk (union (triple A B C) (triple A' B' C')) <=
    rk (union (singleton O) (union (triple A B C) (triple A' B' C')))).
apply matroid2.
clear_all;fsetdecide.
setoid_replace ((union (singleton O) (union (triple A B C) (triple A' B' C')))) with (union (triple O B B') (union (couple O A) (triple C A' C'))) in H1.
omega.
unfold Equal; split.
clear_all;fsetdecide.
clear_all;fsetdecide.
Qed.

Lemma rk_quadruple_ABCD_couple_AB :  
forall A B C D, rk(add D (triple A B C))>=4 -> rk(couple A B)=2.
Proof.
intros A0 B0 C0 D0 rABCD0.
assert (rk(couple A0 B0)=1\/rk(couple A0 B0)=2).

assert (rk (couple A0 B0) <= 2).
apply (rk_couple_2 A0 B0).
assert (1 <= rk (couple A0 B0)).
apply (rk_couple_1 A0 B0).
omega.
elim H0.
2:auto.
intros H'.
rewrite (couple_rk2 A0 B0 H') in rABCD0.
setoid_replace (add D0 (triple B0 B0 C0)) with (triple B0 C0 D0) in rABCD0.
assert (rk (triple B0 C0 D0) <= 3) by apply (rk_triple_le B0 C0 D0).
omega.
clear_all;fsetdecide.
Qed.

Lemma rk_quadruple_ABCD_couple_AC :  
forall A B C D, rk(add D (triple A B C))>=4 -> rk(couple A C)=2.
Proof.
intros A0 B0 C0 D0 rABCD0.
eapply (rk_quadruple_ABCD_couple_AB A0 C0 B0 D0).
setoid_replace (add D0 (triple A0 C0 B0)) with (add D0 (triple A0 B0 C0)) by (clear_all;fsetdecide).
assumption.
Qed.

Lemma rk_quadruple_ABCD_couple_AD :  
forall A B C D, rk(add D (triple A B C))>=4 -> rk(couple A D)=2.
Proof.
intros A0 B0 C0 D0 rABCD0.
eapply (rk_quadruple_ABCD_couple_AB A0 D0 B0 C0).
setoid_replace (add C0 (triple A0 D0 B0)) with (add D0 (triple A0 B0 C0)) by (clear_all;fsetdecide).
assumption.
Qed.

Lemma rk_quadruple_ABCD_couple_BC :  
forall A B C D, rk(add D (triple A B C))>=4 -> rk(couple B C)=2.
Proof.
intros A0 B0 C0 D0 rABCD0.
eapply (rk_quadruple_ABCD_couple_AB B0 C0 D0 A0).
setoid_replace (add D0 (triple A0 B0 C0)) with (add A0 (triple B0 C0 D0)) in rABCD0 by (clear_all;fsetdecide).
assumption.
Qed.

Lemma rk_quadruple_ABCD_couple_BD :  
forall A B C D, rk(add D (triple A B C))>=4 -> rk(couple B D)=2.
Proof.
intros A0 B0 C0 D0 rABCD0.
eapply (rk_quadruple_ABCD_couple_AB B0 D0 C0 A0).
setoid_replace (add A0 (triple B0 D0 C0)) with (add D0 (triple A0 B0 C0)) by (clear_all;fsetdecide).
assumption.
Qed.

Lemma rk_quadruple_ABCD_couple_CD :  
forall A B C D, rk(add D (triple A B C))>=4 -> rk(couple C D)=2.
Proof.
intros A0 B0 C0 D0 rABCD0.
eapply (rk_quadruple_ABCD_couple_AB C0 D0 A0 B0).
setoid_replace (add B0 (triple C0 D0 A0)) with (add D0 (triple A0 B0 C0)) by (clear_all;fsetdecide).
assumption.
Qed.

Lemma rk_quadruple_ABCD_triple_ABC :  
forall A B C D, rk(add D (triple A B C))>=4 -> rk(triple A B C)=3.
Proof.
intros A0 B0 C0 D0 rABCD0.
apply le_antisym.
apply rk_triple_le.
assert (rk (triple A0 B0 C0) <=
             rk (add D0 (triple A0 B0 C0)) <=
             rk (triple A0 B0 C0) + 1).
apply matroid2';auto.
intuition.
Qed.

Lemma intersecting_lines_rank_3 : forall A B C D I,
rk (triple A B I) <= 2 ->
rk (triple C D I) <= 2 ->
rk (union (singleton I) (quadruple A B C D)) <= 3.
Proof.
intros.
assert (rk (union (triple A B I) (triple C D I)) +
       rk (singleton I) <=
       rk (triple A B I) + rk (triple C D I)).
apply (matroid3_useful (triple A B I) (triple C D I) (singleton I)).
fsetdecide.
rewrite rk_singleton in H2.
setoid_replace (union (triple A B I) (triple C D I)) 
with (union (singleton I) (quadruple A B C D)) in H2.
omega.
unfold Equal; split;clear_all;fsetdecide.
Qed.

(** Uniqueness of inter *)
Lemma uniq_inter : 
forall A B C D P Q, 
rk(couple A B)=2 -> 
rk(couple C D) = 2 ->
rk(triple A B P) <= 2 -> 
rk(triple C D P) <= 2 -> 
rk(triple A B Q) <= 2 ->
rk(triple C D Q) <= 2 -> 
rk(quadruple A B C D) >= 3 -> 
rk(couple P Q) = 1.
Proof.
intros A B C D P Q rAB rCD rABM rCDM rABP rCDP rABCD.
apply le_antisym.

assert (rk(add Q (triple A B P))<=2).
generalize (matroid3 (triple A B P) (triple A B Q)).
setoid_replace (union (triple A B P) (triple A B Q)) 
with (add Q (triple A B P)).
assert (rk (inter (triple A B P) (triple A B Q))>=rk(couple A B)).
apply matroid2.
clear_all;fsetdecide.
omega.
clear_all;fsetdecide.
assert (rk(add Q (triple C D P))<=2).
generalize (matroid3 (triple C D P) (triple C D Q)).
setoid_replace (union (triple C D P) (triple C D Q)) 
with (add Q (triple C D P)).
assert (rk (inter (triple C D P) (triple C D Q))>=rk(couple C D)).
apply matroid2.
clear_all;fsetdecide.
omega.
clear_all;fsetdecide.
assert(rk(union (triple A B C) (triple D P Q))>=3).
assert(rk (quadruple A B C D) <= 3).
assert (rk (union (singleton P) (quadruple A B C D)) <= 3).
apply (intersecting_lines_rank_3 A B C D P);auto.
assert (rk (quadruple A B C D) <=
       rk (union (singleton P) (quadruple A B C D))).
apply matroid2.
clear_all;fsetdecide.
omega.
assert (rABCD' : rk (quadruple A B C D) = 3).
omega.
rewrite <- rABCD'.
apply matroid2.
clear_all;fsetdecide.

generalize (matroid3 (add Q (triple A B P))  (add Q (triple C D P))).
setoid_replace (union (add Q (triple A B P)) (add Q (triple C D P))) with
(union (triple A B C) (triple D P Q)).
assert (rk((inter (add Q (triple A B P)) (add Q (triple C D P))))>=rk(couple P Q)).
apply matroid2.
clear_all;fsetdecide.
omega.
clear_all;fsetdecide.
apply rk_couple_1.
Qed.

Lemma uniq_inter_spec : forall gamma a b B,
rk (triple a b gamma) <= 2 ->
rk (triple a B gamma) <= 2 ->
rk (triple a b B) >= 3 ->
rk (couple a gamma) = 1.
Proof.
intros.
case_eq (eq_dec a gamma).
intros.
rewrite e.
setoid_replace (couple gamma gamma) with (singleton gamma).
apply rk_singleton.
clear_all;fsetdecide.
intros.
assert(rk(couple a gamma)=2).
apply rk_couple1.
assumption.
assert (rk (union (triple a b gamma) (triple a B gamma)) + rk (couple a gamma) <=
       rk (triple a b gamma) + rk (triple a B gamma)).
apply matroid3_useful.
clear_all;fsetdecide.
assert (rk (quadruple a b B gamma) <= 2).
setoid_replace (quadruple a b B gamma) with  (union (triple a b gamma) (triple a B gamma)).
omega.
clear_all;fsetdecide.
assert (rk (triple a b B)  <= rk (quadruple a b B gamma)).
apply matroid2.
clear_all;fsetdecide.
omega.
Qed.

Lemma uniq_inter_spec_bis : forall gamma a b B,
rk (triple a b gamma) <= 2 ->
rk (triple a B gamma) <= 2 ->
rk (couple a gamma) = 1 \/  rk (triple a b B) <= 2.
Proof.
intros.
assert (rk (triple a b B) <= 2 \/ rk (triple a b B) >= 3).
omega.
elim H2;intro.
right; auto.
left.
eapply (uniq_inter_spec).
apply H0.
apply H1.
auto.
Qed.

Lemma stays_in_plane : forall E a b x, rk(E)<=3 -> In a E -> In b E -> 
rk(couple a b)=2->
rk(triple a b x)=2 -> 
rk(add x E)<=3.
Proof.
intros E m n x.
intros.
generalize (matroid3 E (triple m n x)).
assert (rk (union E (triple m n x))>=rk (add x E)).
apply matroid2.
clear_all;fsetdecide.
assert (rk(inter E (triple m n x))>=rk(couple m n)).
apply matroid2.
clear_all;fsetdecide.
omega.
Qed.

Lemma stays_in_the_plane : forall R N P Q,
rk(triple R N P) = 3 -> rk(triple R N Q) = 2 -> rk(add Q (triple R N P)) = 3.
Proof.
intros R N P Q rRNP rRNQ.
assert (rk(couple R N) = 2).
eapply rk_triple_ABC_couple_AB.
eassumption.
apply le_antisym.
generalize (matroid3 (triple R N P) (triple R N Q)).
setoid_replace (union (triple R N P) (triple R N Q)) 
with (add Q (triple R N P)).
assert (rk(inter (triple R N P) (triple R N Q))>=rk(couple R N)).
apply matroid2.
clear_all;fsetdecide.
omega.
clear_all;fsetdecide.
rewrite <- rRNP.
apply matroid2.
clear_all;fsetdecide.
Qed.

(** How to remove a point from a flat of 4 points whose rank is 3 ? *) 
Lemma rk2_3 : forall P Q R S, 
rk(add S (triple P Q R)) = 3->
rk(triple P Q R)=2->
rk(couple P Q)=2 ->
rk(couple R S)=2 ->
rk(triple P Q S)=3.
Proof.
intros X Y Z T HXYZT HXYZ HXY HZT.
apply le_antisym.
apply rk_triple_le.
generalize (matroid3 (triple X Y Z) (triple X Y T)).
setoid_replace (union (triple X Y Z) (triple X Y T)) with (add T (triple X Y Z)).
rewrite HXYZT.
assert (rk  (inter (triple X Y Z) (triple X Y T))>=rk (couple X Y)).
apply matroid2.
clear_all;fsetdecide.
omega.
clear_all;fsetdecide.
Qed.

(** changing one of the points defining a plane in a 3D figure *)
Lemma rk3_4 : forall A B C M P,
rk(add M (triple A B C)) = 3 ->
rk(triple B C M) = 3 -> 
rk(add P (triple A B C)) >= 4 ->
rk(add P (triple M B C)) >= 4.
Proof.
intros A B C Q P rABCQ rBCQ rABCP.
generalize (matroid3 (add P (triple Q B C)) (add Q (triple A B C))).
setoid_replace  (union (add P (triple Q B C)) (add Q (triple A B C))) with
(union (triple A B C) (couple Q P)).
assert  (rk (inter (add  P (triple Q B C)) (add Q (triple A B C)))>= rk (triple B C Q)).
apply matroid2.
clear_all;fsetdecide.
assert (rk(union (triple A B C) (couple Q P)) >= rk(add P (triple A B C))).
apply matroid2.
clear_all;fsetdecide.
omega.
clear_all;fsetdecide.
Qed.

Lemma rank_not_empty : forall E, (exists x, In x E) -> rk E > 0.
Proof.
intros.
elim H0; intros x H2; clear H0.
assert (Subset (singleton x) E) by fsetdecide.
assert (rk (singleton x) <= rk E) by (apply matroid2; fsetdecide).
rewrite rk_singleton in H1.
omega.
Qed.

Lemma double_flag : forall  x A B, 
rk (add x A) <= 2 ->
rk (add x B) <= 2 ->
rk (add x (union A B)) <= 3.
Proof.
intros.
assert (rk (union (add x A) (add x B)) + rk (singleton x) <=
       rk (add x A) + rk (add x B)).
apply (matroid3_useful).
fsetdecide.
rewrite rk_singleton in H2.
setoid_replace (add x (union A B))  with (union (add x A) (add x B)) by fsetdecide.
omega.
Qed.

Lemma construction : 
 forall n , forall E, rk E = n -> n<=3 -> exists P, rk (add P E) = n+1.
Proof.
intros.
assert (T:= rk_lower_dim).
assert (rk (quadruple P0 P1 P2 P3) = 4).
apply le_antisym.
apply rk_quadruple_le.
auto.
clear H2.
assert (n=0 \/ n=1 \/ n=2 \/ n=3) by omega.

(** Case n=0 *)
intuition.
subst.
rewrite H3.
assert (rk (add P0 E) = 0 \/ rk (add P0 E) = 1).
assert (rk E <= rk (add P0 E) <= rk E + 1) by apply matroid2'.
omega.
assert (rk (add P1 E) = 0 \/ rk (add P1 E) = 1).
assert (rk E <= rk (add P1 E) <= rk E + 1) by apply matroid2'.
omega.
assert (rk (add P2 E) = 0 \/ rk (add P2 E) = 1).
assert (rk E <= rk (add P2 E) <= rk E + 1) by apply matroid2'.
omega.
assert (rk (add P3 E) = 0 \/ rk (add P3 E) = 1).
assert (rk E <= rk (add P3 E) <= rk E + 1) by apply matroid2'.
omega.

elim H0;intro;[idtac|firstorder];clear H0.
elim H2;intro;[idtac|firstorder];clear H2.
elim H4;intro;[idtac|firstorder];clear H4.
elim H5;intro;[idtac|firstorder];clear H5.
assert (rk E = rk (union E (couple P0 P1))).
eapply matroid3';solve[intuition]. 

rewrite H3 in H5.
assert (rk (couple P0 P1) <= rk  (union E (couple P0 P1))).
apply matroid2;fsetdecide.
assert (rk (couple P0 P1) <= 0) by omega.
assert (rk (couple P0 P1) >= 1).
apply rk_couple_1.
cut False;intuition.

(** Case n=1 *)
subst.
rewrite H2.
assert (rk (add P0 E) = 1 \/ rk (add P0 E) = 2).
assert (rk E <= rk (add P0 E) <= rk E + 1) by apply matroid2'.
omega.
assert (rk (add P1 E) = 1 \/ rk (add P1 E) = 2).
assert (rk E <= rk (add P1 E) <= rk E + 1) by apply matroid2'.
omega.
assert (rk (add P2 E) = 1 \/ rk (add P2 E) = 2).
assert (rk E <= rk (add P2 E) <= rk E + 1) by apply matroid2'.
omega.
assert (rk (add P3 E) = 1 \/ rk (add P3 E) = 2).
assert (rk E <= rk (add P3 E) <= rk E + 1) by apply matroid2'.
omega.
elim H0;intro;[idtac|firstorder];clear H0.
elim H4;intro;[idtac|firstorder];clear H4.
elim H3;intro;[idtac|firstorder];clear H3.
elim H5;intro;[idtac|firstorder];clear H5.
assert (rk E = rk (union E (couple P0 P1))).
eapply matroid3';solve[intuition]. 

assert (rk E = rk (union E (couple P2 P3))).
apply matroid3';solve[intuition].

assert (rk (union E (union (couple P0 P1) (couple P2 P3))) =rk E).
apply (matroid3'_gen E (couple P0 P1) (couple P2 P3));symmetry;auto.
rewrite H2 in H8.
assert (rk (quadruple P0 P1 P2 P3) <= rk (union E (union (couple P0 P1) (couple P2 P3)))).
apply (matroid2).
clear_all;fsetdecide.
cut False;intuition.

subst.
rewrite H3.
assert (rk (add P0 E) = 2 \/ rk (add P0 E) = 3).
assert (rk E <= rk (add P0 E) <= rk E + 1) by apply matroid2'.
omega.
assert (rk (add P1 E) = 2 \/ rk (add P1 E) = 3).
assert (rk E <= rk (add P1 E) <= rk E + 1) by apply matroid2'.
omega.
assert (rk (add P2 E) = 2 \/ rk (add P2 E) = 3).
assert (rk E <= rk (add P2 E) <= rk E + 1) by apply matroid2'.
omega.
assert (rk (add P3 E) = 2 \/ rk (add P3 E) = 3).
assert (rk E <= rk (add P3 E) <= rk E + 1) by apply matroid2'.
omega.
elim H0;intro;[idtac|firstorder];clear H0.
elim H2;intro;[idtac|firstorder];clear H2.
elim H4;intro;[idtac|firstorder];clear H4.
elim H5;intro;[idtac|firstorder];clear H5.

assert (rk E = rk (union E (couple P0 P1))).
eapply matroid3';solve[intuition].

assert (rk E = rk (union E (couple P2 P3))).
apply matroid3';solve[intuition].

assert (rk (union E (union (couple P0 P1) (couple P2 P3))) =rk E).
apply (matroid3'_gen E (couple P0 P1) (couple P2 P3));symmetry;auto.
rewrite H3 in H8.
assert (rk (quadruple P0 P1 P2 P3) <= rk (union E (union (couple P0 P1) (couple P2 P3)))).
apply (matroid2).
clear_all;fsetdecide.
cut False;intuition.

subst.
rewrite H3.
assert (rk (add P0 E) = 3 \/ rk (add P0 E) = 4).
assert (rk E <= rk (add P0 E) <= rk E + 1) by apply matroid2'.
omega.
assert (rk (add P1 E) = 3 \/ rk (add P1 E) = 4).
assert (rk E <= rk (add P1 E) <= rk E + 1) by apply matroid2'.
omega.
assert (rk (add P2 E) = 3 \/ rk (add P2 E) = 4).
assert (rk E <= rk (add P2 E) <= rk E + 1) by apply matroid2'.
omega.
assert (rk (add P3 E) = 3 \/ rk (add P3 E) = 4).
assert (rk E <= rk (add P3 E) <= rk E + 1) by apply matroid2'.
omega.
elim H0;intro;[idtac|firstorder];clear H0.
elim H2;intro;[idtac|firstorder];clear H2.
elim H4;intro;[idtac|firstorder];clear H4.
elim H5;intro;[idtac|firstorder];clear H5.

assert (rk E = rk (union E (couple P0 P1))).
apply matroid3';solve[intuition].

assert (rk E = rk (union E (couple P2 P3))).
apply matroid3';solve[intuition]. 

assert (rk (union E (union (couple P0 P1) (couple P2 P3))) =rk E).
apply (matroid3'_gen E (couple P0 P1) (couple P2 P3));symmetry;auto.
rewrite H3 in H8.
assert (rk (quadruple P0 P1 P2 P3) <= rk (union E (union (couple P0 P1) (couple P2 P3)))).
apply (matroid2).
clear_all;fsetdecide.
cut False;intuition.
Qed.

End s_rankProperties_2.

Hint Resolve rk_singleton rk_couple1 rk_couple2 couple_rk1 couple_rk2 couple_rk_degen : rk_base.