Require Export ProjectiveGeometry.Dev.matroid_to_matroid_p.

(*****************************************************************************)
(** Matroid properties **)


Section s_matroidProperties.

Context `{M : Matroid}.
Context `{EP : EqDecidability Point}.

Global Add Morphism couple : couple_mor.
Proof.
intros.
unfold couple.
rewrite H0.
rewrite H1.
fsetdecide.
Qed.

Lemma add_inj : forall x E E', 
 Equal E E' -> (Equal (add x E) (add x E')).
Proof.
intros.
rewrite H0.
fsetdecide.
Qed.

Global Add Morphism triple : triple_mor.
Proof.
intros.
unfold triple.
rewrite H0;clear H0.
apply add_inj.
rewrite H1; clear H1.
apply add_inj.
rewrite H2; clear H2.
fsetdecide.
Qed.

Global Add Morphism quadruple : quadruple_mor.
Proof.
intros.
unfold quadruple.
rewrite H0;clear H0.
apply add_inj.
rewrite H1; clear H1.
apply add_inj.
rewrite H2; clear H2.
apply add_inj.
rewrite H3.
fsetdecide.
Qed.

Lemma rk_singleton_le : forall p : Point, rk (singleton p) <= 1.
Proof.
generalize (matroid2' empty).
intro.
rewrite matroid1' in H0.
intro.
assert (HH:= H0 p).
setoid_replace (add p empty) with (singleton p) in HH.
omega.
fsetdecide.
Qed.

Lemma matroid1_b_useful :  forall X m,  cardinal X <= m -> rk X <= m.
Proof.
intros.
assert (rk X <= cardinal X).
apply matroid1_b;auto.
omega.
Qed.

Lemma cardinal_couple : forall p q, ~ p[==]q -> cardinal (couple p q) = 2.
Proof.
intros.
unfold couple.
repeat (rewrite (add_cardinal_2)).
rewrite empty_cardinal;auto.
fsetdecide.
fsetdecide.
Qed.

Lemma cardinal_triple : forall p q r, ~ p[==]q -> ~ p[==]r -> ~ q[==]r -> cardinal (triple p q r) <= 3.
Proof.
intros.
unfold triple.
repeat (rewrite (add_cardinal_2)).
rewrite empty_cardinal;auto.
fsetdecide.
fsetdecide.
fsetdecide.
Qed.

Lemma cardinal_quadruple : forall p q r s,
~ p[==]q -> ~ p[==]r -> ~ p[==]s ->
~ q[==]r -> ~ q[==]s -> ~ r[==]s -> cardinal (quadruple p q r s) <= 4.
Proof.
intros.
unfold quadruple.
repeat (rewrite (add_cardinal_2)).
rewrite empty_cardinal;auto.
fsetdecide.
fsetdecide.
fsetdecide.
fsetdecide.
Qed.

Lemma rk_couple_2 : forall p q : Point, rk(couple p q) <= 2.
Proof.
intros.
case_eq (eq_dec p q).
intros.
rewrite e.
setoid_replace (couple q q) with (singleton q) by fsetdecide.
apply matroid1_b_useful.
assert(cardinal {q} = 1);solve[intuition].
intros.
apply matroid1_b_useful.
rewrite cardinal_couple.
intuition.
intuition.
Qed.

Lemma rk_triple_le : forall A B C : Point, rk (triple A B C) <= 3.
Proof.
intros.
assert (T:=matroid2' (couple A B) C).
decompose [and] T;clear T.
setoid_replace (add C (couple A B)) with (triple A B C) in H1 by fsetdecide.
assert (rk (couple A B) <= 2) by apply rk_couple_2.
omega.
Qed.

Lemma rk_quadruple_le : forall A B C D : Point, rk (quadruple A B C D) <= 4.
Proof.
intros.
assert (T:=matroid2' (triple A B C) D).
decompose [and] T;clear T.
setoid_replace (add D (triple A B C)) with (quadruple A B C D) in H1 by fsetdecide.
assert (rk (triple A B C) <= 3) by apply rk_triple_le.
omega.
Qed.

Lemma matroid3'_gen : forall E A B, 
rk (union E A) = rk E ->
rk (union E B) = rk E ->
rk (union E (union A B)) = rk E.
Proof.
intros.
apply le_antisym.
setoid_replace (union E (union A B)) with (union (union E A) (union E B)) by fsetdecide.
assert (rk (union (union E A) (union E B)) + rk E <=
  rk (union E A) + rk (union E B)).
apply (matroid3_useful (union E A) (union E B) E).
fsetdecide.
rewrite H1 in H2.
rewrite H0 in H2.
omega.
apply matroid2.
fsetdecide.
Qed.

End s_matroidProperties.
