Require Export Omega.
Require Export ProjectiveGeometry.Dev.matroid_axioms.

(*****************************************************************************)
(** Proof of matroid to matroid' **)


Ltac clear_all := repeat match goal with 
| H: rk _ = _ |-_ => clear H
| H: rk _ <> _|-_ => clear H
| H: rk _ >= _ |-_ => clear H
| H: rk _ <= _ |-_ => clear H
| H: rk _ = _ \/ _ |-_ => clear H
| H: rk _ >= _ \/ _ |-_ => clear H
| H: rk _ <= _ \/ _ |-_ => clear H
| H: rk _ + _ = _ |- _ => clear H
| H: rk _ + _ >= _ |- _ => clear H
| H: rk _ + _ <= _ |- _ => clear H
end.

Section s_matroidToMatroid'.

Context `{M : Matroid}.

Lemma rk_compat:
  forall x x', Equal x x' ->
     rk x = rk x'.
Proof.
intros.
apply le_antisym;apply matroid2;firstorder.
Qed.

(*
Global Add Morphism rk : rk_mor.
Proof.
 exact rk_compat.
Qed.
*)

Global Instance rk_mor : Proper (Equal ==> Logic.eq) rk.
Proof.
 exact rk_compat.
Qed.

Lemma matroid1' : rk empty = 0.
Proof.
assert(cardinal empty = 0).
intuition.
assert (rk empty >= 0).
apply matroid1_a.
assert (rk empty <= cardinal empty).
apply matroid1_b.
rewrite H0 in H2.
omega.
Qed.

Lemma rk_singleton : forall x, rk (singleton x) <= 1.
Proof.
intros.
assert(cardinal {x}%set = 1).
intuition.
rewrite <-H0.
apply matroid1_b.
Qed.

Lemma matroid2' : forall X : set Point, forall x : Point, 
rk(X) <= rk (add x X) <= rk(X) + 1.
Proof.
intros.
split.
apply (matroid2).
fsetdecide.
assert (rk (union X (singleton x)) + rk (inter X (singleton x)) <=
       rk X + rk (singleton x)).
apply matroid3.
elim (In_dec x X).
intro.
setoid_replace (inter X (singleton x)) with (singleton x) in H0.
setoid_replace (union X (singleton x)) with (union (singleton x) X) in H0.
rewrite <- add_union_singleton in H0.
omega.

unfold Equal;intro.
split.
fsetdecide.
intros.
fsetdecide.
fsetdecide.
intro.
setoid_replace (inter X (singleton x)) with (empty) in H0.
replace (rk empty) with 0 in H0.
assert (rk (singleton x) <= 1).
apply rk_singleton.
rewrite union_sym in H0.
rewrite <- add_union_singleton in H0.
omega.
symmetry.
apply matroid1'.

unfold Equal;intro.
split.
clear H0.
fsetdecide.

autorewrite with set_simpl in *.
intuition.
apply S0.
apply S0.
apply S0.
Qed.

Lemma matroid3_useful : forall e e' ei : set Point,
 Subset ei (inter e e') ->
 rk(union e e') + rk(ei) <= rk(e) + rk(e').
Proof.
intros.
assert (rk (union e e') + rk (inter e e') <= rk e + rk e').
apply matroid3.
assert (rk (ei) <= rk (inter e e')).
apply matroid2;auto.
omega.
Qed.

Lemma add_union_singleton_sym : forall s, forall x, 
Equal (add x s) (union s (singleton x)).
Proof.
intros.
rewrite union_sym.
apply add_union_singleton.
Qed.

Lemma matroid3': forall X y z, 
   rk(add y X) = rk(add z X) ->
   rk(add z X) = rk(X) ->
   rk(X) = rk(union X (couple y z)).
Proof.
intros.
assert (rk(X) <= rk(union X (couple y z))).
apply matroid2.
fsetdecide.
assert  (rk(union X (couple y z)) <= rk(X)).
assert ( rk (union (union X (singleton y)) (union X (singleton z))) + rk X <=
       rk (union X (singleton y)) + rk (union X (singleton z))).
apply matroid3_useful.
clear_all;fsetdecide.
repeat (rewrite <- add_union_singleton_sym in H3).
setoid_replace (union (add y X) (add z X)) with (union X (couple y z)) in H3.
omega.
clear_all;fsetdecide.
omega.
Qed.

End s_matroidToMatroid'.