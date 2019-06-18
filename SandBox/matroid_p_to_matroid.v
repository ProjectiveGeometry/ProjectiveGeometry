Require Export Omega.
Require Export matroid_axioms.

(*****************************************************************************)
(** Proof of matroid' to matroid **)


Section s_matroid'ToMatroid.

Context `{M : Matroid'}.

Lemma rk_compat:
  forall x x', Equal x x' ->
     rk x = rk x'.
Proof.
intros;apply rk_compat;assumption.
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

Lemma matroid1_a : forall X, rk X >= 0.
Proof.
apply set_induction.
intros.
setoid_replace s with empty.
generalize matroid1';omega.
fsetdecide.
intros.
assert (rk s <= rk (add x s) <= rk s + 1).
apply matroid2'.
omega.
Qed.

Lemma matroid1_b : forall X, rk X <= cardinal X.
Proof.
apply set_induction.
intros.
setoid_replace s with empty by fsetdecide.
rewrite matroid1';auto.
omega.

intros.
assert (rk s <= rk (add x s) <= rk s + 1).
apply matroid2'.
assert (cardinal s' = S (cardinal s)).
eapply cardinal_2;eauto.
rewrite H4.
setoid_replace s' with (add x s).
omega.
rewrite <- Add_Equal;auto.
Qed.

Lemma singleton_eq : forall x y, In y (singleton x) -> x [==] y.
Proof.
intros.
fsetdecide.
Qed.

Hint Resolve singleton_eq.

Lemma set_fact_1 : forall x E A E' , ~ In x A -> ~ In x E -> 
Equal (union E (add x A)) E' ->
Equal (union E A) (diff E' (singleton x)).
Proof.
intros.
assert(HH : ~ (In x (A ++ E))).
fsetdec.
rewrite <-H2.
clear H0 H1 H2.
fsetdecide.
Qed.

Lemma set_fact_2 : forall E E' x, 
 Subset E E' -> 
 ~ In x E -> 
 Subset E (diff E' (singleton x)).
Proof.
intros.
fsetdecide.
Qed.

Lemma set_fact_3: forall e', forall x : Point, 
In x e'  -> Equal (add x (diff e' (singleton x))) e'.
Proof.
intros.
assert(HH := add_remove H0).
fsetdecide.
Qed.

Lemma matroid2:
   forall e e',Subset e e' -> rk(e)<=rk(e').
Proof.
intros.
elim (subset_exists e e' H0).
intros e'' He.

generalize H0; clear H0.
generalize He; clear He.
generalize e; clear e.
generalize e'; clear e'.
generalize e''; clear e''.
 
apply (set_induction (P:= fun e'' => forall (e' e : Set_of_points),
Equal (union e e'') e' -> Subset e e' -> rk e <= rk e')).
intros.
assert (Equal e e').
fsetdecide.
rewrite H3;auto.

intros.

elim (In_dec x e);intro.
apply (H0 e' e).
setoid_replace (union e s') with (union e s) in H3.
auto.
setoid_replace s' with (add x s) in H3 by (apply -> Add_Equal;auto).
setoid_replace s' with (add x s) by (apply -> Add_Equal;auto).
clear H0 H1 H2 H3 H4.
fsetdecide.
auto.

assert (Equal (union e s) (diff e' (singleton x))).
apply set_fact_1;auto.
setoid_replace s' with (add x s) in H3 by (apply -> Add_Equal;auto).
auto.

assert (Subset e (diff e' (singleton x))).
apply set_fact_2;auto.
assert (T:= H0 (diff e' (singleton x)) e H5 H6).

assert (rk (diff e' (singleton x)) <= rk (add x (diff e' (singleton x))))
by (generalize (matroid2' (diff e' (singleton x)) x); intros;intuition).
assert (Equal (add x (diff e' (singleton x))) e').
apply set_fact_3.
setoid_replace s' with (add x s) in H3 by (apply -> Add_Equal;auto).
rewrite <- H3.
clear H0 H1 H2 H3 H4 H5 H6 H7.
fsetdecide.

rewrite H8 in H7.
omega.
Qed.


Lemma matroid3:
forall e e', rk(union e e') + rk(inter e e') <= rk(e) + rk(e'). 
Proof.
apply (set_induction (P:= fun e => forall e' : set Point, 
rk (e ++ e')%set + rk (inter e e') <= rk e + rk e')).

intros.
assert(HH : Equal (s ++ e') e').
fsetdecide.
assert(HH0 : Equal (inter s e') s).
fsetdecide.
rewrite HH.
rewrite HH0.
omega.

intros.
assert(HH := Add_Equal x s s').
assert(HH0 : Equal s' {x; s}).
intuition.
rewrite HH0.

case_eq(In_dec x e').
intros.
assert(HH1 : Equal ({x;s} ++ e') (s ++ e')).
clear H1 H2 HH HH0.
fsetdecide.
assert(HH2 : Equal ({x;inter s e'}) (inter {x;s} e')).
clear H1 H2 HH HH0 H3 HH1.
fsetdecide.
rewrite HH1.
rewrite <-HH2.
assert(HH3 := matroid2' s x).
assert(HH4 := matroid2' (inter s e') x).


(*

apply le_trans with(m:= rk s + rk e').
2:omega.
apply le_trans with (m:= rk (union s e') + rk ((inter s e') + 1)).
admit.
omega.

intros.
assert(HH2 : Equal (inter {x;s} e') (inter s e')).
clear H0 H2 HH HH0.
apply inter_add_2.
assumption.
rewrite HH2.
*)

(*
apply le_trans with (m:= rk ( union s e') + rk (inter s e')).
fsetdec.
*)

(*
generalize s'.
apply (set_induction (P:= fun e' => forall s'0: set Point, 
rk (s'0 ++ e')%set + rk (inter s'0 e') <= rk s'0 + rk e')).

intros.
assert(HH : Equal (s'0 ++ s0) s'0).
fsetdecide.
assert(HH0 : Equal (inter s'0 s0) s0).
fsetdecide.
rewrite HH.
rewrite HH0.
omega.

intros.
assert(HH := matroid3').


intros.
apply (set_induction (P:= fun e' => 
rk (s' ++ e')%set + rk (inter s' e') <= rk s' + rk e')).

intros.
assert(HH : Equal (s' ++ s0) s').
fsetdecide.
assert(HH0 : Equal (inter s' s0) s0).
fsetdecide.
rewrite HH.
rewrite HH0.
omega.

intros.

*)

Admitted.

End s_matroid'ToMatroid.
