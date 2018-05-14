Require Export ProjectiveGeometry.Dev.decidability.
Require Export Containers.SetInterface.
Require Export Containers.SetDecide.
Require Export Containers.SetProperties.

(*****************************************************************************)
(** SetOfPoints Structure **)

(*
Section s_SetOfPoints.

Class SetOfPoints  `(Op : ObjectPoint) `(Eq : EqDecidability Point) `(S : FSetSpecs Point).

End s_SetOfPoints.
*)

Section s_matroidRk.

Class MatroidRk `(Op : ObjectPoint) `(S : FSetSpecs Point) := {
rk : set Point -> nat
}.

End s_matroidRk.

Section s_SetOfPointsDef.

Context `(MR : MatroidRk).

Definition couple (x y : Point) : set Point :=
add x (add y (empty)).

Definition triple(x y t : Point) : set Point :=
add x (add y (add t empty)).

Definition quadruple (x y t u : Point) : set Point :=
add x (add y (add t  (add u empty))).

Definition quintuple (x y t u v : Point) : set Point :=
add x (add y (add t  (add u (add v empty)))).

(*****************************************************************************)

Lemma couple_singleton_eq : forall x y, x [==] y -> 
Equal (couple x y) (singleton x).
Proof.
intros;unfold couple;fsetdec.
Qed.

Lemma subset_exists : forall A B, Subset A B -> exists C, Equal (union A C) B.
Proof.
intros;exists (diff B A);fsetdec.
Qed.

Lemma couple_1 : forall a b, Equal (couple a b) (couple b a).
Proof.
intros;unfold couple;fsetdec.
Qed.

Lemma triple_1 : forall a b c, Equal (triple a b c) (triple a c b).
Proof.
intros;unfold triple;fsetdec.
Qed.

Lemma triple_2 : forall a b c, Equal (triple a b c) (triple b a c).
Proof.
intros;unfold triple;fsetdec.
Qed.

Lemma triple_3 : forall a b c, Equal (triple a b c) (triple b c a).
Proof.
intros;unfold triple;fsetdec.
Qed.

Lemma triple_4 : forall a b c, Equal (triple a b c) (triple c a b).
Proof.
intros;unfold triple;fsetdec.
Qed.

Lemma triple_5 : forall a b c, Equal (triple a b c) (triple c b a).
Proof.
intros;unfold triple;fsetdec.
Qed.

Lemma triple_couple_1 : forall a b, Equal (triple a b b) (couple a b).
Proof.
intros;unfold couple, triple;fsetdec.
Qed.

Lemma triple_couple_2 : forall a b, Equal (triple a b b) (couple b a).
Proof.
intros;unfold couple, triple;fsetdec.
Qed.

Lemma triple_couple_3 : forall a b, Equal (triple b a b) (couple a b).
Proof.
intros;unfold couple, triple;fsetdec.
Qed.

Lemma triple_couple_4 : forall a b, Equal (triple b a b) (couple b a).
Proof.
intros;unfold couple, triple;fsetdec.
Qed.

Lemma triple_couple_5 : forall a b, Equal (triple b b a) (couple a b).
Proof.
intros;unfold couple, triple;fsetdec.
Qed.

Lemma triple_couple_6 : forall a b, Equal (triple b b a) (couple b a).
Proof.
intros;unfold couple, triple;fsetdec.
Qed.

Lemma inter_test : forall a b, Equal (inter (singleton a) (couple a b)) (singleton a).
Proof.
intros;unfold couple. fsetdec.
Qed.

Lemma inter_fsetdecide_1 : forall A B C D, ~ A [==] B -> 
Equal (inter (triple A C D) (triple B C D)) (couple C D).
Proof.
intros;unfold couple, triple;fsetdec.
Qed.

Lemma inter_fsetdecide_2 : forall A B C alpha beta, ~ alpha [==] beta -> 
Equal (inter (union (triple A B C) (singleton alpha))
  (union (triple A B C) (singleton beta))) (triple A B C).
Proof.
intros;unfold triple;fsetdec.
Qed.

Lemma inter_fsetdecide_3 : forall A B C alpha beta gamma,
 ~ alpha [==] gamma -> 
 ~ beta [==] gamma ->
Equal (inter (union (triple A B C) (couple alpha beta))
  (union (triple A B C) (singleton gamma))) (triple A B C).
Proof.
intros;unfold couple, triple; fsetdec.
Qed.

Lemma inter_fsetdecide_4 : forall ps, forall alpha beta : Point,
 ~ alpha [==] beta ->
Equal (inter (union ps (singleton alpha)) (union ps (singleton beta))) ps.
Proof.
intros;fsetdec.
Qed.

Lemma inter_fsetdecide_5 : forall ps, forall alpha beta gamma : Point,
 ~ alpha [==] gamma ->
 ~ beta [==] gamma ->
Equal (inter (union ps (couple alpha beta)) (union ps (singleton gamma))) ps.
Proof.
intros;unfold couple;fsetdec.
Qed.

Lemma union_fsetdecide : forall A0 B0 A1 B1 A C, 
Equal (union (union (quadruple A0 B0 A1 B1) (triple A0 B0 A))
           (triple A1 B1 C)) (union (quadruple A0 B0 A1 B1) (couple A C)).
intuition.
intuition.
Proof.
intros; split; intros.
unfold couple, triple, quadruple in *; fsetdec.
unfold couple, triple, quadruple in *; fsetdec.
Qed.


End s_SetOfPointsDef.

(*****************************************************************************)

Hint Immediate 
   triple_1 triple_2 triple_3 triple_4 triple_5
   triple_couple_1 triple_couple_2 triple_couple_3
   triple_couple_4 triple_couple_5  triple_couple_6
   couple_1
 : hset.

Hint Resolve inter_fsetdecide_1 inter_fsetdecide_2 
                      inter_fsetdecide_3 inter_fsetdecide_4 
                      inter_fsetdecide_5 : hset.

Ltac fsetdecide := (solve [auto with hset]) || (unfold couple, triple, quadruple in *; fsetdec).