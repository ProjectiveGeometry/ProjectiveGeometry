Require Export ProjectiveGeometry.Dev.rank_space_or_higher_properties.

(*****************************************************************************)
(** Proof of projective space geometry to matroid' **)


Section s_rkEquivToPsoh.

Context `{RPSOH : RankProjectiveSpaceOrHigher}.
Context `{EP : EqDecidability Point}.

(*** Definition LineInd ***)
Inductive LineInd : Type :=
| Cline : forall (A B : Point) (H: ~ A [==] B), LineInd.

Definition Line := LineInd.

(*** Definition fstP ***)
Definition fstP : Line -> Point.
intros.
elim H0.
intros.
exact A.
Defined.

(*** Definition sndP ***)
Definition sndP : Line -> Point.
intros.
elim H0.
intros.
exact B.
Defined.

(*** Definition Incid ***)
Definition Incid (A : Point)(l : Line) := rk (triple (fstP l) (sndP l) A) = 2.

Lemma incid_dec :  forall (A : Point)(l : Line), {Incid A l} + {~Incid A l}.
Proof.
intros.
unfold Incid.
exact (eq_nat_dec (rk (triple (fstP l) (sndP l) A)) 2).
Qed.

Lemma second_point : forall A : Point, exists B, ~ A [==] B.
Proof.
intro.
assert (T:= rk_lower_dim).
case_eq(eq_dec P0 A);intros.
case_eq(eq_dec P1 P0);intros.
rewrite e0 in *.
case_eq(eq_dec P2 P0);intros.
rewrite e1 in *.
case_eq(eq_dec P3 P0);intros.
rewrite e2 in *.
setoid_replace (quadruple P0 P0 P0 P0) with (singleton P0) in T by (clear_all;fsetdecide).
rewrite rk_singleton in T.
cut False.
intuition.
omega.
exists P3;rewrite <-e;intuition.
exists P2;rewrite <-e;intuition.
exists P1;rewrite <-e;intuition.
exists P0;intuition.
Qed.

Definition line_eq l m := rk (quadruple (fstP l) (sndP l) (fstP m) (sndP m)) = 2.

Lemma line_eq_refl : forall l, line_eq l l.
Proof.
intro.
induction l.
unfold line_eq, Incid.
simpl.
setoid_replace (quadruple A B A B) with (couple A B) by (clear_all;fsetdecide).
apply rk_couple1.
auto.
Qed.

Lemma line_eq_sym : forall l m, line_eq l m -> line_eq m l.
Proof.
intros.
induction l.
induction m.
unfold line_eq, Incid in *.
simpl in *.
setoid_replace (quadruple A0 B0 A B) with (quadruple A B A0 B0).
auto.
clear_all;fsetdecide.
Qed.

Lemma line_eq_trans : forall l m n, line_eq l m -> line_eq m n -> line_eq l n.
Proof.
intros.
induction l.
induction m.
induction n.
unfold line_eq, Incid in *.
simpl in *.
assert (rk (union (quadruple A B A0 B0) (quadruple A0 B0 A1 B1)) +
           rk (couple A0 B0) <=
           rk (quadruple A B A0 B0) + rk (quadruple A0 B0 A1 B1)).
apply matroid3_useful.
clear_all;fsetdecide.
assert (rk (couple A0 B0) = 2).
apply rk_couple1;auto.
assert (rk (union (quadruple A B A0 B0) (quadruple A0 B0 A1 B1)) <= 2).
omega.
apply le_antisym.
cut (rk (quadruple A B A1 B1) <= rk (union (quadruple A B A0 B0) (quadruple A0 B0 A1 B1)) ).
omega.
apply matroid2;clear H0 H1 H5 H6 H7; fsetdecide.
assert (rk (couple A1 B1) = 2).
apply rk_couple1;auto.
rewrite <- H8.
apply matroid2.
clear_all;fsetdecide.
Qed.

Lemma a1_exists : forall (A B :Point) , exists l, Incid A l /\ Incid B l.
Proof.
intros.
case_eq(eq_dec A B);intros.
elim (second_point B).
intros C H1.
exists (Cline B C H1).
unfold Incid.
simpl.
rewrite e.
setoid_replace (triple B C B) with (couple C B) by (clear_all;fsetdecide).
split.
apply rk_couple1.
solve[intuition].
apply rk_couple1.
solve[intuition].
exists (Cline A B n).
unfold Incid.
simpl.
setoid_replace (triple A B A) with (couple A B) by (clear_all;fsetdecide).
setoid_replace (triple A B B) with (couple A B) by (clear_all;fsetdecide).
split.
apply rk_couple1.
solve[intuition].
apply rk_couple1.
solve[intuition].
Qed.

Lemma uniqueness : forall (A B : Point)(l1 l2 : Line),
   Incid A l1 -> Incid B l1  -> Incid A l2 -> Incid B l2 -> A [==] B \/ line_eq l1 l2.
Proof.
intros A B l1 l2.
case_eq(eq_dec A B);intros.
solve[intuition].
induction l1.
induction l2.
intros.
right.
unfold Incid, line_eq in *.
simpl in *.
assert (rk (couple A0 B0) = 2).
apply rk_couple1;assumption.
assert (rk (couple A1 B1) = 2).
apply rk_couple1;assumption.
assert (rk (couple A B) = 2).
apply rk_couple1;assumption.

assert (rk (quadruple A0 B0 A B) = 2).
apply le_antisym.
assert (rk (union (triple A0 B0 A) (triple A0 B0 B)) + rk (couple A0 B0) <=
           rk (triple A0 B0 A) + rk (triple A0 B0 B)).
apply (matroid3_useful (triple A0 B0 A) (triple A0 B0 B) (couple A0 B0)).
clear_all;fsetdecide.
setoid_replace (union (triple A0 B0 A) (triple A0 B0 B)) with (quadruple A0 B0 A B) in H10.
omega.
clear_all;fsetdecide.
rewrite <- H1.
apply matroid2.
clear_all;fsetdecide.

assert (rk (quadruple A1 B1 A B) = 2).
apply le_antisym.
assert (rk (union (triple A1 B1 A) (triple A1 B1 B)) + rk (couple A1 B1) <=
           rk (triple A1 B1 A) + rk (triple A1 B1 B)).
apply (matroid3_useful (triple A1 B1 A) (triple A1 B1 B) (couple A1 B1)).
clear_all;fsetdecide.
setoid_replace (union (triple A1 B1 A) (triple A1 B1 B)) with (quadruple A1 B1 A B) in H11.
omega.
clear_all;fsetdecide.
rewrite <- H3.
apply matroid2.
clear_all;fsetdecide.
 
assert (rk (union (quadruple A0 B0 A B) (quadruple A1 B1 A B)) +
           rk (couple A B) <=
           rk (quadruple A0 B0 A B) + rk (quadruple A1 B1 A B)).
apply (matroid3_useful (quadruple A0 B0 A B) (quadruple A1 B1 A B) (couple A B)).
clear_all;fsetdecide.
assert (rk (union (quadruple A0 B0 A B) (quadruple A1 B1 A B)) <= 2).
omega.
apply le_antisym.
assert (rk (quadruple A0 B0 A1 B1) <= rk (union (quadruple A0 B0 A B) (quadruple A1 B1 A B))).
apply matroid2.
clear_all;fsetdecide.
omega.
rewrite <- H7.
apply matroid2.
clear_all;fsetdecide.
Qed.

(* A2 Pasch *)

Lemma a2 : forall A B C D : Point, forall lAB lCD lAC lBD : Line, 
~ A [==] B /\ ~ A [==] C /\ ~ A [==] D /\ 
~ B [==] C /\ ~ B [==] D /\ ~ C [==] D -> 
Incid A lAB /\ Incid B lAB ->  
Incid C lCD /\ Incid D lCD -> 
Incid A lAC /\ Incid C lAC -> 
Incid B lBD /\ Incid D lBD ->
(exists I : Point, (Incid I lAB /\ Incid I lCD)) -> exists J : Point, (Incid J lAC /\ Incid J lBD).
Proof.
intros.
induction lAB.
induction lCD.
induction lAC.
induction lBD.
unfold Incid in *.
simpl in *.
decompose [and] H1; clear H1.
decompose [and] H2; clear H2.
decompose [and] H3; clear H3.
decompose [and] H4; clear H4.
elim H5;clear H5.
intro P.
intros.
decompose [and] H4;clear H4.
assert (HC:rk (quadruple A B C D) >= 3 \/ rk (quadruple A B C D) < 3).
omega.
elim HC;intro HABCD;clear HC.

apply (rk_pasch A2 B2 A3 B3).

assert(rk (union (singleton P) (quadruple A0 B0 A1 B1)) <= 3).
apply (intersecting_lines_rank_3 A0 B0 A1 B1 P);omega.
assert (rk (quadruple A0 B0 A1 B1) <= 3).
cut (rk (quadruple A0 B0 A1 B1) <=  rk (union (singleton P) (quadruple A0 B0 A1 B1))).
omega.
apply matroid2; (clear_all; fsetdecide).

assert (rk (couple A0 B0) = 2).
apply rk_couple1;auto.
assert (rk (couple A1 B1) = 2).
apply rk_couple1;auto.
assert (rk (couple A2 B2) = 2).
apply rk_couple1;auto.
assert (rk (couple A3 B3) = 2).
apply rk_couple1;auto.

assert (rk (union (quadruple A0 B0 A1 B1) (triple A0 B0 A)) + rk (couple A0 B0) <=
           rk (quadruple A0 B0 A1 B1) + rk (triple A0 B0 A)).
apply (matroid3_useful (quadruple A0 B0 A1 B1) (triple A0 B0 A) (couple A0 B0)).
(clear_all; fsetdecide).

assert (rk (union (quadruple A0 B0 A1 B1) (triple A0 B0 A))  <= 3).
omega.
assert (rk
         (union (union (quadruple A0 B0 A1 B1) (triple A0 B0 A))
            (triple A1 B1 C)) + rk (couple A1 B1) <=
       rk (union (quadruple A0 B0 A1 B1) (triple A0 B0 A)) +
       rk (triple A1 B1 C)).
apply (matroid3_useful (union (quadruple A0 B0 A1 B1) (triple A0 B0 A))
 (triple A1 B1 C) (couple A1 B1)).
(clear_all; fsetdecide).
assert (rk
        (union (union (quadruple A0 B0 A1 B1) (triple A0 B0 A))
           (triple A1 B1 C)) <= 3).
omega.
setoid_replace (union (union (quadruple A0 B0 A1 B1) (triple A0 B0 A))
           (triple A1 B1 C)) with (union (quadruple A0 B0 A1 B1) (couple A C)) in H24 by (clear_all; fsetdecide).
assert (rk
         (union (union (quadruple A0 B0 A1 B1) (couple A C)) (triple A0 B0 B)) +
       rk (couple A0 B0) <=
       rk (union (quadruple A0 B0 A1 B1) (couple A C)) +
       rk (triple A0 B0 B)).
apply (matroid3_useful (union (quadruple A0 B0 A1 B1) (couple A C))
(triple A0 B0 B) (couple A0 B0)).
(clear_all; fsetdecide).
assert ( rk
        (union (union (quadruple A0 B0 A1 B1) (couple A C)) (triple A0 B0 B)) <= 3).
omega.
assert (rk
         (union
            (union (union (quadruple A0 B0 A1 B1) (couple A C))
               (triple A0 B0 B)) (triple A1 B1 D)) + rk (couple A1 B1) <=
       rk
         (union (union (quadruple A0 B0 A1 B1) (couple A C)) (triple A0 B0 B)) +
       rk (triple A1 B1 D)).
apply (matroid3_useful  (union (union (quadruple A0 B0 A1 B1) (couple A C)) (triple A0 B0 B)) 
(triple A1 B1 D) (couple A1 B1)).
(clear_all; fsetdecide).
assert ( rk
        (union
           (union (union (quadruple A0 B0 A1 B1) (couple A C))
              (triple A0 B0 B)) (triple A1 B1 D)) <= 3).
omega.
assert (rk (quadruple A B C D) <= 3).
cut (rk (quadruple A B C D) <= rk
        (union
           (union (union (quadruple A0 B0 A1 B1) (couple A C))
              (triple A0 B0 B)) (triple A1 B1 D)) ).
omega.
apply matroid2. 
(clear_all; fsetdecide).
assert (rk (quadruple A B C D) = 3).
omega.

assert (rk (quadruple A2 B2 A C) = 2).
apply rk_lemma_1;auto.
assert (rk (quadruple A3 B3 B D) = 2).
apply rk_lemma_1;auto.

decompose [and] H0.
assert (rk (couple A C) =2).
apply rk_couple1;auto.
assert (rk (couple A D) =2).
apply rk_couple1;auto.
assert (rk (couple B C) =2).
apply rk_couple1;auto.
assert (rk (couple B D) =2).
apply rk_couple1;auto.

assert (rk (union (quadruple A2 B2 A C) (quadruple A B C D)) +
            rk (couple A C) <=
           rk (quadruple A2 B2 A C) + rk (quadruple A B C D)).
apply (matroid3_useful (quadruple A2 B2 A C) (quadruple A B C D) (couple A C)).
(clear_all; fsetdecide).
assert (rk (union (quadruple A2 B2 A C) (quadruple A B C D)) <= 3).
omega.
assert (rk (union (quadruple A3 B3 B D) (quadruple A B C D)) +
            rk (couple B D) <=
           rk (quadruple A3 B3 B D) + rk (quadruple A B C D)).
apply (matroid3_useful (quadruple A3 B3 B D) (quadruple A B C D) (couple B D)).
(clear_all; fsetdecide).
assert ( rk (union (quadruple A3 B3 B D) (quadruple A B C D))  <= 3).
omega.
assert (rk
         (union (union (quadruple A2 B2 A C) (quadruple A B C D))
            (union (quadruple A3 B3 B D) (quadruple A B C D))) +
       rk (quadruple A B C D) <=
       rk (union (quadruple A2 B2 A C) (quadruple A B C D)) +
       rk (union (quadruple A3 B3 B D) (quadruple A B C D))).
apply (matroid3_useful (union (quadruple A2 B2 A C) (quadruple A B C D))).
(clear_all; fsetdecide).
assert (rk
        (union (union (quadruple A2 B2 A C) (quadruple A B C D))
           (union (quadruple A3 B3 B D) (quadruple A B C D))) <= 3).
omega.
cut (rk (quadruple A2 B2 A3 B3) <=  rk
        (union (union (quadruple A2 B2 A C) (quadruple A B C D))
           (union (quadruple A3 B3 B D) (quadruple A B C D)))).
omega.
apply matroid2.
(clear_all; fsetdecide).

exists A2.
split.
setoid_replace (triple A2  B2 A2) with (couple A2 B2) by (clear_all; fsetdecide).
apply rk_couple1;auto.
assert (rk (quadruple A B C D) = 2).
apply le_antisym.
omega.
decompose [and] H0.
assert (rk (couple A B) =2).
apply rk_couple1;intuition.
rewrite <- H20.
apply matroid2.
(clear_all; fsetdecide).

assert (rk (couple A0 B0) = 2).
apply rk_couple1;auto.
assert (rk (couple A1 B1) = 2).
apply rk_couple1;auto.
assert (rk (couple A2 B2) = 2).
apply rk_couple1;auto.
assert (rk (couple A3 B3) = 2).
apply rk_couple1;auto.

assert (rk (quadruple A2 B2 A C) = 2).
apply rk_lemma_1;auto.
assert (rk (quadruple A3 B3 B D) = 2).
apply rk_lemma_1;auto.

decompose [and] H0.
assert (rk (couple A C) =2).
apply rk_couple1;auto.
assert (rk (couple A D) =2).
apply rk_couple1;auto.
assert (rk (couple B C) =2).
apply rk_couple1;auto.
assert (rk (couple B D) =2).
apply rk_couple1;auto.

assert (rk (union (quadruple A3 B3 B D) (quadruple A B C D)) +
       rk (couple B D) <=
       rk (quadruple A3 B3 B D) + rk (quadruple A B C D)).
apply (matroid3_useful (quadruple A3 B3 B D) (quadruple A B C D) (couple B D)).
(clear_all; fsetdecide).
assert ( rk (union (quadruple A3 B3 B D) (quadruple A B C D)) <= 2).
omega.

assert (rk
         (union (union (quadruple A3 B3 B D) (quadruple A B C D))
            (quadruple A2 B2 A C)) + rk (couple A C) <=
       rk (union (quadruple A3 B3 B D) (quadruple A B C D)) +
       rk (quadruple A2 B2 A C)).
apply matroid3_useful.
(clear_all; fsetdecide).
assert ( rk
        (union (union (quadruple A3 B3 B D) (quadruple A B C D))
           (quadruple A2 B2 A C)) <= 2).
omega.
apply le_antisym.
cut (rk (triple A3 B3 A2)  <=  rk
        (union (union (quadruple A3 B3 B D) (quadruple A B C D))
           (quadruple A2 B2 A C))).
omega.
apply matroid2.
(clear_all; fsetdecide).
rewrite <- H19.
apply matroid2.
(clear_all; fsetdecide).
Qed.

(* A3 : dimension-related axioms *)

Lemma a3_1 : 
forall l : Line, exists A : Point, exists B : Point, exists C : Point, 
~ A [==] B /\ ~ A [==] C /\ ~ B [==] C /\ Incid A l /\ Incid B l /\ Incid C l.
Proof.
intros.
induction l.
exists A.
exists B.
elim (rk_three_points A B).
intro C.
intros.
exists C.
unfold Incid.
simpl.
setoid_replace (triple A B A) with (couple A B).
setoid_replace (triple A B B) with (couple A B).
assert (rk (couple A B) = 2).
apply rk_couple1;auto.
intuition.
rewrite H3 in H5.
apply couple_rk1 in H5;intuition.
rewrite H3 in H4.
apply couple_rk1 in H4;intuition.
apply triple_couple_1.
assumption.
apply triple_couple_4.
assumption.
Qed.

Lemma a3_2 (* dim >= 3 *) : exists l1, exists l2, forall p, ~(Incid p l1 /\ Incid p l2).
Proof.
exists (Cline P0 P1 base_points_distinct_1).
exists (Cline P2 P3 base_points_distinct_2).
intros.
unfold Incid.
simpl.
unfold not;intro.
destruct H0.
assert (rk (union (triple P0 P1 p) (triple P2 P3 p)) + rk (singleton p) <=
           rk (triple P0 P1 p) + rk (triple P2 P3 p)).
apply matroid3_useful.
(clear_all; fsetdecide).
rewrite rk_singleton in H2.
assert (rk (union (triple P0 P1 p) (triple P2 P3 p)) <= 3).
omega.
clear H0.
assert (rk (quadruple P0 P1 P2 P3) <= 3).
cut (rk (quadruple P0 P1 P2 P3) <= rk (union (triple P0 P1 p) (triple P2 P3 p)) ).
omega.
apply matroid2.
(clear_all; fsetdecide).
assert (T:= rk_lower_dim).
omega.
Qed.

End s_rkEquivToPsoh.