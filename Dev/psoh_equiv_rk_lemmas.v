Require Export ProjectiveGeometry.Dev.psoh_equiv_c4p.

(*****************************************************************************)
(** Rkl **)


Section s_psohEquivCRk_1.

Context `{PPS : PreProjectiveSpace}.
Context `{EP : EqDecidability Point}.
Context `{OP : OrderedType Point}.
Context `{EL : EqDecidabilityL Line}.
Context `{ELI : EqDecidabilityP Line Intersect}.

(*** Definition rkl ***)
Definition rkl  l := match l with
| nil => 0
| x :: nil => 1
| l => if contains_four_non_coplanar_points l then 4 else 
          if contains_three_non_collinear_points l then 3 else
             if contains_two_distinct_points l then  2 else 1
end.

Functional Scheme rkl_ind := Induction for rkl Sort Prop.

Global Instance rank_morph : Proper (@equivlistA Point eq ==> (@Logic.eq nat)) rkl.
Proof.
repeat red.
intros x; elim x using rkl_ind.
(* 1 *)
intros l Hl.
intros y; elim y using rkl_ind.
solve [trivial].
intros.
assert (T:InA eq _x (_x::nil)).
solve [intuition].
destruct (H _x).
generalize (H1 T); intros Hinv; inversion Hinv.
intros; subst.
assert (T:InA eq _x (_x :: _x0 :: _x1)).
solve [intuition].
destruct (H _x).
generalize (H1 T); intros Hinv; inversion Hinv.
intros; subst.
assert (T:InA eq _x (_x :: _x0 :: _x1)).
solve [intuition].
destruct (H _x).
generalize (H1 T); intros Hinv; inversion Hinv.
intros; subst.
assert (T:InA eq _x (_x :: _x0 :: _x1)).
solve [intuition].
destruct (H _x).
generalize (H1 T); intros Hinv; inversion Hinv.
intros; subst.
assert (T:InA eq _x (_x :: _x0 :: _x1)).
solve [intuition].
destruct (H _x).
generalize (H1 T); intros Hinv; inversion Hinv.
(* 2 *)
intros l _x m Hl Hm; subst.
intros y; elim y using rkl_ind.
intros; subst.
assert (T:InA eq _x (_x :: nil)).
solve [intuition].
destruct (H _x).
generalize (H0 T); intros Hinv; inversion Hinv.
solve [trivial].
intros; subst.
rewrite <- H in e1.
inversion e1.
intros; subst.
rewrite <- H in e2.
inversion e2.
intros; subst.
rewrite <-H in e3.
inversion e3.
solve[trivial].
(* 3 *)
intros l _x m Hl _y n Hn Hl2.
intros y; elim y using rkl_ind. 
intros; subst.
assert (T:InA eq _x (_x :: _y :: n)).
solve [intuition].
destruct (H _x).
generalize (H0 T); intros Hinv; inversion Hinv.
intros; subst.
rewrite H in Hl2.
simpl in *.
inversion Hl2.
intros; subst.
solve [trivial].
intros; subst.
rewrite H in Hl2.
rewrite e1 in Hl2. 
inversion Hl2.
intros; subst.
rewrite H in Hl2.
rewrite e1 in Hl2.
inversion Hl2.
intros; subst.
rewrite H in Hl2.
rewrite e1 in Hl2.
inversion Hl2.
(* 4 *)
intros l _x m Hm _y n Hl Hl2 Hl3.
intros y; elim y using rkl_ind.
intros; subst.
assert (T: InA eq _x  (_x :: _y :: n)).
solve [intuition].
destruct (H _x) as [Hx1 Hx2].
generalize (Hx1 T); intros Hinv; inversion Hinv. 
intros; subst.
rewrite H in Hl3.
inversion Hl3.
intros; subst.
rewrite H in Hl2.
rewrite e1 in Hl2.
inversion Hl2.
intros; subst.
solve [trivial].
intros; subst.
rewrite H in Hl3.
rewrite e2 in Hl3.
inversion Hl3.
intros; subst.
rewrite H in Hl3.
rewrite e2 in Hl3.
inversion Hl3.
(* 5 *)
intros l _x m Hm _y n Hl Hl1 Hl2 Hl3.
intros y; elim y using rkl_ind.
intros; subst.
assert (T: InA eq _x (_x :: _y :: n)).
solve [intuition].
destruct (H _x) as [Hx1 Hx2].
generalize (Hx1 T); intros Hinv; inversion Hinv.
intros;subst.
rewrite H in Hl3.
inversion Hl3.
intros; subst.
rewrite H in Hl1.
rewrite e1 in Hl1.
inversion Hl1.
intros; subst.
rewrite H in Hl2.
rewrite e2 in Hl2.
inversion Hl2.
intros; subst.
solve [trivial].
intros; subst.
rewrite H in Hl3.
rewrite e3 in Hl3.
inversion Hl3.
(* 6 *)
intros l _x m Hm _y n Hl Hl1 Hl2 Hl3.
intros y; elim y using rkl_ind.
intros; subst.
assert (T: InA eq _x (_x :: _y :: n)).
solve [intuition].
destruct (H _x) as [Hx1 Hx2].
generalize (Hx1 T); intros Hinv; inversion Hinv.
intros; subst.
solve [trivial].
intros;subst.
rewrite H in Hl1.
rewrite e1 in Hl1.
inversion Hl1.
intros;subst.
rewrite H in Hl2.
rewrite e2 in Hl2.
inversion Hl2.
intros;subst.
rewrite H in Hl3.
rewrite e3 in Hl3.
inversion Hl3.
intros; subst.
solve [trivial].
Qed.

End s_psohEquivCRk_1.


Ltac my_rank :=
  repeat match goal with
  |[H : _ |- _] => progress intros
  |[H : _ |- _] => progress intro
  |[H : _ |- _ <-> _] => split
  |[H : _ |- _ /\ _] => split
  |[H : _ |- _ /\ _] => split
  |[H : _ /\ _ |- _] => destruct H
  |[H : _ |- _] => solve[intuition]
  |[H : _ |- _] => progress contradiction
  |[H : ?X :: _ = nil |- _] => inversion H
  |[H : false = true |- _] => inversion H
  |[H : true = false |- _] => inversion H
  |[H : ?X[==]?X -> False |- _] => apply False_ind;apply H;reflexivity

  |[H : _ |- (if if ?X then _ else _
                then _ else _) = _ \/ _] => case_eq X
  |[H : _ |- (if ?X then _ else _) = _ \/ _] => case_eq X
  |[H : _ |- (if if ?X then _ else _
                then _ else _) = _] => case_eq X
  |[H : _ |-  (if ?X then _ else _) = _] => case_eq X
  |[H : _ |- _ = (if if ?X then _ else _
                then _ else _)] => case_eq X
  |[H : _ |- _ = (if ?X then _ else _)] => case_eq X
  |[H : _ |- (if if ?X then _ else _
                then _ else _) >= _] => case_eq X
  |[H : _ |- (if ?X then _ else _) >= _ ] => case_eq X              
  |[H : _ |- (if if ?X then _ else _
                then _ else _) <= _] => case_eq X
  |[H : _ |- (if ?X then _ else _) <= _ ] => case_eq X
  |[H : _ |- _ >= (if if ?X then _ else _
                then _ else _)] => case_eq X
  |[H : _ |- _ >= (if ?X then _ else _)] => case_eq X              
  |[H : _ |- _ <= (if if ?X then _ else _
                then _ else _)] => case_eq X
  |[H : _ |- _ <=(if ?X then _ else _)] => case_eq X    

  |[H : _ |- _ + (if if ?X then _ else _
                then _ else _) >= _] => case_eq X
  |[H : _ |- _ + (if ?X then _ else _) >= _ ] => case_eq X              
  |[H : _ |- _ + (if if ?X then _ else _
                then _ else _) <= _] => case_eq X
  |[H : _ |- _ + (if ?X then _ else _) <= _ ] => case_eq X
  |[H : _ |- (if if ?X then _ else _
                then _ else _) + _ >= _] => case_eq X
  |[H : _ |- (if ?X then _ else _) + _ >= _ ] => case_eq X              
  |[H : _ |- (if if ?X then _ else _
                then _ else _) + _ <= _] => case_eq X
  |[H : _ |- (if ?X then _ else _) + _ <= _ ] => case_eq X

  |[H : _ |- _ >= (if if ?X then _ else _
                then _ else _) + _] => case_eq X
  |[H : _ |- _ >= (if ?X then _ else _) + _] => case_eq X              
  |[H : _ |- _ <= (if if ?X then _ else _
                then _ else _) + _] => case_eq X
  |[H : _ |- _ <=(if ?X then _ else _) + _] => case_eq X  
  end.


Section s_psohEquivCRk_2.

Context `{PPS : PreProjectiveSpace}.
Context `{EP : EqDecidability Point}.
Context `{OP : OrderedType Point}.
Context `{EL : EqDecidabilityL Line}.
Context `{ELI : EqDecidabilityP Line Intersect}.

Lemma all_rank : forall l, rkl l = 0 \/ rkl l = 1 \/ rkl l = 2 \/ rkl l = 3 \/ rkl l = 4.
Proof.
my_rank;unfold rkl;case_eq l;my_rank.
Qed.

Lemma matroid1': rkl nil = 0.
Proof.
my_rank.
Qed.

Lemma rk_singleton_ge : forall p:Point, rkl (p::nil) >=1.
Proof.
my_rank.
Qed.

Lemma rk_singleton_le : forall p:Point, rkl (p::nil) <=1.
Proof.
my_rank.
Qed.

Lemma rk_singleton : forall p:Point, rkl (p::nil) = 1.
Proof.
my_rank.
Qed.

Lemma rk_couple_ge : forall p q:Point,~(p[==]q)-> rkl(p::q::nil)>=2.
Proof.
my_rank;
case (eq_dec_u p q);
my_rank;simpl;my_rank.
Qed.

Lemma rank_max_4 : forall e, rkl(e) <= 4.
Proof.
my_rank;case_eq e;my_rank;case_eq l;simpl;my_rank.
Qed.

Lemma rank_min_not_nil : forall e, e <> nil -> rkl(e) >= 1.
Proof.
my_rank;case_eq e;my_rank;case_eq l;simpl;my_rank.
Qed.

Lemma rk_nil : forall l, rkl l = 0 -> l = nil.
Proof.
my_rank;case_eq l;my_rank.
assert(HH : l <> nil);my_rank.
rewrite H1 in H0;inversion H0.
assert(HH0 := rank_min_not_nil l HH);
my_rank;
rewrite H in HH0;inversion HH0.
Qed.

Lemma rk_decr :
forall l, forall a, rkl (a :: a :: l) = rkl (a :: l).
Proof.
my_rank.
apply rank_morph.
my_inA.
Qed.

Lemma rk_decr_reverse :
forall l, forall a, rkl (a :: l) = rkl (a :: a :: l).
Proof.
my_rank.
apply rank_morph.
my_inA.
Qed.

Lemma matroid3_aux1_col_bis :
forall l,forall a,
collinear_with_all a (all_pairs l) = false ->
contains_three_non_collinear_points (a :: l) = true.
Proof.
my_rank;induction l;simpl;my_rank.
inversion H;rewrite H0 in H3;my_rank.
Qed.

Lemma matroid3_aux1_cop_bis :
forall l,forall a,
coplanar_with_all a (all_triples l) = false ->
contains_four_non_coplanar_points (a :: l) = true.
Proof.
my_rank;induction l;simpl;my_rank.
inversion H;rewrite H0 in H3;my_rank.
Qed.

Lemma matroid3_aux1_col_bis_bis : forall l, forall a,
collinear_with_all a (all_pairs (l)) = true ->
contains_three_non_collinear_points (a :: l) = false.
Proof.
my_rank;induction l;simpl;my_rank.
assert(HH := matroid3_aux1 l a0 H1);my_rank.
assert(HH := matroid3_aux0_bis l a a0 H);rewrite H1 in HH;my_rank.
inversion H;rewrite H2 in H0;my_rank.
Qed.

Lemma matroid3_aux1_cop_bis_bis : forall l, forall a,
coplanar_with_all a (all_triples (l)) = true ->
contains_four_non_coplanar_points (a :: l) = false.
Proof.
my_rank;induction l;simpl;my_rank.
assert(HH := matroid3_aux1_cop l a0 H1);my_rank.
assert(HH := matroid3_aux0_cop_bis l a a0 H);rewrite H1 in HH;my_rank.
inversion H;rewrite H2 in H0;my_rank.
Qed.

Lemma matroid3_aux2_col : 
forall l,
contains_two_distinct_points l = true ->
contains_three_non_collinear_points l = false ->
rkl l = 2.
Proof.
my_rank;induction l;simpl;my_rank.
inversion H.
rewrite H1 in H;inversion H.
assert (HH := matroid3_aux1_cop (p::l0) a H2);rewrite H3 in HH;my_rank.
assert (HH := matroid3_aux1 (p::l0) a H4);rewrite H5 in HH;my_rank.
assert(inclA eq (p::l) (p::l0));my_inA;assert (HH := contains_two_distinct_points_sublist (p :: p :: l0) (p::l0) H8 H);rewrite H7 in HH;my_rank.
subst; assert (HH := matroid3_aux1_col_bis (p :: l0) a H4);rewrite HH in H0;my_rank.
subst; assert (HH := matroid3_aux1_cop_bis (p :: l0) a H2);assert(HH0 := contains_four_to_three_aux' (a :: p :: l0) HH);rewrite HH0 in H0;my_rank.
Qed.

Lemma matroid3_aux2_cop : 
forall l,
contains_three_non_collinear_points l = true ->
contains_four_non_coplanar_points l = false ->
rkl l = 3.
Proof.
my_rank;induction l;simpl;my_rank.
inversion H.
rewrite H1 in H;inversion H.
assert (HH := matroid3_aux1_cop (p::l0) a H2);rewrite H3 in HH;my_rank.
assert (HH := matroid3_aux1_col_bis_bis (p::l0) a H4);rewrite <-H1 in HH;rewrite H in HH;my_rank.
assert (HH := matroid3_aux1_col_bis_bis (p::l0) a H4);rewrite <-H1 in HH;rewrite H in HH;my_rank.
assert (HH := matroid3_aux1_col_bis_bis (p::l0) a H4);rewrite <-H1 in HH;rewrite H in HH;my_rank.
assert (HH := matroid3_aux1_cop_bis (p::l0) a H2);rewrite <-H1 in HH;rewrite H0 in HH;my_rank.
Qed.

Lemma matroid3_aux2_col_bis :
forall l,
contains_three_non_collinear_points l = true ->
contains_two_distinct_points l = true.
Proof.
my_rank;induction l;simpl;my_rank;case_eq l;my_rank.
subst;inversion H.
subst;apply IHl;my_subst;rewrite <-H;apply contains_three_morph;my_inA.
Qed.

Lemma matroid3_aux2_cop_bis :
forall l,
contains_four_non_coplanar_points l = true ->
contains_three_non_collinear_points l = true.
Proof.
apply contains_four_to_three_aux'.
Qed.

Lemma matroid3_aux2_col_bis_bis :
forall l,
contains_two_distinct_points l = false ->
contains_three_non_collinear_points l = false.
Proof.
my_rank;induction l;my_rank;simpl;my_rank.
assert( HH := matroid3_aux1 l a H0);my_rank.
assert( HH := matroid3_aux1_col_bis l a H0);assert ( HH0 := matroid3_aux2_col_bis (a::l) HH);rewrite HH0 in H;my_rank.
Qed.

Lemma matroid3_aux2_cop_bis_bis :
forall l,
contains_three_non_collinear_points l = false ->
contains_four_non_coplanar_points l = false.
Proof.
my_rank;induction l;my_rank;simpl;my_rank.
assert( HH := matroid3_aux1_cop l a H0);my_rank.
assert( HH := matroid3_aux1_cop_bis l a H0);assert ( HH0 := matroid3_aux2_cop_bis (a::l) HH);rewrite HH0 in H;my_rank.
Qed.

Lemma matroid3_aux3 : 
forall l,
contains_two_distinct_points l = false ->
rkl l = 0 \/ rkl l = 1.
Proof.
my_rank;case_eq l;my_rank.
unfold rkl;case_eq l0;my_rank.
subst;assert(HH := matroid3_aux2_col_bis_bis (p :: p0 :: l1) H);assert(HH0 := matroid3_aux2_cop_bis_bis (p :: p0 :: l1) HH);rewrite H2 in HH0;my_rank.
subst;assert(HH := matroid3_aux2_col_bis_bis (p :: p0 :: l1) H);rewrite H3 in HH;my_rank.
subst;rewrite H4 in H;my_rank.
Qed.

Lemma matroid3_aux3_bis :
forall l, l <> nil ->
rkl(l) = 1 \/ rkl(l) = 2 \/ rkl(l) = 3 \/ rkl(l) = 4.
Proof.
my_rank;case_eq l;my_rank.
unfold rkl;case_eq l0;my_rank.
Qed.

Lemma matroid3_aux3_bis_bis :
forall l,
contains_four_non_coplanar_points l = true ->
rkl l = 4.
Proof.
my_rank;case_eq l;my_rank.
rewrite H0 in H;simpl in H;my_rank.
unfold rkl;case_eq l0;my_rank;subst;my_rank.
inversion H.
rewrite H in H2;my_rank.
rewrite H in H2;my_rank.
rewrite H in H2;my_rank.
Qed.

Lemma matroid3_aux9 :
forall l,
rkl l = 3 ->
contains_three_non_collinear_points l = true.
Proof.
unfold rkl;intros l;case_eq l. my_rank.
intros p l0;case_eq l0;my_rank.
generalize H1;case_eq (contains_four_non_coplanar_points (p :: p0 :: l1));
case_eq (contains_three_non_collinear_points (p :: p0 :: l1));case_eq(contains_two_distinct_points (p :: p0 :: l1));my_rank.
Qed.

Lemma matroid3_aux9_alt :
forall l,
rkl l = 4 ->
contains_four_non_coplanar_points l = true.
Proof.
unfold rkl;intros l;case_eq l. my_rank.
intros p l0;case_eq l0;my_rank.
generalize H1;case_eq (contains_four_non_coplanar_points (p :: p0 :: l1));
case_eq (contains_three_non_collinear_points (p :: p0 :: l1));case_eq(contains_two_distinct_points (p :: p0 :: l1));my_rank;inversion H5.
Qed.

Lemma matroid3_aux9_bis :
forall l,forall a a0,
~a[==]a0 ->
contains_two_distinct_points (a :: a0 :: l) = true.
Proof.
my_rank;simpl;case_eq(eq_dec_u a a0);my_rank.
Qed.

Lemma matroid3_aux9_bis_bis :
forall l,
rkl l = 1 ->
contains_two_distinct_points l = false.
Proof.
unfold rkl;intros l;case_eq l. my_rank.
intros p l0;case_eq l0;my_rank.
generalize H1;case_eq (contains_four_non_coplanar_points (p :: p0 :: l1));
case_eq (contains_three_non_collinear_points (p :: p0 :: l1));case_eq(contains_two_distinct_points (p :: p0 :: l1));my_rank;inversion H5.
Qed.

Lemma matroid3_aux9_bis_bis_aux2 :
forall l,
rkl l = 1 ->
contains_three_non_collinear_points l = false.
Proof.
unfold rkl;intros l;case_eq l. my_rank.
intros p l0;case_eq l0;my_rank.
generalize H1;case_eq (contains_four_non_coplanar_points (p :: p0 :: l1));
case_eq (contains_three_non_collinear_points (p :: p0 :: l1));case_eq(contains_two_distinct_points (p :: p0 :: l1));my_rank;inversion H5.
Qed.

Lemma matroid3_aux9_bis_bis_aux3 :
forall l,
rkl l = 1 ->
contains_four_non_coplanar_points l = false.
Proof.
unfold rkl;intros l;case_eq l. my_rank.
intros p l0;case_eq l0;my_rank.
generalize H1;case_eq (contains_four_non_coplanar_points (p :: p0 :: l1));
case_eq (contains_three_non_collinear_points (p :: p0 :: l1));case_eq(contains_two_distinct_points (p :: p0 :: l1));my_rank;inversion H5.
Qed.

Lemma matroid3_aux9_bis_bis_reverse :
forall l,
rkl l = 2 ->
contains_two_distinct_points l = true.
Proof.
unfold rkl;intros l;case_eq l. my_rank.
intros p l0;case_eq l0;my_rank.
generalize H1;case_eq (contains_four_non_coplanar_points (p :: p0 :: l1));
case_eq (contains_three_non_collinear_points (p :: p0 :: l1));case_eq(contains_two_distinct_points (p :: p0 :: l1));my_rank.
Qed.

Lemma matroid3_aux9_bis_bis_aux :
forall l,
rkl l = 2 ->
contains_three_non_collinear_points l = false.
Proof.
unfold rkl;intros l;case_eq l. my_rank.
intros p l0;case_eq l0;my_rank.
generalize H1;case_eq (contains_four_non_coplanar_points (p :: p0 :: l1));
case_eq (contains_three_non_collinear_points (p :: p0 :: l1));case_eq(contains_two_distinct_points (p :: p0 :: l1));my_rank;inversion H5.
Qed.

Lemma matroid3_aux9_bis_bis_alt :
forall l,
rkl l = 2 ->
contains_four_non_coplanar_points l = false.
Proof.
unfold rkl;intros l;case_eq l. my_rank.
intros p l0;case_eq l0;my_rank.
generalize H1;case_eq (contains_four_non_coplanar_points (p :: p0 :: l1));
case_eq (contains_three_non_collinear_points (p :: p0 :: l1));case_eq(contains_two_distinct_points (p :: p0 :: l1));my_rank;inversion H5.
Qed.

Lemma matroid3_aux9_bis_bis_bis :
forall l,
rkl l = 3 ->
contains_four_non_coplanar_points l = false.
Proof.
unfold rkl;intros l;case_eq l. my_rank.
intros p l0;case_eq l0;my_rank.
generalize H1;case_eq (contains_four_non_coplanar_points (p :: p0 :: l1));
case_eq (contains_three_non_collinear_points (p :: p0 :: l1));case_eq(contains_two_distinct_points (p :: p0 :: l1));my_rank;inversion H5.
Qed.

Lemma matroid3_aux10 :
forall l, forall a,
rkl (a :: l) = 1 ->
rkl l = 1 ->
InA eq a l.
Proof.
my_rank;generalize H;unfold rkl;case_eq l;my_rank;subst;[inversion H0|].
generalize H2;case_eq(contains_four_non_coplanar_points (a :: p :: l0));
case_eq(contains_three_non_collinear_points (a :: p :: l0));case_eq(contains_two_distinct_points(a :: p :: l0));my_rank;inversion H5.
generalize H1;simpl;case_eq(eq_dec_u a p);my_rank.
Qed.

Lemma matroid3_aux10_aux4 :
forall l, forall a,
rkl (a :: l) = 1 ->
rkl l = 0 \/ rkl l = 1.
Proof.
my_rank;induction l;my_rank.
case_eq(eq_dec_u a a0);my_rank;my_subst;right;rewrite <-H;[apply rk_decr_reverse|].
assert(HH := matroid3_aux9_bis l a a0 n);assert(HH0 := matroid3_aux9_bis_bis (a :: a0 :: l) H);rewrite HH in HH0;my_rank.
Qed.

Lemma matroid3_aux10_aux5 :
forall l, forall a,
rkl (a :: l) = 3 ->
rkl l = 2 \/ rkl l = 3.
Proof.
my_rank;induction l;my_rank;simpl;case_eq l;my_rank;subst.
- simplgen H;case_eq(eq_dec_u a a0);my_rank.
- assert(HH := matroid3_aux1_cop (p :: l0) a0 H1);rewrite HH in H2;my_rank.
- my_subst;assert(HH := matroid3_aux3 (p :: l0) H6);my_rank;
  assert(HH0 : equivlistA eq (a :: p :: p :: l0) (a :: p :: l0));[my_inA|];rewrite HH0 in H;my_rank.
- assert(HH := matroid3_aux1_cop_bis (p :: l0) a0 H1);assert(HH0 := matroid3_aux9_bis_bis_bis (a :: a0 :: p :: l0) H);
  assert(HH1 : inclA eq (a0 :: p :: l0) (a :: a0 :: p :: l0));[my_inA|];
  assert(HH2 := contains_four_non_coplanar_points_sublist (a0 :: p :: l0) (a :: a0 :: p :: l0) HH1 HH);
  rewrite HH2 in HH0;my_rank.
Qed.

Lemma matroid3_aux10_aux6 :
forall l, forall a,
rkl (a :: l) = 2 ->
rkl l = 1 \/ rkl l = 2.
Proof.
my_rank;induction l;my_rank;simpl;case_eq l;my_rank;subst.
- assert(HH := matroid3_aux1_cop (p :: l0) a0 H1);rewrite HH in H2;my_rank.
- assert(HH := matroid3_aux1 (p :: l0) a0 H3);rewrite HH in H4;my_rank.
- subst;assert(HH := matroid3_aux1_col_bis (p :: l0) a0 H3);assert(HH0 := matroid3_aux9_bis_bis_aux (a :: a0 :: p :: l0) H);
  assert(HH1 : inclA eq (a0 :: p :: l0) (a :: a0 :: p :: l0));[my_inA|];
  assert(HH2 := contains_three_non_collinear_points_sublist (a0 :: p :: l0) (a :: a0 :: p :: l0) HH1 HH);
  rewrite HH2 in HH0;my_rank.
- subst;assert(HH := matroid3_aux1_cop_bis (p :: l0) a0 H1);assert(HH0 := matroid3_aux9_bis_bis_alt (a :: a0 :: p :: l0) H);
  assert(HH1 : inclA eq (a0 :: p :: l0) (a :: a0 :: p :: l0));[my_inA|];
  assert(HH2 := contains_four_non_coplanar_points_sublist (a0 :: p :: l0) (a :: a0 :: p :: l0) HH1 HH);
  rewrite HH2 in HH0;my_rank.
Qed.

Lemma matroid3_aux10_aux7 :
forall l, forall a,
rkl (a :: l) = 4 ->
rkl l = 3 \/ rkl l = 4.
Proof.
my_rank;induction l;my_rank;simpl;case_eq l;my_rank;subst.
- simplgen H;case_eq(eq_dec_u a a0);my_rank.
- assert(HH := matroid3_aux2_col (p :: l0) H6 H4);
  subst;assert(HH0 : equivlistA eq (a :: a0 :: p :: l0) (a :: p :: l0));[my_inA|];
  rewrite HH0 in H;my_rank.
- assert(HH := matroid3_aux3 (p :: l0) H6);
  subst;assert(HH0 : equivlistA eq (a :: a0 :: p :: l0) (a :: p :: l0));[my_inA|];
  rewrite HH0 in H;my_rank.
- assert(HH := matroid3_aux9_alt (a :: a0 :: p :: l0) H);
  assert(HH0 := contains_four_to_three_aux2 (a0 :: p :: l0) a HH).
  assert(HH1 := matroid3_aux1_col_bis_bis (p :: l0) a0 H3).
  rewrite HH0 in HH1;my_rank.
Qed.

Lemma matroid3_aux10_bis :
forall l m,
rkl m = 1 ->
rkl (list_inter l m) = 0 \/ rkl(list_inter l m) = 1.
Proof.
my_rank;induction l;my_rank.
unfold list_inter;simpl;case_eq(Inb a m);my_rank;simpl;case_eq(list_inter l m);my_rank;rewrite list_inter_rewrite in H2.
- rewrite H2 in H1;inversion H1.
- rewrite H2 in H1;inversion H1.
- rewrite H2 in H1;inversion H1.
- rewrite H2 in H1;inversion H1.
- rewrite H2 in H1;inversion H1.
- rewrite H2 in H1;inversion H1.
- assert(HH := matroid3_aux1_cop (p0 :: l1) a H3);rewrite H4 in HH;my_rank.
- assert(HH := matroid3_aux1 (p0 :: l1) a H5);rewrite H6 in HH;my_rank.
- subst;assert(HH := matroid3_aux2_col (p0 :: l1) H8 H6);rewrite <-H2 in HH;my_rank.
- assert(HH := Inb_aux1 a m H0);assert(HH0 : equivlistA eq (a :: m) m);[my_inA|];rewrite <-HH0 in *;
  assert(HH1 := matroid3_aux9_bis l1 a p0 n);
  assert(HH2 : inclA eq (a :: list_inter l m) (a :: m));[apply inclA_aux5;apply inclA_inter_bis|];rewrite <-H2 in *;
  assert(HH3 := contains_two_distinct_points_sublist (a :: list_inter l m) (a :: m) HH2 HH1);
  assert(HH4 := matroid3_aux9_bis_bis (a :: m) H);rewrite HH4 in HH3;my_rank.
- assert(HH1 := matroid3_aux1_col_bis (p0 :: l1) a H5);
  assert(HH := Inb_aux1 a m H0);assert(HH0 : equivlistA eq (a :: m) m);[my_inA|];rewrite <-HH0 in *;
  assert(HH2 : inclA eq (a :: list_inter l m) (a :: m));[apply inclA_aux5;apply inclA_inter_bis|];rewrite <-H2 in *;
  assert(HH3 := contains_three_non_collinear_points_sublist (a :: list_inter l m) (a :: m) HH2 HH1);
  assert(HH4 := matroid3_aux9_bis_bis_aux2 (a :: m) H);rewrite HH4 in HH3;my_rank.
- assert(HH := matroid3_aux1_cop_bis (p0 :: l1) a H3);rewrite <-H2 in HH;assert(HH0 := matroid3_aux3_bis_bis (a :: list_inter l m) HH);
  assert(HH1 := matroid3_aux10_aux7 (list_inter l m) a HH0);my_rank.
Qed.

Lemma matroid3_aux13 :
forall l m, forall a,
rkl (a :: l) = 1 ->
rkl (a :: list_inter l m) = 1.
Proof.
my_rank;simpl;
assert(HH : inclA eq (list_inter l m) (a :: l));
[apply inclA_aux4_bis;apply inclA_inter|].
assert(HH0 : inclA eq (a :: list_inter l m) (a :: l));
[apply inclA_aux5;apply inclA_inter|].
case_eq(list_inter l m);my_rank;rewrite <-H0 in *.

assert(HH2 := matroid3_aux1_cop (list_inter l m) a H1);rewrite H2 in HH2;inversion HH2.
assert(HH2 := matroid3_aux1 (list_inter l m) a H3);rewrite H4 in HH2;inversion HH2.
assert(HH2 := contains_two_distinct_points_sublist (list_inter l m) (a :: l) HH H6);
assert(HH3 := matroid3_aux9_bis_bis (a :: l) H);rewrite HH2 in HH3;my_rank.
assert(HH2 := matroid3_aux9_bis l0 a p n);rewrite <-H0 in HH2;
assert(HH3 := contains_two_distinct_points_sublist (a :: list_inter l m) (a :: l) HH0 HH2);
assert(HH4 := matroid3_aux9_bis_bis (a :: l) H);rewrite HH3 in HH4;my_rank.
assert(HH2 := matroid3_aux1_col_bis (list_inter l m) a H3);
assert(HH3 := contains_three_non_collinear_points_sublist (a :: list_inter l m) (a :: l) HH0 HH2);
assert(HH4 := matroid3_aux9_bis_bis_aux2 (a :: l) H);rewrite HH3 in HH4;my_rank.
assert(HH2 := matroid3_aux1_cop_bis (list_inter l m) a H1);
assert(HH3 := contains_four_non_coplanar_points_sublist (a :: list_inter l m) (a :: l) HH0 HH2);
assert(HH4 := matroid3_aux9_bis_bis_aux3 (a :: l) H);rewrite HH3 in HH4;my_rank.
Qed.

Lemma matroid3_aux13_bis :
forall l m, forall a,
rkl (a :: l) = 1 ->
rkl (list_inter l m) = 0 \/ rkl (list_inter l m) = 1.
Proof.
my_rank;unfold rkl;
assert(HH : inclA eq (list_inter l m) (a :: l));
[apply inclA_aux4_bis;apply inclA_inter|].
assert(HH0 : inclA eq (a :: list_inter l m) (a :: l));
[apply inclA_aux5;apply inclA_inter|].
case_eq(list_inter l m);my_rank.
subst;rewrite <-H0 in *;assert(HH1 := contains_four_non_coplanar_points_sublist (list_inter l m) (a :: l) HH H2);
assert(HH2 := matroid3_aux9_bis_bis_aux3 (a :: l) H);rewrite HH1 in HH2;my_rank.
subst;rewrite <-H0 in *;assert(HH1 := contains_three_non_collinear_points_sublist (list_inter l m) (a :: l) HH H3);
assert(HH2 := matroid3_aux9_bis_bis_aux2 (a :: l) H);rewrite HH1 in HH2;my_rank.
subst;rewrite <-H0 in *;assert(HH1 := contains_two_distinct_points_sublist (list_inter l m) (a :: l) HH H4);
assert(HH2 := matroid3_aux9_bis_bis (a :: l) H);rewrite HH1 in HH2;my_rank.
Qed.

Lemma matroid3_aux14 :
forall l m, forall a,
rkl (a :: l) = 2 ->
rkl (list_inter l m) = 0 \/ rkl (list_inter l m) = 1 \/ rkl(list_inter l m) = 2.
Proof.
my_rank;unfold rkl;
assert(HH : inclA eq (list_inter l m) (a :: l));
[apply inclA_aux4_bis;apply inclA_inter|].
assert(HH0 : inclA eq (a :: list_inter l m) (a :: l));
[apply inclA_aux5;apply inclA_inter|].
case_eq(list_inter l m);my_rank.
subst;rewrite <-H0 in *;assert(HH1 := contains_four_non_coplanar_points_sublist (list_inter l m) (a :: l) HH H2);
assert(HH2 := matroid3_aux9_bis_bis_alt (a :: l) H);rewrite HH1 in HH2;my_rank.
subst;rewrite <-H0 in *;assert(HH1 := contains_three_non_collinear_points_sublist (list_inter l m) (a :: l) HH H3);
assert(HH2 := matroid3_aux9_bis_bis_aux (a :: l) H);rewrite HH1 in HH2;my_rank.
Qed.

Lemma matroid3_aux14_bis :
forall l m, forall a,
rkl (a :: l) = 2 ->
rkl m = 2 ->
rkl (a :: list_inter l m) = 1 \/ rkl (a :: list_inter l m) = 2.
Proof.
my_rank;simpl;
assert(HH : inclA eq (list_inter l m) (a :: l));
[apply inclA_aux4_bis;apply inclA_inter|].
assert(HH0 : inclA eq (a :: list_inter l m) (a :: l));
[apply inclA_aux5;apply inclA_inter|].
case_eq(list_inter l m);my_rank.
assert(HH1 := matroid3_aux1_cop (p :: l0) a H2);rewrite H3 in HH1;inversion HH1.
assert(HH1 := matroid3_aux1 (p :: l0) a H4);rewrite H5 in HH1;inversion HH1.
assert(HH1 := matroid3_aux1_col_bis (p :: l0) a H4);rewrite <-H1 in *;
assert(HH2 := contains_three_non_collinear_points_sublist (a :: list_inter l m) (a :: l) HH0 HH1);
assert(HH3 := matroid3_aux9_bis_bis_aux (a :: l) H);rewrite HH2 in HH3;my_rank.
assert(HH1 := matroid3_aux1_cop_bis (p :: l0) a H2);rewrite <-H1 in *;
assert(HH2 := contains_four_non_coplanar_points_sublist (a :: list_inter l m) (a :: l) HH0 HH1);
assert(HH3 := matroid3_aux9_bis_bis_alt (a :: l) H);rewrite HH2 in HH3;my_rank.
Qed.

Lemma matroid3_aux15 :
forall l m, forall a,
rkl (a :: l) = 3 ->
rkl (list_inter l m) = 0 \/ rkl (list_inter l m) = 1 \/ rkl (list_inter l m) = 2 \/ rkl (list_inter l m) = 3.
Proof.
my_rank;unfold rkl;
assert(HH : inclA eq (list_inter l m) (a :: l));
[apply inclA_aux4_bis;apply inclA_inter|].
assert(HH0 : inclA eq (a :: list_inter l m) (a :: l));
[apply inclA_aux5;apply inclA_inter|].
case_eq(list_inter l m);my_rank.
subst;rewrite <-H0 in *;assert(HH1 := contains_four_non_coplanar_points_sublist (list_inter l m) (a :: l) HH H2);
assert(HH2 := matroid3_aux9_bis_bis_bis (a :: l) H);rewrite HH1 in HH2;my_rank.
Qed.

Lemma matroid3_aux15_bis :
forall l m, forall a,
rkl (a :: l) = 3 ->
rkl m = 2 ->
rkl (a :: list_inter l m) = 1 \/ rkl (a :: list_inter l m) = 2 \/ rkl (a :: list_inter l m) = 3.
Proof.
my_rank;simpl;
assert(HH : inclA eq (list_inter l m) (a :: l));
[apply inclA_aux4_bis;apply inclA_inter|].
assert(HH0 : inclA eq (a :: list_inter l m) (a :: l));
[apply inclA_aux5;apply inclA_inter|].
case_eq(list_inter l m);my_rank.
assert(HH1 := matroid3_aux1_cop (p :: l0) a H2);rewrite H3 in HH1;inversion HH1.
assert(HH1 := matroid3_aux1_cop_bis (p :: l0) a H2);rewrite <-H1 in *;
assert(HH2 := contains_four_non_coplanar_points_sublist (a :: list_inter l m) (a :: l) HH0 HH1);
assert(HH3 := matroid3_aux9_bis_bis_bis (a :: l) H);rewrite HH2 in HH3;my_rank.
Qed.

Lemma matroid3_aux16 :
forall l m, forall a,
rkl (a :: l) = 4 ->
rkl (list_inter l m) = 0 \/ rkl (list_inter l m) = 1 \/ rkl (list_inter l m) = 2 \/ rkl (list_inter l m) = 3 \/ rkl (list_inter l m) = 4.
Proof.
my_rank;unfold rkl;case_eq(list_inter l m);my_rank.
Qed.

Lemma matroid3_aux16_bis :
forall l m, forall a,
rkl (a :: l) = 4 ->
rkl m = 2 ->
rkl (a :: list_inter l m) = 1 \/ rkl (a :: list_inter l m) = 2 \/ rkl (a :: list_inter l m) = 3.
Proof.
my_rank;simpl;case_eq(list_inter l m);my_rank.
assert(HH := matroid3_aux1_cop (p :: l0) a H2);rewrite H3 in HH;inversion HH.
assert(HH := matroid3_aux1_cop_bis (p :: l0) a H2);rewrite <-H1 in HH;
assert(HH0 := matroid3_aux3_bis_bis (a :: list_inter l m) HH).
assert(HH1 := matroid3_aux10_aux7 (list_inter l m) a HH0).
assert(HH2 : inclA eq (list_inter l m) m);[apply inclA_inter_bis|].
destruct HH1. 
assert(HH3 := matroid3_aux9 (list_inter l m) H3);assert(HH4 := matroid3_aux9_bis_bis_aux m H0);
assert(HH5 := contains_three_non_collinear_points_sublist (list_inter l m) m HH2 HH3);
rewrite HH4 in HH5;my_rank.
assert(HH3 := matroid3_aux9_alt (list_inter l m) H3);assert(HH4 := matroid3_aux9_bis_bis_alt m H0);
assert(HH5 := contains_four_non_coplanar_points_sublist (list_inter l m) m HH2 HH3);
rewrite HH4 in HH5;my_rank.
Qed.

Lemma matroid3_aux17 :
forall l m,
rkl l = 1 ->
rkl m = 2 ->
rkl (l ++ m) + rkl (list_inter l m) <= 3.
Proof.
my_rank;induction l;my_rank.
inversion H.
unfold list_inter;simpl;case_eq(l ++ m);case_eq(Inb a m);my_rank;rewrite list_inter_rewrite.
- assert(HH := matroid3_aux13 l m a H);my_rank.
- assert(HH := matroid3_aux13_bis l m a H);my_rank.
- assert(HH := matroid3_aux1_cop (p :: l0) a H3);rewrite H4 in HH;my_rank.
- assert(HH := matroid3_aux1 (p :: l0) a H5);rewrite H6 in HH;my_rank.
- assert(HH := matroid3_aux13 l m a H);my_rank.
- assert(HH := matroid3_aux13 l m a H);my_rank.
- assert(HH := matroid3_aux13 l m a H);my_rank.
- assert(HH := matroid3_aux1_col_bis (p :: l0) a H5);assert(HH0 := matroid3_aux1_cop_bis_bis (p :: l0) a H3);
  assert(HH1 := matroid3_aux2_cop (a :: p :: l0) HH HH0);
  assert(HH2 := matroid3_aux10_aux4 l a H);assert(HH3 := Inb_aux1 a m H1);destruct HH2.
  + assert(HH4 := rk_nil l H6); rewrite HH4 in H2; simpl in H2;rewrite <-H2 in HH,HH0;
    assert(HH5: equivlistA eq (a :: m) m);[my_inA|].
    rewrite HH5 in HH,HH0;assert(HH6 := matroid3_aux2_cop m HH HH0);my_rank.
  + assert(HH4 := matroid3_aux10 l a H H6); assert(HH5 : equivlistA eq (a :: l ++ m) (l ++ m));[my_inA|];
    assert(HH6 := IHl H6);rewrite <-H2 in HH1;rewrite HH5 in HH1;rewrite <-HH1;
    rewrite <-HH1 in HH6;assert(HH7 := list_inter_split_reverse a l m HH3 HH4);
    assert(HH8 : equivlistA eq (a :: list_inter l m) (list_inter l m));[my_inA|];
    rewrite HH8;my_rank.
- assert(HH := matroid3_aux1_cop_bis (p :: l0) a H3);assert(HH1 := matroid3_aux3_bis_bis (a :: p :: l0) HH);
  assert(HH2 := matroid3_aux10_aux4 l a H);assert(HH3 := Inb_aux1 a m H1);destruct HH2.
  + assert(HH4 := rk_nil l H4); rewrite HH4 in H2; simpl in H2;rewrite <-H2 in HH;
    assert(HH5: equivlistA eq (a :: m) m);[my_inA|].
    rewrite HH5 in HH;assert(HH6 := matroid3_aux3_bis_bis m HH);my_rank.
  + assert(HH4 := matroid3_aux10 l a H H4); assert(HH5 : equivlistA eq (a :: l ++ m) (l ++ m));[my_inA|];
    assert(HH6 := IHl H4);rewrite <-H2 in HH1;rewrite HH5 in HH1;rewrite <-HH1.
    assert(HH7 := list_inter_split_reverse a l m HH3 HH4);
    assert(HH8 : equivlistA eq (a :: list_inter l m) (list_inter l m));[my_inA|];
    rewrite HH8;my_rank.
- assert(HH := matroid3_aux1_cop (p :: l0) a H3);rewrite H4 in HH;my_rank.
- assert(HH := matroid3_aux1 (p :: l0) a H5);rewrite H6 in HH;my_rank.
- assert(HH := matroid3_aux13_bis l m a H);my_rank.
- assert(HH := matroid3_aux13_bis l m a H);my_rank.
- assert(HH := matroid3_aux13_bis l m a H);my_rank.
- assert(HH := matroid3_aux1_col_bis (p :: l0) a H5);assert(HH0 := matroid3_aux1_cop_bis_bis (p :: l0) a H3);
  assert(HH1 := matroid3_aux2_cop (a :: p :: l0) HH HH0);
  rewrite <-H2 in HH1;assert(HH2 := matroid3_aux10_aux4 l a H);destruct HH2.
  + assert(HH3 := rk_nil l H6);rewrite HH3;my_rank.
  + assert(HH3 := matroid3_aux10 l a H H6);
    assert(HH4: equivlistA eq (a :: l ++ m) (l ++ m));[my_inA|].
    assert(HH5 := IHl H6);rewrite HH4 in HH1;my_rank.
- assert(HH := matroid3_aux1_cop_bis (p :: l0) a H3);assert(HH0 := matroid3_aux3_bis_bis (a :: p :: l0) HH);
  rewrite <-H2 in HH0;assert(HH1 := matroid3_aux10_aux4 l a H);destruct HH1.
  + assert(HH3 := rk_nil l H4);rewrite HH3 in HH0;
    assert(HH4 : equivlistA eq (a :: nil ++ m) (a :: m));[my_inA|];
    rewrite HH4 in HH0;assert(HH5 := matroid3_aux10_aux7 m a HH0);my_rank.
  + assert(HH3 := matroid3_aux10 l a H H4);
    assert(HH4: equivlistA eq (a :: l ++ m) (l ++ m));[my_inA|].
    assert(HH5 := IHl H4);rewrite HH4 in HH0;rewrite HH0 in HH5;my_rank.
Qed.

Lemma matroid3_aux17_bis_aux1 :
forall l,
contains_two_distinct_points l = true -> exists x, exists y, ~x[==]y /\ InA eq x l /\ InA eq y l.
Proof.
my_rank;induction l;[inversion H|];induction l;[inversion H|];my_rank.
case_eq(eq_dec_u a a0). 
- my_rank;assert(HH0 : equivlistA eq (a :: a0 :: l) (a0 :: l));[my_inA|];
  rewrite HH0 in H;assert(HH1 := IHl H);destruct HH1; destruct H1;
  exists x;exists x0;my_rank.
- my_rank;exists a;exists a0;my_rank.
Qed.

Lemma matroid3_aux17_bis_aux2 :
forall l,
rkl l = 2 <-> contains_two_distinct_points l = true /\ contains_three_non_collinear_points l = false.
Proof.
my_rank.
apply matroid3_aux9_bis_bis_reverse;my_rank.
apply matroid3_aux9_bis_bis_aux;my_rank.
apply matroid3_aux2_col;my_rank.
Qed.

Lemma matroid3_aux17_bis_aux3 :
forall l m, forall A B C,
contains_two_distinct_points (list_inter l m) = true ->
contains_three_non_collinear_points l = false ->
contains_three_non_collinear_points m = false ->
InA eq A l ->
InA eq B l ->
InA eq C m ->
collinear A B C = true /\ collinear A C B = true /\ 
collinear B C A = true /\ collinear B A C = true /\
collinear C A B = true /\ collinear C B A = true.
Proof.
intros l m A B C;case_eq (eq_dec_u A B).
my_rank;my_subst;my_rank;my_col.
my_rank;apply matroid3_aux17_bis_aux1 in H0;destruct H0;destruct H0;my_rank;
assert(HH0 := list_inter_split_bis x l m H6);assert(HH1 := list_inter_split_bis x0 l m H7);
my_rank; rewrite contains_2 in H1; rewrite contains_2 in H2;
assert(HH1 : collinear x B A = true);my_rank;
assert(HH2 : collinear x x0 A = true);my_rank;
assert(HH3 : collinear x x0 B = true);my_rank;
assert(HH4 : collinear x x0 C = true);my_rank;
assert(HH5 := col_trans x x0 B C H0 HH3 HH4);
assert(HH6 := col_trans x x0 A C H0 HH2 HH4);
case_eq(eq_dec_u x C);
solve[(my_rank;my_subst;my_col)|(my_rank;rewrite col_exchange2 in HH5;rewrite col_exchange2 in HH6;
assert(HH7 := col_trans_bis x C A B n0 HH6 HH5);my_col2)].
Qed.

Lemma matroid3_aux17_bis_aux :
forall l m,
rkl l = 2 ->
rkl m = 2 ->
rkl (list_inter l m) = 2 ->
rkl (l ++ m) = 2.
Proof.
my_rank;
apply matroid3_aux17_bis_aux2;apply matroid3_aux17_bis_aux2 in H;
apply matroid3_aux17_bis_aux2 in H0;apply matroid3_aux17_bis_aux2 in H1;
assert(HH : inclA eq l (l ++ m));[my_inA|];my_rank;
assert( HH0 := contains_two_distinct_points_sublist l (l ++ m) HH H);my_rank.
rewrite contains_2;my_rank;assert( HH1 := H1);rewrite (list_inter_reverse l m) in H1.
apply InA_app_iff in H5.
apply InA_app_iff in H6.
apply InA_app_iff in H7.
destruct H5;destruct H6;destruct H7.
rewrite contains_2 in H4;my_rank.
apply matroid3_aux17_bis_aux3 with (l:=l) (m:=m) (A:=A) (B:=B) (C:=C);assumption.
apply matroid3_aux17_bis_aux3 with (l:=l) (m:=m) (A:=A) (B:=C) (C:=B);assumption.
apply matroid3_aux17_bis_aux3 with (l:=m) (m:=l) (A:=B) (B:=C) (C:=A);assumption.
apply matroid3_aux17_bis_aux3 with (l:=l) (m:=m) (A:=B) (B:=C) (C:=A);assumption.
apply matroid3_aux17_bis_aux3 with (l:=m) (m:=l) (A:=A) (B:=C) (C:=B);assumption.
apply matroid3_aux17_bis_aux3 with (l:=m) (m:=l) (A:=A) (B:=B) (C:=C);assumption.
rewrite contains_2 in H3;my_rank.
Qed.

(*
Lemma matroid3_aux17_bis_bis_aux1 :
forall l,
contains_three_non_collinear_points l = true -> exists x, exists y, exists z, collinear x y z = false /\ InA eq x l /\ InA eq y l /\ InA eq z l.
Proof.
my_rank;induction l;[inversion H|];my_rank.
apply contains_1 in H;destruct H;destruct H;destruct H;my_rank.
exists x;exists x0;exists x1;my_rank.
Qed.
*)

Lemma matroid3_aux17_bis_bis_aux2 :
forall l,
rkl l = 3 <-> contains_three_non_collinear_points l = true /\ contains_four_non_coplanar_points l = false.
Proof.
my_rank.
apply matroid3_aux9;my_rank.
apply matroid3_aux9_bis_bis_bis;my_rank.
apply matroid3_aux2_cop;my_rank.
Qed.

Lemma matroid3_aux17_bis_bis_aux3 :
forall l,
contains_two_distinct_points l = false /\ l <> nil -> exists x, InA eq x l.
Proof.
my_rank;induction l;my_rank.
exists a;my_rank.
Qed.

Lemma matroid3_aux17_bis_bis_aux4 :
forall l,
rkl l = 1 <-> contains_two_distinct_points l = false /\ l <> nil.
Proof.
my_rank.
apply matroid3_aux9_bis_bis;my_rank.
rewrite H0 in H;my_rank;simpl in H;my_rank.
assert(HH0 := matroid3_aux3 l H);assert(HH1 := matroid3_aux3_bis l H0);my_rank.
Qed.

Lemma matroid3_aux17_bis_bis_aux5 :
forall A B C D,
A[==]B ->
coplanar A B C D = true /\ coplanar A B D C = true /\
coplanar A C B D = true /\ coplanar A C D B = true /\
coplanar A D B C = true /\ coplanar A D C B = true /\
coplanar B A C D = true /\ coplanar B A D C = true /\
coplanar B C A D = true /\ coplanar B C D A = true /\
coplanar B D A C = true /\ coplanar B D C A = true /\
coplanar C A B D = true /\ coplanar C A D B = true /\
coplanar C B A D = true /\ coplanar C B D A = true /\
coplanar C D A B = true /\ coplanar C D B A = true /\
coplanar D A B C = true /\ coplanar D A C B = true /\
coplanar D B A C = true /\ coplanar D B C A = true /\
coplanar D C A B = true /\ coplanar D C B A = true.
Proof.
my_rank;rewrite H;assert(HH := cop_1 B C D);my_cop2.
Qed.

Lemma matroid3_aux17_bis_bis_aux6 :
forall x x0 x1 A,
collinear x x0 x1 = false ->
collinear x x0 A = false \/ collinear x x1 A = false \/ collinear x0 x1 A = false.
Proof.
intros.
unfold collinear.
case_eq (eq_dec_u x x0).
intros.
rewrite e in *.
assert( HH18 := col_1 x0 x1).
rewrite HH18 in H.
inversion H.
case_eq (eq_dec_u x x1).
intros.
rewrite e in *.
assert( HH18 := col_1 x1 x0).
assert( HH19 := col_shift x1 x1 x0).
rewrite HH19 in HH18.
rewrite HH18 in H.
inversion H.
case_eq (eq_dec_u x0 x1).
intros.
rewrite e in *.
assert( HH18 := col_2 x x1).
rewrite HH18 in H.
inversion H.
intros.
destruct (a1_exist x x0).
destruct (a1_exist x x1).
destruct (a1_exist x0 x1).
simpl.
case_eq (incid_dec A x2).
case_eq (incid_dec A x3).
case_eq (incid_dec A x4).
intros.
destruct a.
destruct a0.
destruct a1.
clear H0 H1 H2.
assert( HH0 := uniqueness x A x2 x3 H6 i1 H8 i0).
destruct HH0.
rewrite H0 in *.
assert( HH0 := uniqueness x0 A x2 x4 H7 i1 H10 i).
destruct HH0.
rewrite H1 in *.
apply False_ind.
apply n1.
reflexivity.
rewrite H1 in *.
rewrite <-H0 in *.
generalize H.
unfold collinear.
case_eq (eq_dec_u x x0).
intros.
contradiction.
destruct (a1_exist x x0).
simpl.
case_eq (incid_dec x1 x5).
intros.
inversion H13.
intros.
destruct a.
assert( HH0 := uniqueness x x0 x4 x5 H6 H7 H14 H15).
destruct HH0.
contradiction.
rewrite H16 in *.
contradiction.
rewrite H0 in *.
generalize H.
unfold collinear.
case_eq (eq_dec_u x x0).
intros.
contradiction.
destruct (a1_exist x x0).
simpl.
case_eq (incid_dec x1 x5).
intros.
inversion H12.
intros.
destruct a.
assert( HH0 := uniqueness x x0 x3 x5 H6 H7 H13 H14).
destruct HH0.
contradiction.
rewrite H15 in *.
contradiction.
intros.
right.
right.
reflexivity.
intros.
right.
left.
reflexivity.
intros.
left.
reflexivity.
Qed.

Lemma matroid3_aux17_bis_bis_aux8 :
forall l,
rkl l = 4 <-> contains_four_non_coplanar_points l = true.
Proof.
my_rank.
apply matroid3_aux9_alt;my_rank.
apply matroid3_aux3_bis_bis;my_rank.
Qed.

Lemma matroid3_aux17_bis_bis_aux11 :
forall A B C D E,
collinear A B E = true ->
collinear C D E = true ->
coplanar A B C D = true.
Proof.
intros.
unfold coplanar.
case_eq (eq_dec_u A B).
intros.
reflexivity.
intros.
case_eq (eq_dec_u C D).
intros.
reflexivity.
intros.
destruct (a1_exist A B).
destruct (a1_exist C D).
simpl.
case_eq (eq_dec_l x x0).
intros.
reflexivity.
intros.
case_eq (eq_dec_p x x0).
intros.
reflexivity.
intros.
generalize H.
generalize H0.
unfold collinear.
case_eq (eq_dec_u C D).
intros.
contradiction.
case_eq (eq_dec_u A B).
intros.
contradiction.
destruct (a1_exist C D).
destruct (a1_exist A B).
simpl.
case_eq (incid_dec E x1).
case_eq (incid_dec E x2).
intros.
clear H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
destruct a.
destruct a0.
destruct a1.
destruct a2.
assert( HH0 := uniqueness A B x x2 H1 H2 H7 H8).
destruct HH0.
contradiction.
assert( HH1 := uniqueness C D x0 x1 H3 H4 H5 H6).
destruct HH1.
contradiction.
rewrite H9 in *.
rewrite H10 in *.
assert( HH2 : Intersect x2 x1).
unfold Intersect.
exists E.
split.
assumption.
assumption.
contradiction.
intros.
inversion H10.
case_eq (incid_dec E x2).
intros.
inversion H9.
intros.
inversion H10.
Qed.

Lemma matroid3_aux17_bis_bis_aux12 :
forall l m, forall A B C D,
contains_three_non_collinear_points l = false ->
contains_three_non_collinear_points m = false ->
contains_two_distinct_points (list_inter l m) = false /\ list_inter l m <> nil ->
InA eq A l ->
InA eq B l ->
InA eq C m ->
InA eq D m ->
coplanar A B C D = true /\ coplanar A B D C = true /\
coplanar A C B D = true /\ coplanar A C D B = true /\
coplanar A D B C = true /\ coplanar A D C B = true /\
coplanar B A C D = true /\ coplanar B A D C = true /\
coplanar B C A D = true /\ coplanar B C D A = true /\
coplanar B D A C = true /\ coplanar B D C A = true /\
coplanar C A B D = true /\ coplanar C A D B = true /\
coplanar C B A D = true /\ coplanar C B D A = true /\
coplanar C D A B = true /\ coplanar C D B A = true /\
coplanar D A B C = true /\ coplanar D A C B = true /\
coplanar D B A C = true /\ coplanar D B C A = true /\
coplanar D C A B = true /\ coplanar D C B A = true.
Proof.
intros.
rewrite contains_2 in H.
rewrite contains_2 in H0.
apply matroid3_aux17_bis_bis_aux3 in H1.
destruct H1.
apply list_inter_split_bis in H1.
destruct H1.
assert( HH0 := H A B x H2 H3 H1).
assert( HH1 := H0 C D x H4 H5 H6).
assert( HH2 := matroid3_aux17_bis_bis_aux11 A B C D x HH0 HH1).
my_rank;my_cop2.
Qed.

Lemma matroid3_aux17_bis_aux_aux :
forall l m,
rkl l = 2 ->
rkl m = 2 ->
rkl (list_inter l m) = 1 ->
rkl (l ++ m) <> 4.
Proof.
intros.
intro.
apply matroid3_aux17_bis_aux2 in H.
apply matroid3_aux17_bis_aux2 in H0.
apply matroid3_aux17_bis_bis_aux4 in H1.
destruct H, H0.
apply matroid3_aux17_bis_bis_aux8 in H2.
apply contains_1_cop in H2.
destruct H2;destruct H2;destruct H2;destruct H2;
destruct H2;destruct H5;destruct H6;destruct H7.
assert( HH2 := list_inter_reverse l m).
apply InA_app_iff in H5.
apply InA_app_iff in H6.
apply InA_app_iff in H7.
apply InA_app_iff in H2.
destruct H5, H6, H7, H2.

(* Cas 4-0 3-1 ou 2-2 *)
apply contains_2 with (A:=x) (B:=x0) (C:=x1) in H3;my_rank.
assert( HH0 := col_to_cop x x0 x1 x2 H3);
rewrite HH0 in H8;my_rank.

apply contains_2 with (A:=x0) (B:=x1) (C:=x2) in H3;my_rank.
assert( HH0 := col_to_cop x0 x1 x2 x H3);
rewrite cop_exchange2 in HH0;
rewrite cop_exchange3 in HH0;
rewrite cop_exchange1 in HH0;
rewrite HH0 in H8;my_rank.

apply contains_2 with (A:=x) (B:=x0) (C:=x1) in H3;my_rank.
assert( HH0 := col_to_cop x x0 x1 x2 H3);
rewrite HH0 in H8;my_rank.

assert( HH50 := matroid3_aux17_bis_bis_aux12 l m x0 x1 x x2 H3 H4 H1 H5 H6 H2 H7);
my_rank;rewrite H21 in H8;my_rank.

apply contains_2 with (A:=x) (B:=x0) (C:=x2) in H3;my_rank.
assert( HH0 := col_to_cop x x0 x2 x1 H3);
rewrite cop_exchange2 in HH0;
rewrite HH0 in H8;my_rank.

assert( HH50 := matroid3_aux17_bis_bis_aux12 l m x0 x2 x x1 H3 H4 H1 H5 H7 H2 H6);
my_rank;rewrite H22 in H8;my_rank.

assert( HH50 := matroid3_aux17_bis_bis_aux12 l m x x0 x1 x2 H3 H4 H1 H2 H5 H6 H7);
my_rank;rewrite H9 in H8;my_rank.

apply contains_2 with (A:=x) (B:=x1) (C:=x2) in H4;my_rank.
assert( HH0 := col_to_cop x x1 x2 x0 H4);
rewrite cop_exchange2 in HH0;
rewrite cop_exchange3 in HH0;
rewrite HH0 in H8;my_rank.

apply contains_2 with (A:=x) (B:=x1) (C:=x2) in H3;my_rank.
assert( HH0 := col_to_cop x x1 x2 x0 H3);
rewrite cop_exchange2 in HH0;
rewrite cop_exchange3 in HH0;
rewrite HH0 in H8;my_rank.

assert( HH50 := matroid3_aux17_bis_bis_aux12 l m x1 x2 x x0 H3 H4 H1 H6 H7 H2 H5);
my_rank;rewrite H25 in H8;my_rank.

assert( HH50 := matroid3_aux17_bis_bis_aux12 l m x x1 x0 x2 H3 H4 H1 H2 H6 H5 H7);
my_rank;rewrite H11 in H8;my_rank.

apply contains_2 with (A:=x) (B:=x0) (C:=x2) in H4;my_rank.
assert( HH0 := col_to_cop x x0 x2 x1 H4);
rewrite cop_exchange2 in HH0;
rewrite HH0 in H8;my_rank.

assert( HH50 := matroid3_aux17_bis_bis_aux12 l m x x2 x0 x1 H3 H4 H1 H2 H7 H5 H6);
my_rank;rewrite H12 in H8;my_rank.

apply contains_2 with (A:=x) (B:=x0) (C:=x1) in H4;my_rank.
assert( HH0 := col_to_cop x x0 x1 x2 H4);
rewrite HH0 in H8;my_rank.

apply contains_2 with (A:=x0) (B:=x1) (C:=x2) in H4;my_rank.
assert( HH0 := col_to_cop x0 x1 x2 x H4);
rewrite cop_exchange2 in HH0;
rewrite cop_exchange3 in HH0;
rewrite cop_exchange1 in HH0;
rewrite HH0 in H8;my_rank.

apply contains_2 with (A:=x) (B:=x0) (C:=x1) in H4;my_rank.
assert( HH0 := col_to_cop x x0 x1 x2 H4);
rewrite HH0 in H8;my_rank.

Qed.

Lemma matroid3_aux17_bis :
forall l m,
rkl l = 2 ->
rkl m = 2 ->
rkl (l ++ m) + rkl (list_inter l m) <= 4.
Proof.
my_rank;induction l;my_rank.
inversion H.
unfold list_inter;simpl;case_eq(l ++ m);case_eq(Inb a m);my_rank;rewrite list_inter_rewrite.
- assert(HH := matroid3_aux14_bis l m a H);my_rank.
- assert(HH := matroid3_aux14 l m a H);my_rank.
- assert(HH := matroid3_aux1_cop (p :: l0) a H3);rewrite H4 in HH;my_rank.
- assert(HH := matroid3_aux1 (p :: l0) a H5);rewrite H6 in HH;my_rank.
- assert(HH := matroid3_aux14_bis l m a H);my_rank.
- assert(HH := matroid3_aux14_bis l m a H);my_rank.
- assert(HH := matroid3_aux14_bis l m a H);my_rank.
- assert(HH := matroid3_aux14_bis l m a H H0); progress intuition.
  assert(HH : rkl(list_inter (a :: l) m) = 2);
  [unfold list_inter;simpl;case_eq(Inb a m);rewrite list_inter_rewrite;my_rank|]. rewrite H7 in H1;my_rank.
  assert(HH0 := matroid3_aux17_bis_aux (a :: l) m H H0 HH);assert(HH1 : equivlistA eq ((a :: l) ++ m) (a :: l ++ m));[my_inA|].
  assert(HH2 := matroid3_aux1_col_bis (p :: l0) a H5);assert(HH3 := matroid3_aux1_cop_bis_bis (p :: l0) a H3);
  assert(HH4 := matroid3_aux2_cop (a :: p :: l0) HH2 HH3);rewrite <-H2 in HH4;rewrite HH1 in HH0;my_rank.
- assert(HH := matroid3_aux1_cop_bis (p :: l0) a H3);assert(HH1 := matroid3_aux3_bis_bis (a :: p :: l0) HH).
  assert(HH2 := matroid3_aux14_bis l m a H H0);progress intuition.
  + assert(HH3 : rkl(list_inter (a :: l) m) = 1);
    [unfold list_inter;simpl;case_eq(Inb a m);rewrite list_inter_rewrite;my_rank|]. rewrite H5 in H1;my_rank.
    assert(HH4 := matroid3_aux17_bis_aux_aux (a :: l) m H H0 HH3);
    assert(HH5 : equivlistA eq ((a :: l) ++ m) (a :: l ++ m));[my_inA|];
    rewrite <-H2 in HH1;rewrite HH5 in HH4;my_rank.
  + assert(HH3 : rkl(list_inter (a :: l) m) = 2);
    [unfold list_inter;simpl;case_eq(Inb a m);rewrite list_inter_rewrite;my_rank|]. rewrite H5 in H1;my_rank.
    assert(HH4 := matroid3_aux17_bis_aux (a :: l) m H H0 HH3).
    assert(HH5 : equivlistA eq ((a :: l) ++ m) (a :: l ++ m));[my_inA|];
    rewrite <-H2 in HH1;rewrite HH5 in HH4;my_rank.
- assert(HH := matroid3_aux1_cop (p :: l0) a H3);rewrite H4 in HH;my_rank.
- assert(HH := matroid3_aux1 (p :: l0) a H5);rewrite H6 in HH;my_rank.
- assert(HH := matroid3_aux14 l m a H);my_rank.
- assert(HH := matroid3_aux14 l m a H);my_rank.
- assert(HH := matroid3_aux14 l m a H);my_rank.
- assert(HH1 := matroid3_aux1_col_bis (p :: l0) a H5);assert(HH2 := matroid3_aux1_cop_bis_bis (p :: l0) a H3);
  assert(HH3 := matroid3_aux2_cop (a :: p :: l0) HH1 HH2);rewrite <-H2 in HH3;
  assert(HH4 := matroid3_aux14_bis l m a H H0); progress intuition.
  assert(HH5 := matroid3_aux10_aux4 (list_inter l m) a H6);my_rank.
  assert(HH5 := matroid3_aux10_aux6 (list_inter l m) a H6); progress intuition.
  assert(HH6 : rkl(list_inter (a :: l) m) = 2);
  [unfold list_inter;simpl;case_eq(Inb a m);rewrite list_inter_rewrite;my_rank|].
  assert(HH7 := matroid3_aux17_bis_aux (a :: l) m H H0 HH6);
  assert(HH8 : equivlistA eq ((a :: l) ++ m) (a :: l ++ m));[my_inA|].
  rewrite HH8 in HH7;my_rank.
- assert(HH1 := matroid3_aux1_cop_bis (p :: l0) a H3);assert(HH2 := matroid3_aux3_bis_bis (a :: p :: l0) HH1).
  rewrite <-H2 in HH2;assert(HH4 := matroid3_aux14_bis l m a H H0); progress intuition.
  assert(HH5 := matroid3_aux10_aux4 (list_inter l m) a H4);progress intuition.
  assert(HH3 : rkl(list_inter (a :: l) m) = 1);
  [unfold list_inter;simpl;case_eq(Inb a m);rewrite list_inter_rewrite;my_rank|].
  assert(HH6 := matroid3_aux17_bis_aux_aux (a :: l) m H H0 HH3);my_rank.
  assert(HH5 := matroid3_aux10_aux6 (list_inter l m) a H4); progress intuition.
  assert(HH3 : rkl(list_inter (a :: l) m) = 1);
  [unfold list_inter;simpl;case_eq(Inb a m);rewrite list_inter_rewrite;my_rank|]. rewrite H6 in H1;my_rank.
  assert(HH6 := matroid3_aux17_bis_aux_aux (a :: l) m H H0 HH3);my_rank.
  assert(HH3 : rkl(list_inter (a :: l) m) = 2);
  [unfold list_inter;simpl;case_eq(Inb a m);rewrite list_inter_rewrite;my_rank|].
  assert(HH4 := matroid3_aux17_bis_aux (a :: l) m H H0 HH3).
  assert(HH5 : equivlistA eq ((a :: l) ++ m) (a :: l ++ m));[my_inA|];
  rewrite <-H2 in HH1;rewrite HH5 in HH4;my_rank.
Qed.

Lemma matroid3_aux17_bis_bis_aux13 :
forall A B C D E,
~D[==]E ->
collinear A B C = false ->
collinear D E A = false \/ collinear D E B = false \/ collinear D E C = false.
Proof.
intros.
unfold collinear.
case_eq (eq_dec_u D E).
intros.
contradiction.
destruct (a1_exist D E).
simpl.
case_eq (incid_dec A x).
case_eq (incid_dec B x).
case_eq (incid_dec C x).
intros.
generalize H0.
unfold collinear.
case_eq (eq_dec_u A B).
intros.
inversion H6.
destruct (a1_exist A B).
simpl.
case_eq (incid_dec C x0).
intros.
inversion H7.
intros.
destruct a0.
assert( HH0 := uniqueness A B x x0 i1 i0 H8 H9).
destruct HH0.
contradiction.
clear H5.
clear H1.
rewrite H10 in *.
contradiction.
my_col.
my_col.
my_col.
Qed.

Lemma matroid3_aux17_bis_bis_aux14 :
forall A B C x x0 D,
~ x[==]x0 ->
collinear x x0 D = true ->
coplanar A B C x = true ->
coplanar A B C x0 = true ->
coplanar A B C D = true.
Proof.
intros.
unfold coplanar.
destruct (eq_dec_u A B).
reflexivity.
case_eq (eq_dec_u C D).
intros.
reflexivity.
destruct (a1_exist A B).
destruct (a1_exist C D).
simpl.
case_eq (eq_dec_l x1 x2).
intros.
reflexivity.
case_eq (eq_dec_p x1 x2).
intros.
reflexivity.
intros.
generalize H0.
unfold collinear.
case_eq (eq_dec_u x x0).
intros.
contradiction.
destruct (a1_exist x x0).
simpl.
case_eq (incid_dec D x3).
intros.
generalize H1, H2.
unfold coplanar.
case_eq (eq_dec_u A B).
intros.
contradiction.
case_eq (eq_dec_u C x).
case_eq (eq_dec_u C x0).
intros.
clear H9 H10.
rewrite e0 in e.
contradiction.
destruct (a1_exist A B).
destruct (a1_exist C x0).
simpl.
case_eq (eq_dec_l x4 x5).
intros.
clear H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14.
rewrite e in *.
rewrite e0 in *.
destruct a.
destruct a2.
assert( HH0 := uniqueness A B x1 x5 H3 H4 H5 H6).
destruct HH0.
contradiction.
rewrite H7 in *.
assert( Intersect x5 x2).
unfold Intersect.
exists x.
destruct a0.
destruct a3.
split.
assumption.
assumption.
contradiction.
case_eq (eq_dec_p x4 x5).
intros.
clear H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15.
rewrite e in *.
destruct a.
destruct a2.
assert( HH0 := uniqueness A B x1 x4 H3 H4 H5 H6).
destruct HH0.
contradiction.
rewrite H7 in *.
destruct a1.
destruct a3.
assert( HH0 := uniqueness x x0 x3 x5 H8 H9 H10 H11).
destruct HH0.
contradiction.
rewrite H12 in *.
destruct a0.
assert( HH0 := uniqueness x D x2 x5 H13 H14 H8 i).
destruct HH0.
contradiction.
rewrite H15 in *.
contradiction.
intros.
inversion H15.
destruct (a1_exist A B).
destruct (a1_exist C x).
destruct (a1_exist C x0).
simpl.
case_eq (eq_dec_l x4 x5).
case_eq (eq_dec_u C x0).
intros.
clear H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14.
rewrite e in *.
rewrite e0 in *.
destruct a.
destruct a2.
assert( HH0 := uniqueness A B x1 x5 H3 H4 H5 H6).
destruct HH0.
contradiction.
rewrite H7 in *.
assert( Intersect x5 x2).
unfold Intersect.
exists x0.
destruct a0.
destruct a3.
split.
assumption.
assumption.
contradiction.
case_eq (eq_dec_l x4 x6).
intros.
clear H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14.
rewrite e in *.
rewrite e0 in *.
destruct a.
destruct a2.
destruct a0.
destruct a3.
assert( HH0 := uniqueness A B x1 x5 H3 H4 H5 H6).
destruct HH0.
contradiction.
rewrite H11 in *.
assert( Intersect x5 x2).
unfold Intersect.
exists C.
split.
assumption.
assumption.
contradiction.
case_eq (eq_dec_p x4 x6).
intros.
clear H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16.
rewrite e in *.
destruct a.
destruct a2.
destruct a0.
destruct a3.
assert( HH0 := uniqueness A B x1 x5 H3 H4 H5 H6).
destruct HH0.
contradiction.
rewrite H11 in *.
assert( Intersect x5 x2).
unfold Intersect.
exists C.
split.
assumption.
assumption.
contradiction.
intros.
inversion H16.
case_eq (eq_dec_p x4 x5).
case_eq (eq_dec_u C x0).
intros.
clear H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15.
rewrite e in *.
destruct a.
destruct a2.
assert( HH0 := uniqueness A B x1 x4 H3 H4 H5 H6).
destruct HH0.
contradiction.
rewrite H7 in *.
destruct a1.
destruct a3.
assert( HH0 := uniqueness x x0 x3 x5 H8 H9 H11 H10).
destruct HH0.
contradiction.
rewrite H12 in *.
destruct a0.
assert( HH0 := uniqueness x0 D x2 x5 H13 H14 H9 i).
destruct HH0.
contradiction.
rewrite H15 in *.
contradiction.
case_eq (eq_dec_l x4 x6).
intros.
clear H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16.
rewrite e in *.
destruct a.
destruct a2.
assert( HH0 := uniqueness A B x1 x6 H3 H4 H5 H6).
destruct HH0.
contradiction.
rewrite H7 in *.
destruct a1.
destruct a3.
assert( Intersect x6 x2).
unfold Intersect.
exists C.
destruct a0.
destruct a4.
split.
assumption.
assumption.
contradiction.
case_eq (eq_dec_p x4 x6).
intros.
clear H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17.
destruct a.
destruct a2.
assert( HH0 := uniqueness A B x1 x4 H3 H4 H5 H6).
destruct HH0.
contradiction.
rewrite H7 in *.
destruct a1.
destruct a3.
unfold Intersect in i0.
destruct i0.
unfold Intersect in i1.
destruct i1.
case_eq (eq_dec_u x7 x8).
intros.
rewrite e in *.
destruct a4.
destruct H12.
destruct H13.
assert( HH0 := uniqueness C x8 x5 x6 H10 H18 H15 H17).
destruct HH0.
rewrite H19 in *.
assert( Intersect x4 x2).
unfold Intersect.
destruct a0.
exists x8.
split.
assumption.
assumption.
contradiction.
rewrite H19 in *.
assert( HH0 := uniqueness x x0 x3 x6 H8 H9 H11 H16).
destruct HH0.
contradiction.
rewrite H20 in *.
destruct a0.
assert( HH0 := uniqueness C D x2 x6 H21 H22 H10 i).
destruct HH0.
contradiction.
rewrite H23 in *.
assert( Intersect x4 x6).
unfold Intersect.
exists x8.
split.
assumption.
assumption.
contradiction.
intros.
case_eq (eq_dec_u x7 x).
intros.
rewrite e in *.
destruct a4.
destruct H12.
assert( HH0 := uniqueness C x x5 x6 H10 H11 H16 H18).
destruct HH0.
contradiction.
rewrite H19 in *.
assert( HH0 := uniqueness x x0 x3 x6 H8 H9 H11 H17).
destruct HH0.
contradiction.
rewrite H20 in *.
destruct a0.
assert( HH0 := uniqueness C D x2 x6 H21 H22 H10 i).
destruct HH0.
contradiction.
rewrite H23 in *.
assert( Intersect x4 x6).
unfold Intersect.
exists x8.
destruct H13.
split.
assumption.
assumption.
contradiction.
intros.
case_eq (eq_dec_u x8 x0).
intros.
rewrite e in *.
destruct a4.
destruct H13.
assert( HH0 := uniqueness C x0 x5 x6 H10 H19 H17 H18).
destruct HH0.
contradiction.
rewrite H20 in *.
assert( HH0 := uniqueness x x0 x3 x6 H8 H9 H11 H18).
destruct HH0.
contradiction.
rewrite H21 in *.
destruct a0.
assert( HH0 := uniqueness C D x2 x6 H22 H23 H10 i).
destruct HH0.
contradiction.
rewrite H24 in *.
assert( Intersect x4 x6).
unfold Intersect.
exists x7.
destruct H12.
split.
assumption.
assumption.
contradiction.
intros.

(* Cas degenere x7 = x0 *)
case_eq (eq_dec_u x7 x0).
intros.
clear H14 H15 H16.
rewrite e in *.
case_eq (eq_dec_u D x0).
intros.
rewrite e0 in *.
assert( Intersect x4 x2).
unfold Intersect.
destruct a0.
destruct H12.
exists x0.
split.
assumption.
assumption.
contradiction.
intros.
case_eq (eq_dec_u D x8).
intros.
rewrite e0 in *.
destruct a0.
destruct H13.
assert( HH0 : Intersect x4 x2).
unfold Intersect.
exists x8.
split.
assumption.
assumption.
contradiction.
case_eq (eq_dec_u x8 C).
intros.
rewrite e0 in *.
assert( Intersect x4 x2).
unfold Intersect.
exists C.
destruct a0.
destruct H13.
split.
assumption.
assumption.
contradiction.
intros.
assert( HH0 : dist4 x0 D x8 C).
unfold dist4.
split.
intro.
assert( HH0 := eq_reverse x0 D H18).
contradiction.
split.
assumption.
split.
intros.
intro.
assert( HH0 := eq_reverse x0 C H18).
contradiction.
split.
assumption.
split.
intro.
assert( HH0 := eq_reverse D C H18).
contradiction.
assumption.
destruct  a0, a4, H12, H13.
assert( HH1 : Incid x0 x3 /\ Incid D x3).
split.
assumption.
assumption.
assert( HH2 : Incid x8 x5 /\ Incid C x5).
split.
assumption.
assumption.
assert( HH3 : Incid x0 x4 /\ Incid x8 x4).
split.
assumption.
assumption.
assert( HH4 : Incid D x2 /\ Incid C x2).
split.
assumption.
assumption.
assert( HH5 : (exists I : Point, Incid I x3 /\ Incid I x5)).
exists x.
split.
assumption.
assumption.
assert( HH6 := a2 x0 D x8 C x3 x5 x4 x2 HH0 HH1 HH2 HH3 HH4 HH5).
destruct HH6.
destruct H24.
assert( Intersect x4 x2).
unfold Intersect.
exists x9.
split.
assumption.
assumption.
contradiction.

(* Cas degenere x8 = x *)
case_eq (eq_dec_u x8 x).
intros.
clear H14 H15 H16.
rewrite e in *.
case_eq (eq_dec_u D x).
intros.
rewrite e0 in *.
assert( Intersect x4 x2).
unfold Intersect.
destruct a0.
destruct H13.
exists x.
split.
assumption.
assumption.
contradiction.
intros.
case_eq (eq_dec_u D x7).
intros.
rewrite e0 in *.
destruct a0.
destruct H12.
assert( HH0 : Intersect x4 x2).
unfold Intersect.
exists x7.
split.
assumption.
assumption.
contradiction.
case_eq (eq_dec_u x7 C).
intros.
rewrite e0 in *.
assert( Intersect x4 x2).
unfold Intersect.
exists C.
destruct a0.
destruct H12.
split.
assumption.
assumption.
contradiction.
intros.
assert( HH0 : dist4 x D x7 C).
unfold dist4.
split.
intro.
assert( HH0 := eq_reverse x D H19).
contradiction.
split.
intros.
intro.
assert( HH0 := eq_reverse x x7 H19).
contradiction.
split.
intros.
intro.
assert( HH0 := eq_reverse x C H19).
contradiction.
split.
assumption.
split.
intro.
assert( HH0 := eq_reverse D C H19).
contradiction.
assumption.
destruct  a0, a4, H12, H13.
assert( HH1 : Incid x x3 /\ Incid D x3).
split.
assumption.
assumption.
assert( HH2 : Incid x7 x6 /\ Incid C x6).
split.
assumption.
assumption.
assert( HH3 : Incid x x4 /\ Incid x7 x4).
split.
assumption.
assumption.
assert( HH4 : Incid D x2 /\ Incid C x2).
split.
assumption.
assumption.
assert( HH5 : (exists I : Point, Incid I x3 /\ Incid I x6)).
exists x0.
split.
assumption.
assumption.
assert( HH6 := a2 x D x7 C x3 x6 x4 x2 HH0 HH1 HH2 HH3 HH4 HH5).
destruct HH6.
destruct H25.
assert( Intersect x4 x2).
unfold Intersect.
exists x9.
split.
assumption.
assumption.
contradiction.
intros.

(* Cas général *)
(* 1 er Pasch *)
assert( HH0 : dist4 x7 x0 x8 x).
unfold dist4.
split.
assumption.
split.
assumption.
split.
assumption.
split.
intros.
intro.
assert( HH0 := eq_reverse x0 x8 H19).
contradiction.
split.
intro.
assert( HH0 := eq_reverse x0 x H19).
contradiction.
assumption.
destruct  a0, a4, H12, H13.
assert( HH1 : Incid x7 x6 /\ Incid x0 x6).
split.
assumption.
assumption.
assert( HH2 : Incid x8 x5 /\ Incid x x5).
split.
assumption.
assumption.
assert( HH3 : Incid x7 x4 /\ Incid x8 x4).
split.
assumption.
assumption.
assert( HH4 : Incid x0 x3 /\ Incid x x3).
split.
assumption.
assumption.
assert( HH5 : (exists I : Point, Incid I x6 /\ Incid I x5)).
exists C.
split.
assumption.
assumption.
assert( HH6 := a2 x7 x0 x8 x x6 x5 x4 x3 HH0 HH1 HH2 HH3 HH4 HH5).
destruct HH6.
destruct H25.

(* 2 eme Pasch *)
clear H14 H15 H16 H17 H18 HH0 HH1 HH2 HH3 HH4 HH5.
case_eq (eq_dec_u x9 D).
intros.
rewrite e in *.
assert( HH6 : Intersect x4 x2).
unfold Intersect.
exists D.
split.
assumption.
assumption.
contradiction.
intros.
case_eq (eq_dec_u x9 x7).
intros.
rewrite e in *.
assert( HH0 := uniqueness x0 x7 x3 x6 H9 H26 H22 H23).
destruct HH0.
rewrite H16 in *.
apply False_ind.
apply n13.
reflexivity.
rewrite H16 in *.
assert( HH0 := uniqueness C D x2 x6 H19 H20 H21 i).
destruct HH0.
contradiction.
rewrite H17 in *.
assert( HH6 : Intersect x4 x6).
unfold Intersect.
exists x7.
split.
assumption.
assumption.
contradiction.
intros.
case_eq (eq_dec_u x9 C).
intros.
rewrite e in *.
assert( HH6 : Intersect x4 x2).
unfold Intersect.
exists C.
split.
assumption.
assumption.
contradiction.
intros.
case_eq (eq_dec_u D x7).
intros.
rewrite e in *.
assert( HH6 : Intersect x4 x2).
unfold Intersect.
exists x7.
split.
assumption.
assumption.
contradiction.
intros.
case_eq (eq_dec_u x7 C).
intros.
rewrite e in *.
assert( HH6 : Intersect x4 x2).
unfold Intersect.
exists C.
split.
assumption.
assumption.
contradiction.
intros.
assert( HH0 : dist4 x9 D x7 C).
unfold dist4.
split.
assumption.
split.
assumption.
split.
assumption.
split.
assumption.
split.
intro.
assert( HH0 := eq_reverse D C H27).
contradiction.
assumption.
assert( HH1 : Incid x9 x3 /\ Incid D x3).
split.
assumption.
assumption.
assert( HH2 : Incid x7 x6 /\ Incid C x6).
split.
assumption.
assumption.
assert( HH3 : Incid x9 x4 /\ Incid x7 x4).
split.
assumption.
assumption.
assert( HH4 : Incid D x2 /\ Incid C x2).
split.
assumption.
assumption.
assert( HH5 : (exists I : Point, Incid I x3 /\ Incid I x6)).
exists x0.
split.
assumption.
assumption.
assert( HH6 := a2 x9 D x7 C x3 x6 x4 x2 HH0 HH1 HH2 HH3 HH4 HH5).
destruct HH6.
destruct H27.
assert( HH6 : Intersect x4 x2).
unfold Intersect.
exists x10.
split.
assumption.
assumption.
contradiction.
intros.
inversion H17.
intros.
inversion H13.
intros.
inversion H8.
Qed.

Lemma matroid3_aux17_bis_bis_aux15 :
forall l m, forall A B C D,
contains_four_non_coplanar_points l = false ->
contains_three_non_collinear_points m = false ->
contains_two_distinct_points (list_inter l m) = true ->
InA eq A l ->
InA eq B l ->
InA eq C l ->
InA eq D m ->
coplanar A B C D = true /\ coplanar A B D C = true /\
coplanar A C B D = true /\ coplanar A C D B = true /\
coplanar A D B C = true /\ coplanar A D C B = true /\
coplanar B A C D = true /\ coplanar B A D C = true /\
coplanar B C A D = true /\ coplanar B C D A = true /\
coplanar B D A C = true /\ coplanar B D C A = true /\
coplanar C A B D = true /\ coplanar C A D B = true /\
coplanar C B A D = true /\ coplanar C B D A = true /\
coplanar C D A B = true /\ coplanar C D B A = true /\
coplanar D A B C = true /\ coplanar D A C B = true /\
coplanar D B A C = true /\ coplanar D B C A = true /\
coplanar D C A B = true /\ coplanar D C B A = true.
Proof.
intros.
rewrite contains_2_cop in H.
rewrite contains_2 in H0.
apply matroid3_aux17_bis_aux1 in H1.
destruct H1.
destruct H1.
destruct H1.
destruct H6.
apply list_inter_split_bis in H6.
apply list_inter_split_bis in H7.
destruct H6.
destruct H7.
case_eq (collinear A B C).
intros.
assert (HH0 := col_to_cop A B C D H10).
my_rank;my_cop2.
intros.
assert( HH1 := H0 x x0 D H8 H9 H5).
assert( HH2 := H A B C x H2 H3 H4 H6).
assert( HH3 := H A B C x0 H2 H3 H4 H7).
assert( HH4 := matroid3_aux17_bis_bis_aux14 A B C x x0 D H1 HH1 HH2 HH3).
my_rank;my_cop2.
Qed.

Lemma matroid3_aux17_bis_bis_aux16 :
forall l m, forall A B C D,
contains_four_non_coplanar_points l = false ->
contains_three_non_collinear_points m = false ->
contains_two_distinct_points (list_inter l m) = true ->
InA eq A l ->
InA eq B l ->
InA eq C m ->
InA eq D m ->
coplanar A B C D = true /\ coplanar A B D C = true /\
coplanar A C B D = true /\ coplanar A C D B = true /\
coplanar A D B C = true /\ coplanar A D C B = true /\
coplanar B A C D = true /\ coplanar B A D C = true /\
coplanar B C A D = true /\ coplanar B C D A = true /\
coplanar B D A C = true /\ coplanar B D C A = true /\
coplanar C A B D = true /\ coplanar C A D B = true /\
coplanar C B A D = true /\ coplanar C B D A = true /\
coplanar C D A B = true /\ coplanar C D B A = true /\
coplanar D A B C = true /\ coplanar D A C B = true /\
coplanar D B A C = true /\ coplanar D B C A = true /\
coplanar D C A B = true /\ coplanar D C B A = true.
Proof.
intros.
rewrite contains_2_cop in H.
rewrite contains_2 in H0.
apply matroid3_aux17_bis_aux1 in H1.
destruct H1.
destruct H1.
destruct H1.
destruct H6.
apply list_inter_split_bis in H6.
apply list_inter_split_bis in H7.
destruct H6.
destruct H7.
case_eq (collinear A B D).
intros.
assert (HH0 := col_to_cop A B D C H10).
rewrite cop_exchange2 in HH0.
my_rank;my_cop2.
intros.
assert( HH0 := H0 x x0 D H8 H9 H5).
assert( HH1 := cop_3 A B x).
assert( HH2 := H A B x x0 H2 H3 H6 H7).
assert( HH3 := matroid3_aux17_bis_bis_aux14 A B x x x0 D H1 HH0 HH1 HH2).
rewrite cop_exchange2 in HH3.
rewrite cop_exchange2 in HH2.
assert( HH4 := cop_3 A B x0).
assert( HH5 := matroid3_aux17_bis_bis_aux14 A B x0 x x0 D H1 HH0 HH2 HH4).
rewrite cop_exchange2 in HH5.
assert( HH6 := H0 x x0 C H8 H9 H4).
assert( HH7 := matroid3_aux17_bis_bis_aux14 A B D x x0 C H1 HH6 HH3 HH5).
rewrite cop_exchange2 in HH7.
my_rank;my_cop2.
Qed.

Lemma matroid3_aux17_bis_bis_aux :
forall l m,
rkl l = 3 ->
rkl m = 2 ->
rkl (list_inter l m) = 2 ->
rkl (l ++ m) = 3.
Proof.
intros.
apply matroid3_aux17_bis_bis_aux2 in H.
apply matroid3_aux17_bis_aux2 in H0.
apply matroid3_aux17_bis_aux2 in H1.
apply matroid3_aux17_bis_bis_aux2.
destruct H, H0, H1.
split.
assert( inclA eq l (l ++ m));[my_inA|].
assert( HH0 := contains_three_non_collinear_points_sublist l (l ++ m) H5 H).
assumption.
apply contains_2_cop.
intros.
assert( HH2 := list_inter_reverse l m).
apply InA_app_iff in H5.
apply InA_app_iff in H6.
apply InA_app_iff in H7.
apply InA_app_iff in H8.
destruct H5, H6, H7, H8.

(* Cas 4-0 *)
rewrite contains_2_cop in H2.
assert( HH0 := H2 A B C D H5 H6 H7 H8).
assumption.

(* Cas 3-1 1-3 et 2-2 *)
assert( HH0 := matroid3_aux17_bis_bis_aux15 l m A B C D H2 H3 H1 H5 H6 H7 H8).
destruct HH0.
assumption.
assert( HH0 := matroid3_aux17_bis_bis_aux15 l m A B D C H2 H3 H1 H5 H6 H8 H7).
destruct HH0.
destruct H10.
assumption.
assert( HH0 := matroid3_aux17_bis_bis_aux16 l m A B C D H2 H3 H1 H5 H6 H7 H8).
destruct HH0.
assumption.
assert( HH0 := matroid3_aux17_bis_bis_aux15 l m A C D B H2 H3 H1 H5 H7 H8 H6).
destruct HH0.
destruct H10. destruct H11. destruct H12. destruct H13.
assumption.
assert( HH0 := matroid3_aux17_bis_bis_aux16 l m A C B D H2 H3 H1 H5 H7 H6 H8).
destruct HH0.
destruct H10. destruct H11.
assumption.
assert( HH0 := matroid3_aux17_bis_bis_aux16 l m A D B C H2 H3 H1 H5 H8 H6 H7).
destruct HH0.
destruct H10. destruct H11. destruct H12.
assumption.
rewrite contains_2 in H3.
assert( HH0 := H3 B C D H6 H7 H8).
assert( HH1 := col_to_cop B C D A HH0).
rewrite cop_exchange2 in HH1.
rewrite cop_exchange3 in HH1.
rewrite cop_exchange1 in HH1.
assumption.
assert( HH0 := matroid3_aux17_bis_bis_aux15 l m B C D A H2 H3 H1 H6 H7 H8 H5).
destruct HH0.
destruct H10. destruct H11. destruct H12. destruct H13. destruct H14. destruct H15. destruct H16. destruct H17. destruct H18. destruct H19. destruct H20. destruct H21. destruct H22. destruct H23. destruct H24. destruct H25. destruct H26. destruct H27. destruct H28.
assumption.
assert( HH0 := matroid3_aux17_bis_bis_aux16 l m B C A D H2 H3 H1 H6 H7 H5 H8).
destruct HH0.
destruct H10. destruct H11. destruct H12. destruct H13. destruct H14. destruct H15. destruct H16. destruct H17. destruct H18. destruct H19. destruct H20. destruct H21. destruct H22. destruct H23. destruct H24. destruct H25. destruct H26. destruct H27. destruct H28.
assumption.
assert( HH0 := matroid3_aux17_bis_bis_aux16 l m B D A C H2 H3 H1 H6 H8 H5 H7).
destruct HH0.
destruct H10. destruct H11. destruct H12. destruct H13. destruct H14. destruct H15. destruct H16. destruct H17. destruct H18. destruct H19. destruct H20. destruct H21. destruct H22. destruct H23. destruct H24. destruct H25. destruct H26. destruct H27. destruct H28.
assumption.
rewrite contains_2 in H3.
assert( HH0 := H3 A C D H5 H7 H8).
assert( HH1 := col_to_cop A C D B HH0).
rewrite cop_exchange2 in HH1.
rewrite cop_exchange3 in HH1.
assumption.
assert( HH0 := matroid3_aux17_bis_bis_aux16 l m C D A B H2 H3 H1 H7 H8 H5 H6).
destruct HH0.
destruct H10. destruct H11. destruct H12. destruct H13. destruct H14. destruct H15. destruct H16. destruct H17. destruct H18. destruct H19. destruct H20. destruct H21. destruct H22. destruct H23. destruct H24. destruct H25. destruct H26. destruct H27. destruct H28.
assumption.
rewrite contains_2 in H3.
assert( HH0 := H3 A B D H5 H6 H8).
assert( HH1 := col_to_cop A B D C HH0).
rewrite cop_exchange2 in HH1.
assumption.
rewrite contains_2 in H3.
assert( HH0 := H3 A B C H5 H6 H7).
assert( HH1 := col_to_cop A B C D HH0).
assumption.
rewrite contains_2 in H3.
assert( HH0 := H3 A B C H5 H6 H7).
assert( HH1 := col_to_cop A B C D HH0).
assumption.

Qed.

Lemma matroid3_aux17_bis_bis :
forall l m,
rkl l = 3 ->
rkl m = 2 ->
rkl (l ++ m) + rkl (list_inter l m) <= 5.
Proof.
my_rank;induction l;my_rank.
inversion H.
unfold list_inter;simpl;case_eq(l ++ m);case_eq(Inb a m);my_rank;rewrite list_inter_rewrite.
- assert(HH := matroid3_aux15_bis l m a H);my_rank.
- assert(HH := matroid3_aux15 l m a H);my_rank.
- assert(HH := matroid3_aux1_cop (p :: l0) a H3);rewrite H4 in HH;my_rank.
- assert(HH := matroid3_aux1 (p :: l0) a H5);rewrite H6 in HH;my_rank.
- assert(HH := matroid3_aux15_bis l m a H);my_rank.
- assert(HH := matroid3_aux15_bis l m a H);my_rank.
- assert(HH := matroid3_aux15_bis l m a H);my_rank.
- assert(HH := matroid3_aux15_bis l m a H H0); progress intuition.
  assert(HH := Inb_aux1 a m H1);assert(HH0 : inclA eq (a :: list_inter l m) m);
  [my_inA;apply list_inter_split_bis in H9;my_inA|];
  assert(HH1 := matroid3_aux9_bis_bis_aux m H0);
  assert(HH2 := matroid3_aux9 (a :: list_inter l m) H7);
  assert(HH3 := contains_three_non_collinear_points_sublist (a :: list_inter l m) m HH0 HH2);
  rewrite HH3 in HH1;my_rank.
- assert(HH := matroid3_aux15_bis l m a H H0);assert(HH0 := matroid3_aux1_cop_bis (p :: l0) a H3);
  assert(HH1 := matroid3_aux3_bis_bis (a :: p :: l0) HH0);progress intuition.
  + rewrite <-H2 in HH1;assert(HH2 := Inb_aux1 a m H1);
    assert(HH3 : rkl(list_inter (a :: l) m) = 2);
    [unfold list_inter;simpl;case_eq(Inb a m);rewrite list_inter_rewrite;my_rank|]. rewrite H4 in H1;my_rank.
    assert(HH4 := matroid3_aux17_bis_bis_aux (a :: l) m H H0 HH3);
    assert(HH5 : equivlistA eq ((a :: l) ++ m) (a :: l ++ m));[my_inA|];
    rewrite HH5 in HH4;my_rank.
  + assert(HH2 := Inb_aux1 a m H1);assert(HH3 : inclA eq (a :: list_inter l m) m);
    [my_inA;apply list_inter_split_bis in H7;my_inA|].
    assert(HH4 := matroid3_aux9_bis_bis_aux m H0);
    assert(HH5 := matroid3_aux9 (a :: list_inter l m) H5);
    assert(HH6 := contains_three_non_collinear_points_sublist (a :: list_inter l m) m HH3 HH5);
    rewrite HH6 in HH4;my_rank.
- assert(HH := matroid3_aux1_cop (p :: l0) a H3);rewrite H4 in HH;my_rank.
- assert(HH := matroid3_aux1 (p :: l0) a H5);rewrite H6 in HH;my_rank.
- assert(HH := matroid3_aux15 l m a H);my_rank.
- assert(HH := matroid3_aux15 l m a H);my_rank.
- assert(HH := matroid3_aux15 l m a H);my_rank.
- assert(HH := matroid3_aux15 l m a H);progress intuition.
  assert(HH0 : inclA eq (list_inter l m) m);
  [my_inA;apply list_inter_split_bis in H7;my_inA|].
  assert(HH1 := matroid3_aux9_bis_bis_aux m H0);
  assert(HH2 := matroid3_aux9 (list_inter l m) H6);
  assert(HH3 := contains_three_non_collinear_points_sublist (list_inter l m) m HH0 HH2);
  rewrite HH3 in HH1;my_rank.
- assert(HH := matroid3_aux1_cop_bis (p :: l0) a H3);assert(HH0 := matroid3_aux3_bis_bis (a :: p :: l0) HH);
  assert(HH1 := matroid3_aux15 l m a H);progress intuition.
  assert(HH1 := matroid3_aux15_bis l m a H);progress intuition.
  + assert(HH1 := matroid3_aux10_aux4 (list_inter l m) a H6); progress intuition.
  + assert(HH2 : rkl(list_inter (a :: l) m) = 2);
    [unfold list_inter;simpl;case_eq(Inb a m);rewrite list_inter_rewrite;my_rank|];
    rewrite <-H2 in HH0; assert(HH3 := matroid3_aux17_bis_bis_aux (a :: l) m H H0 HH2);
    assert(HH4 : equivlistA eq ((a :: l) ++ m) (a :: l ++ m));[my_inA|];
    rewrite HH4 in HH3;my_rank.
  + assert(HH2 : rkl(list_inter (a :: l) m) = 2);
    [unfold list_inter;simpl;case_eq(Inb a m);rewrite list_inter_rewrite;my_rank|]. rewrite H6 in H1;my_rank.
    rewrite <-H2 in HH0; assert(HH3 := matroid3_aux17_bis_bis_aux (a :: l) m H H0 HH2);
    assert(HH4 : equivlistA eq ((a :: l) ++ m) (a :: l ++ m));[my_inA|];
    rewrite HH4 in HH3;my_rank.
  + assert(HH1 : inclA eq (list_inter l m) m);
    [my_inA;apply list_inter_split_bis in H5;my_inA|].
    assert(HH2 := matroid3_aux9_bis_bis_aux m H0);
    assert(HH3 := matroid3_aux9 (list_inter l m) H4);
    assert(HH4 := contains_three_non_collinear_points_sublist (list_inter l m) m HH1 HH3);
    rewrite HH4 in HH2;my_rank.
Qed.

Lemma matroid3_aux17_bis_bis_bis :
forall l m,
rkl l = 4 ->
rkl m = 2 ->
rkl (l ++ m) + rkl (list_inter l m) <= 6.
Proof.
my_rank;induction l;my_rank.
inversion H.
unfold list_inter;simpl;case_eq(l ++ m);case_eq(Inb a m);my_rank;rewrite list_inter_rewrite.
- assert(HH := matroid3_aux16_bis l m a H);my_rank.
- assert(HH := matroid3_aux16 l m a H);my_rank.
- assert(HH := matroid3_aux1_cop (p :: l0) a H3);rewrite H4 in HH;my_rank.
- assert(HH := matroid3_aux1 (p :: l0) a H5);rewrite H6 in HH;my_rank.
- assert(HH := matroid3_aux16_bis l m a H);my_rank.
- assert(HH := matroid3_aux16_bis l m a H);my_rank.
- assert(HH := matroid3_aux16_bis l m a H);my_rank.
- assert(HH := matroid3_aux16_bis l m a H H0);my_rank.
- assert(HH := matroid3_aux16_bis l m a H H0); progress intuition.
  assert(HH := Inb_aux1 a m H1);assert(HH0 : inclA eq (a :: list_inter l m) m);
  [my_inA;apply list_inter_split_bis in H7;my_inA|];
  assert(HH1 := matroid3_aux9_bis_bis_aux m H0);
  assert(HH2 := matroid3_aux9 (a :: list_inter l m) H5);
  assert(HH3 := contains_three_non_collinear_points_sublist (a :: list_inter l m) m HH0 HH2);
  rewrite HH3 in HH1;my_rank.
- assert(HH := matroid3_aux1_cop (p :: l0) a H3);rewrite H4 in HH;my_rank.
- assert(HH := matroid3_aux1 (p :: l0) a H5);rewrite H6 in HH;my_rank.
- assert(HH := matroid3_aux16 l m a H);my_rank.
- assert(HH := matroid3_aux16 l m a H);my_rank.
- assert(HH := matroid3_aux16 l m a H);my_rank.
- assert(HH := matroid3_aux16 l m a H); progress intuition.
  assert(HH0 : inclA eq (list_inter l m) m);
  [my_inA;apply list_inter_split_bis in H6;my_inA|].
  assert(HH1 := matroid3_aux9_bis_bis_alt m H0);
  assert(HH2 := matroid3_aux9_alt (list_inter l m) H7).
  assert(HH3 := contains_four_non_coplanar_points_sublist (list_inter l m) m HH0 HH2);
  rewrite HH3 in HH1;my_rank.
- assert(HH := matroid3_aux16 l m a H);assert(HH0 := matroid3_aux1_cop_bis (p :: l0) a H3);
  assert(HH1 := matroid3_aux3_bis_bis (a :: p :: l0) HH0);progress intuition.
  + assert(HH2 : inclA eq (list_inter l m) m);
    [my_inA;apply list_inter_split_bis in H4;my_inA|].
    assert(HH3 := matroid3_aux9_bis_bis_aux m H0);
    assert(HH4 := matroid3_aux9 (list_inter l m) H5);
    assert(HH5 := contains_three_non_collinear_points_sublist (list_inter l m) m HH2 HH4);
    rewrite HH5 in HH3;my_rank.
  + assert(HH2 : inclA eq (list_inter l m) m);
    [my_inA;apply list_inter_split_bis in H4;my_inA|].
    assert(HH3 := matroid3_aux9_bis_bis_alt m H0);
    assert(HH4 := matroid3_aux9_alt (list_inter l m) H5).
    assert(HH5 := contains_four_non_coplanar_points_sublist (list_inter l m) m HH2 HH4);
    rewrite HH5 in HH3;my_rank.
Qed.

Lemma matroid3_aux20 :
forall l m, forall a,
rkl (a :: l) = 1 ->
rkl m = 1 ->
rkl (a :: list_inter l m) = 1.
Proof.
my_rank;apply matroid3_aux13;my_rank.
Qed.

Lemma matroid3_aux21 :
forall l m, forall a,
rkl (a :: l) = 2 ->
rkl m = 1 ->
rkl (a :: list_inter l m) = 1 \/ rkl (a :: list_inter l m) = 2.
Proof.
my_rank;simpl;
assert(HH : inclA eq (list_inter l m) (a :: l));
[apply inclA_aux4_bis;apply inclA_inter|].
assert(HH0 : inclA eq (a :: list_inter l m) (a :: l));
[apply inclA_aux5;apply inclA_inter|].
case_eq(list_inter l m);my_rank.
subst;rewrite <-H1 in *;assert(HH2 := matroid3_aux1_cop (list_inter l m) a H2);rewrite H3 in HH2;inversion HH2.
subst;rewrite <-H1 in *;assert(HH2 := matroid3_aux1 (list_inter l m) a H4);rewrite H5 in HH2;inversion HH2.
assert(HH1 := matroid3_aux1_col_bis (p :: l0) a H4);rewrite <-H1 in *;
assert(HH2 := contains_three_non_collinear_points_sublist (a :: list_inter l m) (a :: l) HH0 HH1);
assert(HH3 := matroid3_aux9_bis_bis_aux (a :: l) H);rewrite HH2 in HH3;my_rank.
assert(HH1 := matroid3_aux1_cop_bis (p :: l0) a H2);rewrite <-H1 in *;
assert(HH2 := contains_four_non_coplanar_points_sublist (a :: list_inter l m) (a :: l) HH0 HH1);
assert(HH3 := matroid3_aux9_bis_bis_alt (a :: l) H);rewrite HH2 in HH3;my_rank.
Qed.

Lemma matroid3_aux22 :
forall l m, forall a,
rkl (a :: l) = 3 ->
rkl m = 1 ->
rkl (a :: list_inter l m) = 1 \/ rkl (a :: list_inter l m) = 2.
Proof.
my_rank;simpl;
assert(HH : inclA eq (list_inter l m) (a :: l));
[apply inclA_aux4_bis;apply inclA_inter|].
assert(HH0 : inclA eq (a :: list_inter l m) (a :: l));
[apply inclA_aux5;apply inclA_inter|].
case_eq(list_inter l m);my_rank.
subst;rewrite <-H1 in *;assert(HH2 := matroid3_aux1_cop (list_inter l m) a H2);rewrite H3 in HH2;inversion HH2.
subst;rewrite <-H1 in *;assert(HH2 := matroid3_aux1 (list_inter l m) a H4);rewrite H5 in HH2;inversion HH2.
assert(HH1 := matroid3_aux1_col_bis (p :: l0) a H4);assert(HH2 := matroid3_aux1_cop_bis_bis (p :: l0) a H2);
rewrite <-H1 in *;assert(HH3 := matroid3_aux2_cop (a :: list_inter l m) HH1 HH2);
assert(HH4 : inclA eq (list_inter l m) m);
[apply inclA_inter_bis|].
assert(HH5 := matroid3_aux10_aux5 (list_inter l m) a HH3). destruct HH5.
assert(HH6 := matroid3_aux9_bis_bis_reverse (list_inter l m) H5);
assert(HH7 := matroid3_aux9_bis_bis m H0);
assert(HH8 := contains_two_distinct_points_sublist (list_inter l m) m HH4 HH6);
rewrite HH8 in HH7;my_rank.
assert(HH6 := matroid3_aux9 (list_inter l m) H5);
assert(HH7 := matroid3_aux9_bis_bis_aux2 m H0);
assert(HH8 := contains_three_non_collinear_points_sublist (list_inter l m) m HH4 HH6);
rewrite HH8 in HH7;my_rank.
assert(HH1 := matroid3_aux1_cop_bis (p :: l0) a H2);rewrite <-H1 in *;
assert(HH2 := contains_four_non_coplanar_points_sublist (a :: list_inter l m) (a :: l) HH0 HH1);
assert(HH3 := matroid3_aux9_bis_bis_bis (a :: l) H);rewrite HH2 in HH3;my_rank.
Qed.

Lemma matroid3_aux23 :
forall l m, forall a,
rkl (a :: l) = 4 ->
rkl m = 1 ->
rkl (a :: list_inter l m) = 1 \/ rkl (a :: list_inter l m) = 2.
Proof.
my_rank;simpl;
assert(HH : inclA eq (list_inter l m) (a :: l));
[apply inclA_aux4_bis;apply inclA_inter|].
assert(HH0 : inclA eq (a :: list_inter l m) (a :: l));
[apply inclA_aux5;apply inclA_inter|].
case_eq(list_inter l m);my_rank.
subst;rewrite <-H1 in *;assert(HH2 := matroid3_aux1_cop (list_inter l m) a H2);rewrite H3 in HH2;inversion HH2.
subst;rewrite <-H1 in *;assert(HH2 := matroid3_aux1 (list_inter l m) a H4);rewrite H5 in HH2;inversion HH2.
assert(HH1 := matroid3_aux1_col_bis (p :: l0) a H4);assert(HH2 := matroid3_aux1_cop_bis_bis (p :: l0) a H2);
rewrite <-H1 in *;assert(HH3 := matroid3_aux2_cop (a :: list_inter l m) HH1 HH2);
assert(HH4 : inclA eq (list_inter l m) m);
[apply inclA_inter_bis|].
assert(HH5 := matroid3_aux10_aux5 (list_inter l m) a HH3). destruct HH5.
assert(HH6 := matroid3_aux9_bis_bis_reverse (list_inter l m) H5);
assert(HH7 := matroid3_aux9_bis_bis m H0);
assert(HH8 := contains_two_distinct_points_sublist (list_inter l m) m HH4 HH6);
rewrite HH8 in HH7;my_rank.
assert(HH6 := matroid3_aux9 (list_inter l m) H5);
assert(HH7 := matroid3_aux9_bis_bis_aux2 m H0);
assert(HH8 := contains_three_non_collinear_points_sublist (list_inter l m) m HH4 HH6);
rewrite HH8 in HH7;my_rank.
assert(HH2 := matroid3_aux1_cop_bis (p :: l0) a H2);
rewrite <-H1 in *;assert(HH3 := matroid3_aux3_bis_bis (a :: list_inter l m) HH2);
assert(HH4 : inclA eq (list_inter l m) m);
[apply inclA_inter_bis|].
assert(HH5 := matroid3_aux10_aux7 (list_inter l m) a HH3). destruct HH5.
assert(HH6 := matroid3_aux9 (list_inter l m) H3);
assert(HH7 := matroid3_aux9_bis_bis_aux2 m H0);
assert(HH8 := contains_three_non_collinear_points_sublist (list_inter l m) m HH4 HH6);
rewrite HH8 in HH7;my_rank.
assert(HH6 := matroid3_aux9_alt (list_inter l m) H3);
assert(HH7 := matroid3_aux9_bis_bis_aux3 m H0);
assert(HH8 := contains_four_non_coplanar_points_sublist (list_inter l m) m HH4 HH6);
rewrite HH8 in HH7;my_rank.
Qed.

Lemma matroid3_aux24 :
forall l m,
rkl l = 1 ->
rkl m = 1 ->
rkl (l ++ m) + rkl (list_inter l m) <= 2.
Proof.
my_rank;induction l;my_rank.
inversion H.
unfold list_inter;simpl;case_eq(l ++ m);case_eq(Inb a m);my_rank;rewrite list_inter_rewrite.
- assert(HH := matroid3_aux20 l m a H);my_rank.
- assert(HH := matroid3_aux13_bis l m a H);my_rank.
- assert(HH := matroid3_aux1_cop (p :: l0) a H3);rewrite H4 in HH;my_rank.
- assert(HH := matroid3_aux1 (p :: l0) a H5);rewrite H6 in HH;my_rank.
- assert(HH := matroid3_aux10_aux4 l a H);destruct HH.
  + assert(HH0 := rk_nil l H9);rewrite HH0 in H2;simpl in H2;rewrite <-H2 in *.
    assert(HH1 := matroid3_aux9_bis_bis m H0).
    rewrite H8 in HH1;my_rank.
  + assert(HH0 := matroid3_aux10 l a H H9).
    assert(HH1 := Inb_aux1 a m H1).
    assert(HH2 : equivlistA eq (a :: l ++ m) (l ++ m));[my_inA|].
    assert(HH3 := IHl H9);assert(HH4 := list_inter_split_reverse).
    assert(HH5 : equivlistA eq (a :: list_inter l m) (list_inter l m));[my_inA|].
    rewrite HH5;assert(HH6 := matroid3_aux2_col (p :: l0) H8 H6);rewrite <-H2 in HH6;
    my_rank.
- assert(HH := matroid3_aux20 l m a H);my_rank.
- assert(HH := matroid3_aux10_aux4 l a H);destruct HH.
  + assert(HH0 := rk_nil l H8);rewrite HH0 in H2;simpl in H2;rewrite <-H2 in *;
    assert(HH1 := matroid3_aux9_bis_bis m H0);
    assert(HH2 : InA eq p m);[my_inA|];assert(HH3 := Inb_aux1 a m H1).
    assert(HH4 := matroid3_aux9_bis m a p n);
    assert(HH5 : equivlistA eq (a :: p :: m) m);[my_inA|];
    rewrite HH5 in HH4;rewrite HH1 in HH4;my_rank.
  + assert(HH0 := matroid3_aux10 l a H H8);assert(HH1 := Inb_aux1 a m H1);
    assert(HH2 : equivlistA eq (a :: l ++ m) (l ++ m));[my_inA|];
    assert(HH3 := IHl H8);assert(HH4 := list_inter_split_reverse);
    assert(HH5 : equivlistA eq (a :: list_inter l m) (list_inter l m));[my_inA|].
    assert(HH6 := matroid3_aux9_bis l0 a p n);rewrite <-H2 in H6;
    rewrite <-H2 in HH6;rewrite HH2 in HH6;
    assert(HH7 := matroid3_aux2_col (l ++ m) HH6);rewrite HH5;my_rank.
- assert(HH := matroid3_aux10_aux4 l a H);destruct HH.
  + assert(HH0 := rk_nil l H6);rewrite HH0 in H2;simpl in H2;rewrite <-H2 in *;
    assert(HH1 := matroid3_aux9_bis_bis_aux2 m H0);
    assert(HH2 := matroid3_aux1_col_bis m a H5);assert(HH3 := Inb_aux1 a m H1);
    assert(HH4 : equivlistA eq (a :: m) m);[my_inA|];rewrite HH4 in HH2;
    rewrite HH2 in HH1;my_rank.
  + assert(HH0 := matroid3_aux10 l a H H6);assert(HH1 := Inb_aux1 a m H1);
    assert(HH2 : equivlistA eq (a :: l ++ m) (l ++ m));[my_inA|];
    assert(HH3 := IHl H6);assert(HH4 := list_inter_split_reverse);
    assert(HH5 : equivlistA eq (a :: list_inter l m) (list_inter l m));[my_inA|];
    rewrite HH5;assert(HH6 := matroid3_aux1_col_bis (p :: l0) a H5);
    assert(HH7 := matroid3_aux1_cop_bis_bis (p :: l0) a H3);
    rewrite <-H2 in HH6,HH7;assert(HH8 := matroid3_aux2_cop (a :: l ++ m) HH6 HH7);
    assert(HH9 := matroid3_aux9 (a :: l ++ m) HH8);rewrite HH2 in HH8;my_rank.
- assert(HH := matroid3_aux10_aux4 l a H);destruct HH.
  + assert(HH0 := rk_nil l H4);rewrite HH0 in H2;simpl in H2;rewrite <-H2 in *;
    assert(HH1 := matroid3_aux9_bis_bis_aux3 m H0);
    assert(HH2 := matroid3_aux1_cop_bis m a H3);assert(HH3 := Inb_aux1 a m H1);
    assert(HH4 : equivlistA eq (a :: m) m);[my_inA|];rewrite HH4 in HH2;
    rewrite HH2 in HH1;my_rank.
  + assert(HH0 := matroid3_aux10 l a H H4);assert(HH1 := Inb_aux1 a m H1);
    assert(HH2 : equivlistA eq (a :: l ++ m) (l ++ m));[my_inA|];
    assert(HH3 := IHl H4);assert(HH4 := list_inter_split_reverse);
    assert(HH5 : equivlistA eq (a :: list_inter l m) (list_inter l m));[my_inA|];
    rewrite HH5;assert(HH6 := matroid3_aux1_cop_bis (p :: l0) a H3);
    assert(HH7 := matroid3_aux3_bis_bis (a :: p :: l0) HH6);
    rewrite <-H2 in HH7;assert(HH8 := matroid3_aux9_alt (a :: l ++ m) HH7).
    rewrite HH2 in HH7;my_rank.
- assert(HH := matroid3_aux1_cop (p :: l0) a H3);rewrite H4 in HH;my_rank.
- assert(HH := matroid3_aux1 (p :: l0) a H5);rewrite H6 in HH;my_rank.
- assert(HH := matroid3_aux10_aux4 l a H);destruct HH.
  + assert(HH0 := rk_nil l H9);rewrite HH0 in *;my_rank.
  + assert(HH0 := IHl H9);assert(HH1 := matroid3_aux2_col (p :: l0) H8 H6);
    rewrite <-H2 in HH1;my_rank.
- assert(HH := matroid3_aux13_bis l m a H);my_rank.
- assert(HH := matroid3_aux10_aux4 l a H);destruct HH.
  + assert(HH0 := rk_nil l H8);rewrite HH0 in *;my_rank.
  + assert(HH0 := IHl H8);assert(HH1 := matroid3_aux9_bis l0 a p n);
    assert(HH2 := matroid3_aux1_col_bis_bis (p :: l0) a H5);rewrite <-H2 in HH2;
    rewrite <-H2 in HH1;assert(HH3 := matroid3_aux2_col (a :: l ++ m) HH1 HH2);
    assert(HH4 := matroid3_aux10 l a H H8);assert(HH5 : equivlistA eq (a :: l ++ m) (l ++ m));[my_inA|];
   rewrite HH5 in HH3;my_rank.
- assert(HH := matroid3_aux10_aux4 l a H);destruct HH.
  + assert(HH0 := rk_nil l H6);rewrite HH0 in H2;simpl in H2;rewrite <-H2 in *;
    assert(HH1 := matroid3_aux1_col_bis m a H5);assert(HH2 := matroid3_aux1_cop_bis_bis m a H3);
    assert(HH3 := matroid3_aux2_cop (a :: m) HH1 HH2);
    assert(HH4 := matroid3_aux10_aux5 m a HH3);my_rank.
  + assert(HH0 := matroid3_aux10 l a H H6);
    assert(HH2 : equivlistA eq (a :: l ++ m) (l ++ m));[my_inA|];
    assert(HH3 := matroid3_aux1_col_bis (p :: l0) a H5);assert(HH4 := matroid3_aux1_cop_bis_bis (p :: l0) a H3);
    assert(HH5 := matroid3_aux2_cop (a :: p :: l0) HH3 HH4);rewrite <-H2 in HH5;rewrite HH2 in HH5;
    assert(HH6 := IHl H6);my_rank.
- assert(HH := matroid3_aux10_aux4 l a H);destruct HH.
  + assert(HH0 := rk_nil l H4);rewrite HH0 in H2;simpl in H2;rewrite <-H2 in *;
    assert(HH1 := matroid3_aux1_cop_bis m a H3);
    assert(HH3 := matroid3_aux3_bis_bis (a :: m) HH1).
    assert(HH4 := matroid3_aux10_aux7 m a HH3);my_rank.
  + assert(HH0 := matroid3_aux10 l a H H4);
    assert(HH2 : equivlistA eq (a :: l ++ m) (l ++ m));[my_inA|];
    assert(HH3 := matroid3_aux1_cop_bis (p :: l0) a H3);assert(HH4 := matroid3_aux3_bis_bis (a :: p :: l0) HH3).
    rewrite <-H2 in HH4;rewrite HH2 in HH4;
    assert(HH6 := IHl H4);my_rank.
Qed.

Lemma matroid3_aux24_bis :
forall l m,
rkl l = 2 ->
rkl m = 1 ->
rkl (l ++ m) + rkl (list_inter l m) <= 3.
Proof.
my_rank.
assert(HH := list_inter_reverse l m). rewrite HH.
assert(HH0 := list_concat_reverse l m). rewrite HH0.
apply matroid3_aux17;my_rank.
Qed.

Lemma matroid3_aux24_bis_bis :
forall l m,
rkl l = 3 ->
rkl m = 1 ->
rkl (l ++ m) + rkl (list_inter l m) <= 4.
Proof.
my_rank;induction l;my_rank.
inversion H.
unfold list_inter;simpl;case_eq(l ++ m);case_eq(Inb a m);my_rank;rewrite list_inter_rewrite.
- assert(HH := matroid3_aux22 l m a H);my_rank.
- assert(HH := matroid3_aux15 l m a H);my_rank.
- assert(HH := matroid3_aux1_cop (p :: l0) a H3);rewrite H4 in HH;my_rank.
- assert(HH := matroid3_aux1 (p :: l0) a H5);rewrite H6 in HH;my_rank.
- assert(HH := matroid3_aux22 l m a H);my_rank.
- assert(HH := matroid3_aux22 l m a H);my_rank.
- assert(HH := matroid3_aux22 l m a H);my_rank.
- assert(HH := matroid3_aux22 l m a H); progress intuition.
  assert(HH0 : rkl (list_inter (a :: l) m) = 2);
  [unfold list_inter;simpl;case_eq(Inb a m);rewrite list_inter_rewrite;my_rank|]. rewrite H6 in H1;my_rank.
  assert(HH1 : inclA eq (list_inter (a :: l) m) m);[apply inclA_inter_bis|];
  assert(HH2 := matroid3_aux9_bis_bis m H0);assert(HH3 := matroid3_aux9_bis_bis_reverse (list_inter (a :: l) m) HH0);
  assert(HH4 := contains_two_distinct_points_sublist (list_inter (a :: l) m) m HH1 HH3);rewrite HH4 in HH2;my_rank.
- assert(HH := matroid3_aux10_aux5 l a H). destruct HH.
  + assert(HH0 := matroid3_aux24_bis l m H4 H0).
    assert(HH1 := matroid3_aux1_cop_bis (p :: l0) a H3);assert(HH2 := matroid3_aux3_bis_bis (a :: p :: l0) HH1);
    assert(HH3 := Inb_aux1 a m H1);assert(HH4 : equivlistA eq (a :: l ++ m) (l ++ m));[my_inA|];
    rewrite <-H2 in HH2;rewrite HH4 in HH2;my_rank.
  + assert(inclA eq m (a :: l));[my_inA;case_eq(eq_dec_u x a);my_inA|].
    assert(HH := matroid3_aux9_bis m x a n);assert(HH0 := Inb_aux1 a m H1);
    assert(HH1 : equivlistA eq (x :: a :: m) m);[my_inA|];
    rewrite HH1 in HH;assert(HH2 :=  matroid3_aux9_bis_bis m H0);
    rewrite HH2 in HH;my_rank.
    assert(HH := matroid3_aux1_cop_bis (p :: l0) a H3);rewrite <-H2 in HH;
    assert(HH0 := matroid3_aux3_bis_bis (a :: l ++ m) HH);
    assert(HH1 : equivlistA eq (a :: l ++ m) (a :: l));[my_inA;apply InA_cons_tl;apply InA_app_iff;my_inA|];
    rewrite HH1 in HH0;my_rank.    
- assert(HH := matroid3_aux1_cop (p :: l0) a H3);rewrite H4 in HH;my_rank.
- assert(HH := matroid3_aux1 (p :: l0) a H5);rewrite H6 in HH;my_rank.
- assert(HH := matroid3_aux15 l m a H); progress intuition;
  assert(HH0 : inclA eq (list_inter l m) m);[apply inclA_inter_bis|];
  assert(HH1 := matroid3_aux9_bis_bis_aux2 m H0);
  assert(HH2 := matroid3_aux9 (list_inter l m) H9);
  assert(HH3 := contains_three_non_collinear_points_sublist (list_inter l m) m HH0 HH2);
  rewrite HH3 in HH1;my_rank.
- assert(HH := matroid3_aux15 l m a H);my_rank.
- assert(HH := matroid3_aux15 l m a H); progress intuition;  
  assert(HH0 : inclA eq (list_inter l m) m);[apply inclA_inter_bis|];
  assert(HH1 := matroid3_aux9_bis_bis_aux2 m H0);
  assert(HH2 := matroid3_aux9 (list_inter l m) H8);
  assert(HH3 := contains_three_non_collinear_points_sublist (list_inter l m) m HH0 HH2);
  rewrite HH3 in HH1;my_rank.
- assert(HH := matroid3_aux15 l m a H); progress intuition.
  assert(HH0 : inclA eq (list_inter l m) m);[apply inclA_inter_bis|];
  assert(HH1 := matroid3_aux9_bis_bis m H0);
  assert(HH2 := matroid3_aux9_bis_bis_reverse (list_inter l m) H6);
  assert(HH3 := contains_two_distinct_points_sublist (list_inter l m) m HH0 HH2);
  rewrite HH3 in HH1;my_rank.
  assert(HH0 : inclA eq (list_inter l m) m);[apply inclA_inter_bis|];
  assert(HH1 := matroid3_aux9_bis_bis_aux2 m H0);
  assert(HH2 := matroid3_aux9 (list_inter l m) H6);
  assert(HH3 := contains_three_non_collinear_points_sublist (list_inter l m) m HH0 HH2);
  rewrite HH3 in HH1;my_rank.
- assert(HH := matroid3_aux15 l m a H); progress intuition.
  assert(inclA eq m (a :: l)).
  my_inA. apply matroid3_aux17_bis_bis_aux4 in H5.
  apply matroid3_aux17_bis_bis_aux3 in H5.
  destruct H5. case_eq(eq_dec_u x x0).
  my_inA.
  apply list_inter_split_bis in H5;my_inA.
  intros.
  apply list_inter_split_bis in H5;my_inA.
  assert(HH := matroid3_aux9_bis m x x0 n);
  assert(HH1 : equivlistA eq (x :: x0 :: m) m);[my_inA|];
  rewrite HH1 in HH;assert(HH2 :=  matroid3_aux9_bis_bis m H0);
  rewrite HH2 in HH;my_rank.
  assert(HH := matroid3_aux1_cop_bis (p :: l0) a H3);rewrite <-H2 in HH;
  assert(HH0 := matroid3_aux3_bis_bis (a :: l ++ m) HH);
  assert(HH1 : equivlistA eq (a :: l ++ m) (a :: l));[my_inA;apply InA_cons_tl;apply InA_app_iff;my_inA|];
  rewrite HH1 in HH0;my_rank.
  assert(HH0 : inclA eq (list_inter l m) m);[apply inclA_inter_bis|];
  assert(HH1 := matroid3_aux9_bis_bis m H0);
  assert(HH2 := matroid3_aux9_bis_bis_reverse (list_inter l m) H4);
  assert(HH3 := contains_two_distinct_points_sublist (list_inter l m) m HH0 HH2);
  rewrite HH3 in HH1;my_rank.
  assert(HH0 : inclA eq (list_inter l m) m);[apply inclA_inter_bis|];
  assert(HH1 := matroid3_aux9_bis_bis_aux2 m H0);
  assert(HH2 := matroid3_aux9 (list_inter l m) H4);
  assert(HH3 := contains_three_non_collinear_points_sublist (list_inter l m) m HH0 HH2);
  rewrite HH3 in HH1;my_rank. 
Qed.

Lemma matroid3_aux24_bis_bis_bis :
forall l m,
rkl l = 4 ->
rkl m = 1 ->
rkl (l ++ m) + rkl (list_inter l m) <= 5.
Proof.
my_rank;induction l;my_rank.
inversion H.
unfold list_inter;simpl;case_eq(l ++ m);case_eq(Inb a m);my_rank;rewrite list_inter_rewrite.
- assert(HH := matroid3_aux23 l m a H);my_rank.
- assert(HH := matroid3_aux16 l m a H);my_rank.
- assert(HH := matroid3_aux1_cop (p :: l0) a H3);rewrite H4 in HH;my_rank.
- assert(HH := matroid3_aux1 (p :: l0) a H5);rewrite H6 in HH;my_rank.
- assert(HH := matroid3_aux23 l m a H);my_rank.
- assert(HH := matroid3_aux23 l m a H);my_rank.
- assert(HH := matroid3_aux23 l m a H);my_rank.
- assert(HH := matroid3_aux23 l m a H);my_rank.
- assert(HH := matroid3_aux23 l m a H); progress intuition.
  assert(HH0 : inclA eq (a :: list_inter l m) (a :: m));[apply inclA_aux5;apply inclA_inter_bis|].
  assert(HH1 := Inb_aux1 a m H1);assert(HH2 : equivlistA eq (a :: m) m);[my_inA|];rewrite <-HH2 in H0;
  assert(HH3 := matroid3_aux9_bis_bis (a :: m) H0);
  assert(HH4 := matroid3_aux9_bis_bis_reverse (a :: list_inter l m) H5);
  assert(HH5 := contains_two_distinct_points_sublist (a :: list_inter l m) (a :: m) HH0 HH4);
  rewrite HH5 in HH3;my_rank.
- assert(HH := matroid3_aux1_cop (p :: l0) a H3);rewrite H4 in HH;my_rank.
- assert(HH := matroid3_aux1 (p :: l0) a H5);rewrite H6 in HH;my_rank.
- assert(HH := matroid3_aux16 l m a H); progress intuition.
  assert(HH0 : inclA eq (list_inter l m) m);[apply inclA_inter_bis|];
  assert(HH1 := matroid3_aux9_bis_bis_aux3 m H0);
  assert(HH2 := matroid3_aux9_alt (list_inter l m) H10);
  assert(HH3 := contains_four_non_coplanar_points_sublist (list_inter l m) m HH0 HH2);
  rewrite HH3 in HH1;my_rank. 
- assert(HH := matroid3_aux16 l m a H);my_rank.
- assert(HH := matroid3_aux16 l m a H); progress intuition.
  assert(HH0 : inclA eq (list_inter l m) m);[apply inclA_inter_bis|];
  assert(HH1 := matroid3_aux9_bis_bis_aux3 m H0);
  assert(HH2 := matroid3_aux9_alt (list_inter l m) H9);
  assert(HH3 := contains_four_non_coplanar_points_sublist (list_inter l m) m HH0 HH2);
  rewrite HH3 in HH1;my_rank.
- assert(HH := matroid3_aux16 l m a H); progress intuition.
  assert(HH0 : inclA eq (list_inter l m) m);[apply inclA_inter_bis|];
  assert(HH1 := matroid3_aux9_bis_bis_aux2 m H0);
  assert(HH2 := matroid3_aux9 (list_inter l m) H7);
  assert(HH3 := contains_three_non_collinear_points_sublist (list_inter l m) m HH0 HH2);
  rewrite HH3 in HH1;my_rank.
  assert(HH0 : inclA eq (list_inter l m) m);[apply inclA_inter_bis|];
  assert(HH1 := matroid3_aux9_bis_bis_aux3 m H0);
  assert(HH2 := matroid3_aux9_alt (list_inter l m) H7);
  assert(HH3 := contains_four_non_coplanar_points_sublist (list_inter l m) m HH0 HH2);
  rewrite HH3 in HH1;my_rank.
- assert(HH := matroid3_aux16 l m a H); progress intuition.
  assert(HH0 : inclA eq (list_inter l m) m);[apply inclA_inter_bis|];
  assert(HH1 := matroid3_aux9_bis_bis m H0);
  assert(HH2 := matroid3_aux9_bis_bis_reverse (list_inter l m) H4);
  assert(HH3 := contains_two_distinct_points_sublist (list_inter l m) m HH0 HH2);
  rewrite HH3 in HH1;my_rank.
  assert(HH0 : inclA eq (list_inter l m) m);[apply inclA_inter_bis|];
  assert(HH1 := matroid3_aux9_bis_bis_aux2 m H0);
  assert(HH2 := matroid3_aux9 (list_inter l m) H5);
  assert(HH3 := contains_three_non_collinear_points_sublist (list_inter l m) m HH0 HH2);
  rewrite HH3 in HH1;my_rank.
  assert(HH0 : inclA eq (list_inter l m) m);[apply inclA_inter_bis|];
  assert(HH1 := matroid3_aux9_bis_bis_aux3 m H0);
  assert(HH2 := matroid3_aux9_alt (list_inter l m) H5);
  assert(HH3 := contains_four_non_coplanar_points_sublist (list_inter l m) m HH0 HH2);
  rewrite HH3 in HH1;my_rank.
Qed.

Lemma matroid3_aux25  :
forall l m, forall a,
rkl (a :: l) = 1 ->
rkl m = 3 ->
rkl (a :: list_inter l m) = 1 .
Proof.
my_rank;apply matroid3_aux13;my_rank.
Qed.

Lemma matroid3_aux26 :
forall l m, forall a,
rkl (a :: l) = 2 ->
rkl m = 3 ->
rkl (a :: list_inter l m) = 1 \/ rkl (a :: list_inter l m) = 2.
Proof.
my_rank;simpl;
assert(HH : inclA eq (list_inter l m) (a :: l));
[apply inclA_aux4_bis;apply inclA_inter|].
assert(HH0 : inclA eq (a :: list_inter l m) (a :: l));
[apply inclA_aux5;apply inclA_inter|].
case_eq(list_inter l m);my_rank.
assert(HH1 := matroid3_aux1_cop (p :: l0) a H2);rewrite H3 in HH1;inversion HH1.
rewrite <-H1 in *;assert(HH2 := matroid3_aux1 (list_inter l m) a H4);rewrite H5 in HH2;inversion HH2.
assert(HH1 := matroid3_aux1_col_bis (p :: l0) a H4);rewrite <-H1 in *;
assert(HH2 := contains_three_non_collinear_points_sublist (a :: list_inter l m) (a :: l) HH0 HH1);
assert(HH3 := matroid3_aux9_bis_bis_aux (a :: l) H);rewrite HH2 in HH3;my_rank.
assert(HH1 := matroid3_aux1_cop_bis (p :: l0) a H2);rewrite <-H1 in *;
assert(HH2 := contains_four_non_coplanar_points_sublist (a :: list_inter l m) (a :: l) HH0 HH1);
assert(HH3 := matroid3_aux9_bis_bis_alt (a :: l) H);rewrite HH2 in HH3;my_rank.
Qed.

Lemma matroid3_aux27 :
forall l m, forall a,
rkl (a :: l) = 3 ->
rkl m = 3 ->
rkl (a :: list_inter l m) = 1 \/ rkl (a :: list_inter l m) = 2 \/ rkl (a :: list_inter l m) = 3.
Proof.
my_rank;simpl;
assert(HH : inclA eq (list_inter l m) (a :: l));
[apply inclA_aux4_bis;apply inclA_inter|].
assert(HH0 : inclA eq (a :: list_inter l m) (a :: l));
[apply inclA_aux5;apply inclA_inter|].
case_eq(list_inter l m);my_rank.
assert(HH1 := matroid3_aux1_cop (p :: l0) a H2);rewrite H3 in HH1;inversion HH1.
assert(HH1 := matroid3_aux1_cop_bis (p :: l0) a H2);rewrite <-H1 in *;
assert(HH2 := contains_four_non_coplanar_points_sublist (a :: list_inter l m) (a :: l) HH0 HH1);
assert(HH3 := matroid3_aux9_bis_bis_bis (a :: l) H);rewrite HH2 in HH3;my_rank.
Qed.

Lemma matroid3_aux28 :
forall l m, forall a,
rkl (a :: l) = 4 ->
rkl m = 3 ->
rkl (a :: list_inter l m) = 1 \/ rkl (a :: list_inter l m) = 2 \/ rkl (a :: list_inter l m) = 3 \/ rkl (a :: list_inter l m) = 4.
Proof.
my_rank;simpl;case_eq(list_inter l m);my_rank.
Qed.

Lemma matroid3_aux29 :
forall l m,
rkl l = 1 ->
rkl m = 3 ->
rkl (l ++ m) + rkl (list_inter l m) <= 4.
Proof.
my_rank.
assert(HH := list_inter_reverse l m). rewrite HH.
assert(HH0 := list_concat_reverse l m). rewrite HH0.
apply matroid3_aux24_bis_bis;my_rank.
Qed.

Lemma matroid3_aux29_bis :
forall l m,
rkl l = 2 ->
rkl m = 3 ->
rkl (l ++ m) + rkl (list_inter l m) <= 5.
Proof.
my_rank.
assert(HH := list_inter_reverse l m). rewrite HH.
assert(HH0 := list_concat_reverse l m). rewrite HH0.
apply matroid3_aux17_bis_bis;my_rank.
Qed.

Lemma matroid3_aux29_bis_aux1 :
forall l m, forall A B C D,
contains_three_non_collinear_points (list_inter l m) = true ->
contains_three_non_collinear_points l = true ->
contains_three_non_collinear_points m = true ->
contains_four_non_coplanar_points l = false ->
contains_four_non_coplanar_points m = false ->
InA eq A l ->
InA eq B l ->
InA eq C l ->
InA eq D m ->
coplanar A B C D = true /\ coplanar A B D C = true /\
coplanar A C B D = true /\ coplanar A C D B = true /\
coplanar A D B C = true /\ coplanar A D C B = true /\
coplanar B A C D = true /\ coplanar B A D C = true /\
coplanar B C A D = true /\ coplanar B C D A = true /\
coplanar B D A C = true /\ coplanar B D C A = true /\
coplanar C A B D = true /\ coplanar C A D B = true /\
coplanar C B A D = true /\ coplanar C B D A = true /\
coplanar C D A B = true /\ coplanar C D B A = true /\
coplanar D A B C = true /\ coplanar D A C B = true /\
coplanar D B A C = true /\ coplanar D B C A = true /\
coplanar D C A B = true /\ coplanar D C B A = true.
Proof.
intros.
case_eq (eq_dec_u A B).
intros;assert( HH0 := matroid3_aux17_bis_bis_aux5 A B C D e);assumption.
intros.
case_eq (eq_dec_u A C).
intros;assert( HH0 := matroid3_aux17_bis_bis_aux5 A C B D e);my_rank;my_cop2.
intros. 
case_eq (eq_dec_u B C).
intros;assert( HH0 := matroid3_aux17_bis_bis_aux5 B C D A e);my_rank;my_cop2.
intros.
case_eq (eq_dec_u B D).
intros;assert( HH0 := matroid3_aux17_bis_bis_aux5 B D A C e);my_rank;my_cop2.
intros.
case_eq (eq_dec_u A D).
intros;assert( HH0 := matroid3_aux17_bis_bis_aux5 A D B C e);my_rank;my_cop2.
intros.
case_eq (eq_dec_u C D).
intros;assert( HH0 := matroid3_aux17_bis_bis_aux5 C D A B e);my_rank;my_cop2.
intros.
clear H8 H9 H10 H11 H12 H13.
rewrite contains_1 in H.
destruct H;destruct H;destruct H;
destruct H;destruct H8;destruct H9.
assert( HH2 := list_inter_split_bis x l m H).
assert( HH3 := list_inter_split_bis x0 l m H8).
assert( HH4 := list_inter_split_bis x1 l m H9).
destruct HH2,HH3,HH4.
rewrite contains_2_cop in H2.
assert( HH5 : coplanar x x0 x1 A = true).
assert(HH5 := H2 x x0 x1 A);my_rank.
assert( HH6 : coplanar x x0 x1 B = true).
assert(HH6 := H2 x x0 x1 B);my_rank.
assert( HH7 : coplanar x x0 x1 C = true).
assert(HH7 := H2 x x0 x1 C);my_rank.
assert( HH8 : coplanar x x0 A B = true).
assert( HH9 := cop_trans x x0 x1 A B);apply HH9;my_rank.
assert( HH9 : coplanar x x0 B C = true).
assert( HH10 := cop_trans x x0 x1 B C);apply HH10;my_rank.
assert( HH10 : coplanar x x0 A C = true).
assert( HH11 := cop_trans x x0 x1 A C);apply HH11;my_rank.
rewrite contains_2_cop in H3.
assert( HH12 : coplanar x x0 x1 D = true).
assert(HH11 := H3 x x0 x1 D);my_rank.
assert( HH13 : coplanar x x0 A D = true).
assert( HH14 := cop_trans x x0 x1 A D);apply HH14;my_rank.
assert( HH14 : coplanar x x0 B D = true).
assert( HH15 := cop_trans x x0 x1 B D);apply HH15;my_rank.
assert( HH15 : coplanar x x0 C D = true).
assert( HH16 := cop_trans x x0 x1 C D);apply HH16;my_rank.
assert( HH20bis : coplanar x x1 A D = true).
assert( HH16 := cop_trans_bis x x0 x1 A D);apply HH16;my_rank.
assert( HH21bis : coplanar x x1 B D = true).
assert( HH16 := cop_trans_bis x x0 x1 B D);apply HH16;my_rank.
assert( HH22bis : coplanar x x1 C D = true).
assert( HH16 := cop_trans_bis x x0 x1 C D);apply HH16;my_rank.
assert( HH23bis : coplanar x0 x1 A D = true).
assert( HH16 := cop_trans_bis_bis x x0 x1 A D);apply HH16;my_rank.
assert( HH24bis : coplanar x0 x1 B D = true).
assert( HH16 := cop_trans_bis_bis x x0 x1 B D);apply HH16;my_rank.
assert( HH25bis : coplanar x0 x1 C D = true).
assert( HH16 := cop_trans_bis_bis x x0 x1 C D);apply HH16;my_rank.
assert( HH20 : coplanar x x1 B C = true).
assert( HH21 := cop_trans x x1 x0 B C);apply HH21;my_rank.
assert( HH22 := col_exchange x x0 x1);assert( HH23 := col_shift x0 x x1);
rewrite HH23 in HH22;rewrite HH22 in H10;my_rank.
assert( HH21 : coplanar x x1 A B = true).
assert( HH22 := cop_trans x x1 x0 A B);apply HH22;my_rank.
assert( HH23 := col_exchange x x0 x1);assert( HH24 := col_shift x0 x x1);
rewrite HH24 in HH23;rewrite HH23 in H10;my_rank.
assert( HH22 : coplanar x x1 A C = true).
assert( HH23 := cop_trans x x1 x0 A C);apply HH23;my_rank.
assert( HH24 := col_exchange x x0 x1);assert( HH25 := col_shift x0 x x1);
rewrite HH25 in HH24;rewrite HH24 in H10;my_rank.
assert( HH23 : coplanar x0 x1 B C = true).
assert( HH24 := cop_trans x0 x1 x B C);apply HH24;my_rank.
assert( HH25 := col_shift x x0 x1);rewrite HH25 in H10;my_rank.
assert( HH24 : coplanar x0 x1 A B = true).
assert( HH25 := cop_trans x0 x1 x A B);apply HH25;my_rank.
assert( HH26 := col_shift x x0 x1);rewrite HH26 in H10;my_rank.
assert( HH25 : coplanar x0 x1 A C = true).
assert( HH26 := cop_trans x0 x1 x A C);apply HH26;my_rank.
assert( HH27 := col_shift x x0 x1);rewrite HH27 in H10;my_rank.

(* Soit col A B C, soit ~col A B C *)
case_eq (collinear A B C).
intros.
assert( HH0 : coplanar A B C D = true).
unfold coplanar.
case_eq (eq_dec_u A B).
intros.
reflexivity.
case_eq (eq_dec_u C D).
intros.
reflexivity.
intros.
destruct (a1_exist C D).
destruct (a1_exist A B).
simpl.
case_eq (eq_dec_l x3 x2).
intros.
reflexivity.
intros.
case_eq (eq_dec_p x3 x2).
reflexivity.
intros.
generalize H17.
unfold collinear.
case_eq (eq_dec_u A B).
intros.
contradiction.
destruct (a1_exist A B).
simpl.
case_eq (incid_dec C x4).
intros.
destruct a0.
destruct a1.
assert( HH0 := uniqueness A B x3 x4 H25 H26 H27 H28).
destruct HH0.
contradiction.
clear H21.
rewrite H29 in *.
destruct a.
assert( HH0 : Intersect x4 x2).
unfold Intersect.
exists C.
my_rank.
contradiction.
my_rank.
repeat split;my_cop2.

intros.
assert( HH26 := matroid3_aux17_bis_bis_aux6 x x0 x1 A H10).
assert( HH27 := matroid3_aux17_bis_bis_aux6 x x0 x1 B H10).
assert( HH28 := matroid3_aux17_bis_bis_aux6 x x0 x1 C H10).
destruct HH26.
destruct HH27.  
(* 1 - 1 *)    
assert( HH29 := cop_trans_bis_bis x x0 A B C H18 HH8 HH10).
assert( HH30 := cop_trans_bis_bis x x0 A B D H18 HH8 HH13).
assert( HH31 := cop_trans_bis_bis x x0 B C D H19 HH9 HH14).
assert( HH32 := cop_trans_bis_bis x x0 A C D H18 HH10 HH13).
(* 1 - 1 - 1 *)
assert( HH33 := matroid3_aux17_bis_bis_aux6 A B C x0 H17).
destruct HH33.
assert( HH33 := col_exchange A B x0);assert( HH33bis := col_shift B A x0);assert( HH33bisbis := col_exchange A x0 B);
rewrite HH33bisbis in HH33bis;rewrite HH33bis in HH33;rewrite HH33 in H20;assert( HH34 := cop_trans_bis_bis x0 A B C D H20 HH29 HH30).
repeat split;my_cop2.
(* 1 - 1 - 2 *)
destruct H20.
assert( HH29bis := cop_exchange2 x0 A B C);rewrite HH29bis in HH29.
assert( HH33 := col_exchange A C x0);assert( HH33bisbis := col_shift C A x0);assert( HH33bisbisbis := col_exchange A x0 C);
rewrite HH33bisbisbis in HH33bisbis;rewrite HH33bisbis in HH33;rewrite HH33 in H20;assert( HH34 := cop_trans_bis_bis x0 A C B D H20 HH29 HH32).
repeat split;my_cop2.
(* 1 - 1 - 3 *)
assert( HH29bis := cop_exchange3 x0 A B C);assert( HH29bisbis := cop_exchange2 x0 B A C);
rewrite HH29bisbis in HH29bis;rewrite HH29bis in HH29.
assert( HH33 := col_shift B C x0);assert( HH33bis := col_exchange C x0 B);assert( HH33bisbis := col_exchange2 x0 C B);
rewrite HH33bisbis in HH33bis;rewrite HH33bis in HH33;rewrite HH33 in H20;assert( HH34 := cop_trans_bis_bis x0 B C A D H20 HH29 HH31).
repeat split;my_cop2.
(* 1 - 2 *)
destruct H19.
assert( HH29 := cop_trans_bis x x0 A B C H18 HH8 HH10).
assert( HH30 := cop_trans_bis x x0 A B D H18 HH8 HH13).
assert( HH31 := cop_trans_bis x x0 A C D H18 HH10 HH13).
assert( HH21bisbis := cop_exchange2 x x1 A B);rewrite HH21bisbis in HH21.
assert( HH32 := cop_trans_bis x x1 B A C H19 HH21 HH20).
assert( HH33 := cop_trans_bis x x1 B A D H19 HH21 HH21bis).
assert( HH34 := cop_trans_bis x x1 B C D H19 HH20 HH21bis).
(* 1 - 2 - 1 *)
assert( HH35 := matroid3_aux17_bis_bis_aux6 A B C x H17).
destruct HH35.
assert( HH36 := col_shift A B x);assert( HH36bis := col_exchange B x A);assert( HH36bisbis := col_exchange2 x B A);
rewrite HH36bisbis in HH36bis;rewrite HH36bis in HH36;rewrite HH36 in H20;assert( HH37 := cop_trans_bis_bis x A B C D H20 HH29 HH30).
repeat split;my_cop2.
(* 1 - 2 - 2 *)
destruct H20.
assert( HH36 := col_shift A C x);assert( HH36bis := col_exchange C x A);assert( HH36bisbis := col_exchange2 x C A);
rewrite HH36bisbis in HH36bis;rewrite HH36bis in HH36;rewrite HH36 in H20.
assert( HH37 := cop_exchange2 x A B C);rewrite HH37 in HH29;assert( HH38 := cop_trans_bis_bis x A C B D H20 HH29 HH31).
repeat split;my_cop2.
(* 1 - 2 - 3 *)
assert( HH36 := col_shift B C x);assert( HH36bis := col_exchange C x B);assert( HH36bisbis := col_exchange2 x C B).
rewrite HH36bisbis in HH36bis;rewrite HH36bis in HH36;rewrite HH36 in H20.
assert( HH37 := cop_exchange2 x B A C);rewrite HH37 in HH32;assert( HH38 := cop_trans_bis_bis x B C A D H20 HH32 HH34).
repeat split;my_cop2.
(* 1 - 3 *)
assert( HH29 := cop_trans_bis_bis x x0 A B C H18 HH8 HH10).
assert( HH30 := cop_trans_bis_bis x x0 A B D H18 HH8 HH13).
assert( HH31 := cop_trans_bis_bis x x0 A C D H18 HH10 HH13).
assert( HH32bis := cop_exchange2 x0 x1 A B);rewrite HH32bis in HH24.
assert( HH32 := cop_trans_bis x0 x1 B A C H19 HH24 HH23).
assert( HH33 := cop_trans_bis x0 x1 B A D H19 HH24 HH24bis).
assert( HH34 := cop_trans_bis x0 x1 B C D H19 HH23 HH24bis).
(* 1 - 3 - 1 *)
assert( HH35 := matroid3_aux17_bis_bis_aux6 A B C x0 H17).
destruct HH35.
assert( HH36 := col_shift A B x0);assert( HH36bis := col_exchange B x0 A);assert( HH36bisbis := col_exchange2 x0 B A);
rewrite HH36bisbis in HH36bis;rewrite HH36bis in HH36;rewrite HH36 in H20;assert( HH37 := cop_trans_bis_bis x0 A B C D H20 HH29 HH30).
repeat split;my_cop2.
(* 1 - 3 - 2 *)
destruct H20.
assert( HH36 := col_shift A C x0);assert( HH36bis := col_exchange C x0 A);assert( HH36bisbis := col_exchange2 x0 C A);
rewrite HH36bisbis in HH36bis;rewrite HH36bis in HH36;rewrite HH36 in H20.
assert( HH37 := cop_exchange2 x0 A B C);rewrite HH37 in HH29;assert( HH38 := cop_trans_bis_bis x0 A C B D H20 HH29 HH31).
repeat split;my_cop2.
(* 1 - 3 - 3 *)
assert( HH36 := col_shift B C x0);assert( HH36bis := col_exchange C x0 B);assert( HH36bisbis := col_exchange2 x0 C B).
rewrite HH36bisbis in HH36bis;rewrite HH36bis in HH36;rewrite HH36 in H20.
assert( HH37 := cop_exchange2 x0 B A C);rewrite HH37 in HH32;assert( HH38 := cop_trans_bis_bis x0 B C A D H20 HH32 HH34).
repeat split;my_cop2.

destruct H18.
destruct HH27.
(* 2 - 1 *)    
assert( HH29 := cop_trans_bis x x1 A B C H18 HH21 HH22).
assert( HH30 := cop_trans_bis x x1 A B D H18 HH21 HH20bis).
assert( HH31 := cop_trans_bis x x1 A C D H18 HH22 HH20bis).
assert( HH32bis := cop_exchange2 x x0 A B);rewrite HH32bis in HH8.
assert( HH32 := cop_trans_bis x x0 B A C H19 HH8 HH9).
assert( HH33 := cop_trans_bis x x0 B A D H19 HH8 HH14).
assert( HH34 := cop_trans_bis x x0 B C D H19 HH9 HH14).
(* 2 - 1 - 1 *)
assert( HH35 := matroid3_aux17_bis_bis_aux6 A B C x H17).
destruct HH35.
assert( HH35 := col_exchange A B x);assert( HH35bis := col_shift B A x);assert( HH35bisbis := col_exchange A x B);
rewrite HH35bisbis in HH35bis;rewrite HH35bis in HH35;rewrite HH35 in H20;assert( HH36 := cop_trans_bis_bis x A B C D H20 HH29 HH30).
repeat split;my_cop2.
(* 2 - 1 - 2 *)
destruct H20.
assert( HH29bis := cop_exchange2 x A B C);rewrite HH29bis in HH29.
assert( HH35 := col_exchange A C x);assert( HH35bisbis := col_shift C A x);assert( HH35bisbisbis := col_exchange A x C);
rewrite HH35bisbisbis in HH35bisbis;rewrite HH35bisbis in HH35;rewrite HH35 in H20;assert( HH36 := cop_trans_bis_bis x A C B D H20 HH29 HH31).
repeat split;my_cop2.
(* 2 - 1 - 3 *)
assert( HH29bis := cop_exchange3 x A B C);assert( HH29bisbis := cop_exchange2 x B A C);
rewrite HH29bisbis in HH29bis;rewrite HH29bis in HH29.
assert( HH35 := col_shift B C x);assert( HH35bis := col_exchange C x B);assert( HH35bisbis := col_exchange2 x C B);
rewrite HH35bisbis in HH35bis;rewrite HH35bis in HH35;rewrite HH35 in H20;assert( HH36 := cop_trans_bis_bis x B C A D H20 HH29 HH34).
repeat split;my_cop2.
(* 2 - 2 *)
destruct H19.
assert( HH29 := cop_trans_bis x x1 A B C H18 HH21 HH22).
assert( HH30 := cop_trans_bis x x1 A B D H18 HH21 HH20bis).
assert( HH31 := cop_trans_bis x x1 A C D H18 HH22 HH20bis).
assert( HH21bisbis := cop_exchange2 x x1 A B);rewrite HH21bisbis in HH21.
assert( HH32 := cop_trans_bis x x1 B A C H19 HH21 HH20).
assert( HH33 := cop_trans_bis x x1 B A D H19 HH21 HH21bis).
assert( HH34 := cop_trans_bis x x1 B C D H19 HH20 HH21bis).
(* 2 - 2 - 1 *)
assert( HH35 := matroid3_aux17_bis_bis_aux6 A B C x H17).
destruct HH35.
assert( HH36 := col_shift A B x);assert( HH36bis := col_exchange B x A);assert( HH36bisbis := col_exchange2 x B A);
rewrite HH36bisbis in HH36bis;rewrite HH36bis in HH36;rewrite HH36 in H20;assert( HH37 := cop_trans_bis_bis x A B C D H20 HH29 HH30).
repeat split;my_cop2.
(* 2 - 2 - 2 *)
destruct H20.
assert( HH36 := col_shift A C x);assert( HH36bis := col_exchange C x A);assert( HH36bisbis := col_exchange2 x C A);
rewrite HH36bisbis in HH36bis;rewrite HH36bis in HH36;rewrite HH36 in H20.
assert( HH37 := cop_exchange2 x A B C);rewrite HH37 in HH29;assert( HH38 := cop_trans_bis_bis x A C B D H20 HH29 HH31).
repeat split;my_cop2.
(* 2 - 2 - 3 *)
assert( HH36 := col_shift B C x);assert( HH36bis := col_exchange C x B);assert( HH36bisbis := col_exchange2 x C B);
rewrite HH36bisbis in HH36bis;rewrite HH36bis in HH36;rewrite HH36 in H20.
assert( HH37 := cop_exchange2 x B A C);rewrite HH37 in HH32;assert( HH38 := cop_trans_bis_bis x B C A D H20 HH32 HH34).
repeat split;my_cop2.
(* 2 - 3 *)
assert( HH29 := cop_trans_bis_bis x x1 A B C H18 HH21 HH22).
assert( HH30 := cop_trans_bis_bis x x1 A B D H18 HH21 HH20bis).
assert( HH31 := cop_trans_bis_bis x x1 A C D H18 HH22 HH20bis).
assert( HH32bis := cop_exchange2 x0 x1 A B);rewrite HH32bis in HH24.
assert( HH32 := cop_trans_bis_bis x0 x1 B A C H19 HH24 HH23).
assert( HH33 := cop_trans_bis_bis x0 x1 B A D H19 HH24 HH24bis).
assert( HH34 := cop_trans_bis_bis x0 x1 B C D H19 HH23 HH24bis).
(* 2 - 3 - 1 *)
assert( HH35 := matroid3_aux17_bis_bis_aux6 A B C x1 H17).
destruct HH35.
assert( HH36 := col_shift A B x1);assert( HH36bis := col_exchange B x1 A);assert( HH36bisbis := col_exchange2 x1 B A);
rewrite HH36bisbis in HH36bis;rewrite HH36bis in HH36;rewrite HH36 in H20;assert( HH37 := cop_trans_bis_bis x1 A B C D H20 HH29 HH30).
repeat split;my_cop2.
(* 2 - 3 - 2 *)
destruct H20.
assert( HH36 := col_shift A C x1);assert( HH36bis := col_exchange C x1 A);assert( HH36bisbis := col_exchange2 x1 C A);
rewrite HH36bisbis in HH36bis;rewrite HH36bis in HH36;rewrite HH36 in H20.
assert( HH37 := cop_exchange2 x1 A B C);rewrite HH37 in HH29;assert( HH38 := cop_trans_bis_bis x1 A C B D H20 HH29 HH31).
repeat split;my_cop2.
(* 2 - 3 - 3 *)
assert( HH36 := col_shift B C x1);assert( HH36bis := col_exchange C x1 B);assert( HH36bisbis := col_exchange2 x1 C B);
rewrite HH36bisbis in HH36bis;rewrite HH36bis in HH36;rewrite HH36 in H20.
assert( HH37 := cop_exchange2 x1 B A C);rewrite HH37 in HH32;assert( HH38 := cop_trans_bis_bis x1 B C A D H20 HH32 HH34).
repeat split;my_cop2.
destruct HH27.
(* 3 - 1 *)    
assert( HH29 := cop_trans_bis x0 x1 A B C H18 HH24 HH25).
assert( HH30 := cop_trans_bis x0 x1 A B D H18 HH24 HH23bis).
assert( HH31 := cop_trans_bis x0 x1 A C D H18 HH25 HH23bis).
assert( HH32bis := cop_exchange2 x x0 A B);rewrite HH32bis in HH8.
assert( HH32 := cop_trans_bis_bis x x0 B A C H19 HH8 HH9).
assert( HH33 := cop_trans_bis_bis x x0 B A D H19 HH8 HH14).
assert( HH34 := cop_trans_bis_bis x x0 B C D H19 HH9 HH14).
(* 3 - 1 - 1 *)
assert( HH35 := matroid3_aux17_bis_bis_aux6 A B C x0 H17).
destruct HH35.
assert( HH35 := col_exchange A B x0);assert( HH35bis := col_shift B A x0);assert( HH35bisbis := col_exchange A x0 B);
rewrite HH35bisbis in HH35bis;rewrite HH35bis in HH35;rewrite HH35 in H20;assert( HH36 := cop_trans_bis_bis x0 A B C D H20 HH29 HH30).
repeat split;my_cop2.
(* 3 - 1 - 2 *)
destruct H20.
assert( HH29bis := cop_exchange2 x0 A B C);rewrite HH29bis in HH29.
assert( HH35 := col_exchange A C x0);assert( HH35bisbis := col_shift C A x0);assert( HH35bisbisbis := col_exchange A x0 C);
rewrite HH35bisbisbis in HH35bisbis;rewrite HH35bisbis in HH35;rewrite HH35 in H20;assert( HH36 := cop_trans_bis_bis x0 A C B D H20 HH29 HH31).
repeat split;my_cop2.
(* 3 - 1 - 3 *)
assert( HH29bis := cop_exchange3 x0 A B C);assert( HH29bisbis := cop_exchange2 x0 B A C);
rewrite HH29bisbis in HH29bis;rewrite HH29bis in HH29.
assert( HH35 := col_shift B C x0);assert( HH35bis := col_exchange C x0 B);assert( HH35bisbis := col_exchange2 x0 C B);
rewrite HH35bisbis in HH35bis;rewrite HH35bis in HH35;rewrite HH35 in H20;assert( HH36 := cop_trans_bis_bis x0 B C A D H20 HH29 HH34).
repeat split;my_cop2.
(* 3 - 2 *)
destruct H19.
assert( HH29 := cop_trans_bis_bis x0 x1 A B C H18 HH24 HH25).
assert( HH30 := cop_trans_bis_bis x0 x1 A B D H18 HH24 HH23bis).
assert( HH31 := cop_trans_bis_bis x0 x1 A C D H18 HH25 HH23bis).
assert( HH21bisbis := cop_exchange2 x x1 A B);rewrite HH21bisbis in HH21.
assert( HH32 := cop_trans_bis_bis x x1 B A C H19 HH21 HH20).
assert( HH33 := cop_trans_bis_bis x x1 B A D H19 HH21 HH21bis).
assert( HH34 := cop_trans_bis_bis x x1 B C D H19 HH20 HH21bis).
(* 2 - 2 - 1 *)
assert( HH35 := matroid3_aux17_bis_bis_aux6 A B C x1 H17).
destruct HH35.
assert( HH36 := col_shift A B x1);assert( HH36bis := col_exchange B x1 A);assert( HH36bisbis := col_exchange2 x1 B A);
rewrite HH36bisbis in HH36bis;rewrite HH36bis in HH36;rewrite HH36 in H20;assert( HH37 := cop_trans_bis_bis x1 A B C D H20 HH29 HH30).
repeat split;my_cop2.
(* 3 - 2 - 2 *)
destruct H20.
assert( HH36 := col_shift A C x1);assert( HH36bis := col_exchange C x1 A);assert( HH36bisbis := col_exchange2 x1 C A).
rewrite HH36bisbis in HH36bis;rewrite HH36bis in HH36;rewrite HH36 in H20.
assert( HH37 := cop_exchange2 x1 A B C);rewrite HH37 in HH29;assert( HH38 := cop_trans_bis_bis x1 A C B D H20 HH29 HH31).
repeat split;my_cop2.
(* 3 - 2 - 3 *)
assert( HH36 := col_shift B C x1);assert( HH36bis := col_exchange C x1 B);assert( HH36bisbis := col_exchange2 x1 C B);
rewrite HH36bisbis in HH36bis;rewrite HH36bis in HH36;rewrite HH36 in H20.
assert( HH37 := cop_exchange2 x1 B A C);rewrite HH37 in HH32;assert( HH38 := cop_trans_bis_bis x1 B C A D H20 HH32 HH34).
repeat split;my_cop2.
(* 3 - 3 *)
assert( HH29 := cop_trans_bis x0 x1 A B C H18 HH24 HH25).
assert( HH30 := cop_trans_bis x0 x1 A B D H18 HH24 HH23bis).
assert( HH31 := cop_trans_bis x0 x1 A C D H18 HH25 HH23bis).
assert( HH32bis := cop_exchange2 x0 x1 A B);rewrite HH32bis in HH24.
assert( HH32 := cop_trans_bis x0 x1 B A C H19 HH24 HH23).
assert( HH33 := cop_trans_bis x0 x1 B A D H19 HH24 HH24bis).
assert( HH34 := cop_trans_bis x0 x1 B C D H19 HH23 HH24bis).
(* 3 - 3 - 1 *)
assert( HH35 := matroid3_aux17_bis_bis_aux6 A B C x0 H17).
destruct HH35.
assert( HH36 := col_shift A B x0);assert( HH36bis := col_exchange B x0 A);assert( HH36bisbis := col_exchange2 x0 B A).
rewrite HH36bisbis in HH36bis;rewrite HH36bis in HH36;rewrite HH36 in H20;assert( HH37 := cop_trans_bis_bis x0 A B C D H20 HH29 HH30).
repeat split;my_cop2.
(* 3 - 3 - 2 *)
destruct H20.
assert( HH36 := col_shift A C x0);assert( HH36bis := col_exchange C x0 A);assert( HH36bisbis := col_exchange2 x0 C A);
rewrite HH36bisbis in HH36bis;rewrite HH36bis in HH36;rewrite HH36 in H20.
assert( HH37 := cop_exchange2 x0 A B C);rewrite HH37 in HH29;assert( HH38 := cop_trans_bis_bis x0 A C B D H20 HH29 HH31).
repeat split;my_cop2.
(* 3 - 3 - 3 *)
assert( HH36 := col_shift B C x0);assert( HH36bis := col_exchange C x0 B);assert( HH36bisbis := col_exchange2 x0 C B).
rewrite HH36bisbis in HH36bis;rewrite HH36bis in HH36;rewrite HH36 in H20.
assert( HH37 := cop_exchange2 x0 B A C);rewrite HH37 in HH32;assert( HH38 := cop_trans_bis_bis x0 B C A D H20 HH32 HH34).
repeat split;my_cop2.
Qed.

Lemma matroid3_aux29_bis_aux2 :
forall l m, forall A B C D,
contains_three_non_collinear_points (list_inter l m) = true ->
contains_three_non_collinear_points l = true ->
contains_three_non_collinear_points m = true ->
contains_four_non_coplanar_points l = false ->
contains_four_non_coplanar_points m = false ->
InA eq A l ->
InA eq B l ->
InA eq C m ->
InA eq D m ->
coplanar A B C D = true /\ coplanar A B D C = true /\
coplanar A C B D = true /\ coplanar A C D B = true /\
coplanar A D B C = true /\ coplanar A D C B = true /\
coplanar B A C D = true /\ coplanar B A D C = true /\
coplanar B C A D = true /\ coplanar B C D A = true /\
coplanar B D A C = true /\ coplanar B D C A = true /\
coplanar C A B D = true /\ coplanar C A D B = true /\
coplanar C B A D = true /\ coplanar C B D A = true /\
coplanar C D A B = true /\ coplanar C D B A = true /\
coplanar D A B C = true /\ coplanar D A C B = true /\
coplanar D B A C = true /\ coplanar D B C A = true /\
coplanar D C A B = true /\ coplanar D C B A = true.
Proof.
intros.
case_eq (eq_dec_u A B).
intros;assert( HH0 := matroid3_aux17_bis_bis_aux5 A B C D e);assumption.
intros.
case_eq (eq_dec_u A C).
intros;assert( HH0 := matroid3_aux17_bis_bis_aux5 A C B D e);my_rank;my_cop2.
intros. 
case_eq (eq_dec_u B C).
intros;assert( HH0 := matroid3_aux17_bis_bis_aux5 B C D A e);my_rank;my_cop2.
intros.
case_eq (eq_dec_u B D).
intros;assert( HH0 := matroid3_aux17_bis_bis_aux5 B D A C e);my_rank;my_cop2.
intros.
case_eq (eq_dec_u A D).
intros;assert( HH0 := matroid3_aux17_bis_bis_aux5 A D B C e);my_rank;my_cop2.
intros.
case_eq (eq_dec_u C D).
intros;assert( HH0 := matroid3_aux17_bis_bis_aux5 C D A B e);my_rank;my_cop2.
intros.
clear H8 H9 H10 H11 H12 H13.
rewrite contains_1 in H.
destruct H;destruct H;destruct H;
destruct H;destruct H8;destruct H9.
assert( HH2 := list_inter_split_bis x l m H).
assert( HH3 := list_inter_split_bis x0 l m H8).
assert( HH4 := list_inter_split_bis x1 l m H9).
destruct HH2,HH3,HH4.
rewrite contains_2_cop in H2.
rewrite contains_2_cop in H3.
assert( HH5 : coplanar x x0 x1 A = true).
assert(HH5 := H2 x x0 x1 A);my_rank.
assert( HH6 : coplanar x x0 x1 B = true).
assert(HH6 := H2 x x0 x1 B);my_rank.
assert( HH7 : coplanar x x0 x1 C = true).
assert(HH7 := H3 x x0 x1 C);my_rank.
assert( HH8 : coplanar x x0 A B = true).
assert( HH9 := cop_trans x x0 x1 A B);apply HH9;my_rank.
assert( HH9 : coplanar x x0 B C = true).
assert( HH10 := cop_trans x x0 x1 B C);apply HH10;my_rank.
assert( HH10 : coplanar x x0 A C = true).
assert( HH11 := cop_trans x x0 x1 A C);apply HH11;my_rank.
assert( HH12 : coplanar x x0 x1 D = true).
assert(HH11 := H3 x x0 x1 D);my_rank.
assert( HH13 : coplanar x x0 A D = true).
assert( HH14 := cop_trans x x0 x1 A D);apply HH14;my_rank.
assert( HH14 : coplanar x x0 B D = true).
assert( HH15 := cop_trans x x0 x1 B D);apply HH15;my_rank.
assert( HH15 : coplanar x x0 C D = true).
assert( HH16 := cop_trans x x0 x1 C D);apply HH16;my_rank.
assert( HH20bis : coplanar x x1 A D = true).
assert( HH16 := cop_trans_bis x x0 x1 A D);apply HH16;my_rank.
assert( HH21bis : coplanar x x1 B D = true).
assert( HH16 := cop_trans_bis x x0 x1 B D);apply HH16;my_rank.
assert( HH22bis : coplanar x x1 C D = true).
assert( HH16 := cop_trans_bis x x0 x1 C D);apply HH16;my_rank.
assert( HH23bis : coplanar x0 x1 A D = true).
assert( HH16 := cop_trans_bis_bis x x0 x1 A D);apply HH16;my_rank.
assert( HH24bis : coplanar x0 x1 B D = true).
assert( HH16 := cop_trans_bis_bis x x0 x1 B D);apply HH16;my_rank.
assert( HH25bis : coplanar x0 x1 C D = true).
assert( HH16 := cop_trans_bis_bis x x0 x1 C D);apply HH16;my_rank.
assert( HH20 : coplanar x x1 B C = true).
assert( HH21 := cop_trans x x1 x0 B C);apply HH21;my_rank.
assert( HH22 := col_exchange x x0 x1);assert( HH23 := col_shift x0 x x1);
rewrite HH23 in HH22;rewrite HH22 in H10;my_rank.
assert( HH21 : coplanar x x1 A B = true).
assert( HH22 := cop_trans x x1 x0 A B);apply HH22;my_rank.
assert( HH23 := col_exchange x x0 x1);assert( HH24 := col_shift x0 x x1);
rewrite HH24 in HH23;rewrite HH23 in H10;my_rank.
assert( HH22 : coplanar x x1 A C = true).
assert( HH23 := cop_trans x x1 x0 A C);apply HH23;my_rank.
assert( HH24 := col_exchange x x0 x1);assert( HH25 := col_shift x0 x x1);
rewrite HH25 in HH24;rewrite HH24 in H10;my_rank.
assert( HH23 : coplanar x0 x1 B C = true).
assert( HH24 := cop_trans x0 x1 x B C);apply HH24;my_rank.
assert( HH25 := col_shift x x0 x1);rewrite HH25 in H10;my_rank.
assert( HH24 : coplanar x0 x1 A B = true).
assert( HH25 := cop_trans x0 x1 x A B);apply HH25;my_rank.
assert( HH26 := col_shift x x0 x1);rewrite HH26 in H10;my_rank.
assert( HH25 : coplanar x0 x1 A C = true).
assert( HH26 := cop_trans x0 x1 x A C);apply HH26;my_rank.
assert( HH27 := col_shift x x0 x1);rewrite HH27 in H10;my_rank.

(* Soit col A B C, soit ~col A B C *)
case_eq (collinear A B C).
intros.
assert( HH0 : coplanar A B C D = true).
unfold coplanar.
case_eq (eq_dec_u A B).
intros.
reflexivity.
case_eq (eq_dec_u C D).
intros.
reflexivity.
intros.
destruct (a1_exist C D).
destruct (a1_exist A B).
simpl.
case_eq (eq_dec_l x3 x2).
intros.
reflexivity.
intros.
case_eq (eq_dec_p x3 x2).
reflexivity.
intros.
generalize H17.
unfold collinear.
case_eq (eq_dec_u A B).
intros.
contradiction.
destruct (a1_exist A B).
simpl.
case_eq (incid_dec C x4).
intros.
destruct a0.
destruct a1.
assert( HH0 := uniqueness A B x3 x4 H25 H26 H27 H28).
destruct HH0.
contradiction.
clear H21.
rewrite H29 in *.
destruct a.
assert( HH0 : Intersect x4 x2).
unfold Intersect.
exists C.
my_rank.
contradiction.
my_rank.
repeat split;my_cop2.

intros.
assert( HH26 := matroid3_aux17_bis_bis_aux6 x x0 x1 A H10).
assert( HH27 := matroid3_aux17_bis_bis_aux6 x x0 x1 B H10).
assert( HH28 := matroid3_aux17_bis_bis_aux6 x x0 x1 C H10).
destruct HH26.
destruct HH27.  
(* 1 - 1 *)    
assert( HH29 := cop_trans_bis_bis x x0 A B C H18 HH8 HH10).
assert( HH30 := cop_trans_bis_bis x x0 A B D H18 HH8 HH13).
assert( HH31 := cop_trans_bis_bis x x0 B C D H19 HH9 HH14).
assert( HH32 := cop_trans_bis_bis x x0 A C D H18 HH10 HH13).
(* 1 - 1 - 1 *)
assert( HH33 := matroid3_aux17_bis_bis_aux6 A B C x0 H17).
destruct HH33.
assert( HH33 := col_exchange A B x0);assert( HH33bis := col_shift B A x0);assert( HH33bisbis := col_exchange A x0 B);
rewrite HH33bisbis in HH33bis;rewrite HH33bis in HH33;rewrite HH33 in H20;assert( HH34 := cop_trans_bis_bis x0 A B C D H20 HH29 HH30).
repeat split;my_cop2.
(* 1 - 1 - 2 *)
destruct H20.
assert( HH29bis := cop_exchange2 x0 A B C);rewrite HH29bis in HH29.
assert( HH33 := col_exchange A C x0);assert( HH33bisbis := col_shift C A x0);assert( HH33bisbisbis := col_exchange A x0 C);
rewrite HH33bisbisbis in HH33bisbis;rewrite HH33bisbis in HH33;rewrite HH33 in H20;assert( HH34 := cop_trans_bis_bis x0 A C B D H20 HH29 HH32).
repeat split;my_cop2.
(* 1 - 1 - 3 *)
assert( HH29bis := cop_exchange3 x0 A B C);assert( HH29bisbis := cop_exchange2 x0 B A C);
rewrite HH29bisbis in HH29bis;rewrite HH29bis in HH29.
assert( HH33 := col_shift B C x0);assert( HH33bis := col_exchange C x0 B);assert( HH33bisbis := col_exchange2 x0 C B);
rewrite HH33bisbis in HH33bis;rewrite HH33bis in HH33;rewrite HH33 in H20;assert( HH34 := cop_trans_bis_bis x0 B C A D H20 HH29 HH31).
repeat split;my_cop2.
(* 1 - 2 *)
destruct H19.
assert( HH29 := cop_trans_bis x x0 A B C H18 HH8 HH10).
assert( HH30 := cop_trans_bis x x0 A B D H18 HH8 HH13).
assert( HH31 := cop_trans_bis x x0 A C D H18 HH10 HH13).
assert( HH21bisbis := cop_exchange2 x x1 A B);rewrite HH21bisbis in HH21.
assert( HH32 := cop_trans_bis x x1 B A C H19 HH21 HH20).
assert( HH33 := cop_trans_bis x x1 B A D H19 HH21 HH21bis).
assert( HH34 := cop_trans_bis x x1 B C D H19 HH20 HH21bis).
(* 1 - 2 - 1 *)
assert( HH35 := matroid3_aux17_bis_bis_aux6 A B C x H17).
destruct HH35.
assert( HH36 := col_shift A B x);assert( HH36bis := col_exchange B x A);assert( HH36bisbis := col_exchange2 x B A);
rewrite HH36bisbis in HH36bis;rewrite HH36bis in HH36;rewrite HH36 in H20;assert( HH37 := cop_trans_bis_bis x A B C D H20 HH29 HH30).
repeat split;my_cop2.
(* 1 - 2 - 2 *)
destruct H20.
assert( HH36 := col_shift A C x);assert( HH36bis := col_exchange C x A);assert( HH36bisbis := col_exchange2 x C A);
rewrite HH36bisbis in HH36bis;rewrite HH36bis in HH36;rewrite HH36 in H20.
assert( HH37 := cop_exchange2 x A B C);rewrite HH37 in HH29;assert( HH38 := cop_trans_bis_bis x A C B D H20 HH29 HH31).
repeat split;my_cop2.
(* 1 - 2 - 3 *)
assert( HH36 := col_shift B C x);assert( HH36bis := col_exchange C x B);assert( HH36bisbis := col_exchange2 x C B).
rewrite HH36bisbis in HH36bis;rewrite HH36bis in HH36;rewrite HH36 in H20.
assert( HH37 := cop_exchange2 x B A C);rewrite HH37 in HH32;assert( HH38 := cop_trans_bis_bis x B C A D H20 HH32 HH34).
repeat split;my_cop2.
(* 1 - 3 *)
assert( HH29 := cop_trans_bis_bis x x0 A B C H18 HH8 HH10).
assert( HH30 := cop_trans_bis_bis x x0 A B D H18 HH8 HH13).
assert( HH31 := cop_trans_bis_bis x x0 A C D H18 HH10 HH13).
assert( HH32bis := cop_exchange2 x0 x1 A B);rewrite HH32bis in HH24.
assert( HH32 := cop_trans_bis x0 x1 B A C H19 HH24 HH23).
assert( HH33 := cop_trans_bis x0 x1 B A D H19 HH24 HH24bis).
assert( HH34 := cop_trans_bis x0 x1 B C D H19 HH23 HH24bis).
(* 1 - 3 - 1 *)
assert( HH35 := matroid3_aux17_bis_bis_aux6 A B C x0 H17).
destruct HH35.
assert( HH36 := col_shift A B x0);assert( HH36bis := col_exchange B x0 A);assert( HH36bisbis := col_exchange2 x0 B A);
rewrite HH36bisbis in HH36bis;rewrite HH36bis in HH36;rewrite HH36 in H20;assert( HH37 := cop_trans_bis_bis x0 A B C D H20 HH29 HH30).
repeat split;my_cop2.
(* 1 - 3 - 2 *)
destruct H20.
assert( HH36 := col_shift A C x0);assert( HH36bis := col_exchange C x0 A);assert( HH36bisbis := col_exchange2 x0 C A);
rewrite HH36bisbis in HH36bis;rewrite HH36bis in HH36;rewrite HH36 in H20.
assert( HH37 := cop_exchange2 x0 A B C);rewrite HH37 in HH29;assert( HH38 := cop_trans_bis_bis x0 A C B D H20 HH29 HH31).
repeat split;my_cop2.
(* 1 - 3 - 3 *)
assert( HH36 := col_shift B C x0);assert( HH36bis := col_exchange C x0 B);assert( HH36bisbis := col_exchange2 x0 C B).
rewrite HH36bisbis in HH36bis;rewrite HH36bis in HH36;rewrite HH36 in H20.
assert( HH37 := cop_exchange2 x0 B A C);rewrite HH37 in HH32;assert( HH38 := cop_trans_bis_bis x0 B C A D H20 HH32 HH34).
repeat split;my_cop2.

destruct H18.
destruct HH27.
(* 2 - 1 *)    
assert( HH29 := cop_trans_bis x x1 A B C H18 HH21 HH22).
assert( HH30 := cop_trans_bis x x1 A B D H18 HH21 HH20bis).
assert( HH31 := cop_trans_bis x x1 A C D H18 HH22 HH20bis).
assert( HH32bis := cop_exchange2 x x0 A B);rewrite HH32bis in HH8.
assert( HH32 := cop_trans_bis x x0 B A C H19 HH8 HH9).
assert( HH33 := cop_trans_bis x x0 B A D H19 HH8 HH14).
assert( HH34 := cop_trans_bis x x0 B C D H19 HH9 HH14).
(* 2 - 1 - 1 *)
assert( HH35 := matroid3_aux17_bis_bis_aux6 A B C x H17).
destruct HH35.
assert( HH35 := col_exchange A B x);assert( HH35bis := col_shift B A x);assert( HH35bisbis := col_exchange A x B);
rewrite HH35bisbis in HH35bis;rewrite HH35bis in HH35;rewrite HH35 in H20;assert( HH36 := cop_trans_bis_bis x A B C D H20 HH29 HH30).
repeat split;my_cop2.
(* 2 - 1 - 2 *)
destruct H20.
assert( HH29bis := cop_exchange2 x A B C);rewrite HH29bis in HH29.
assert( HH35 := col_exchange A C x);assert( HH35bisbis := col_shift C A x);assert( HH35bisbisbis := col_exchange A x C);
rewrite HH35bisbisbis in HH35bisbis;rewrite HH35bisbis in HH35;rewrite HH35 in H20;assert( HH36 := cop_trans_bis_bis x A C B D H20 HH29 HH31).
repeat split;my_cop2.
(* 2 - 1 - 3 *)
assert( HH29bis := cop_exchange3 x A B C);assert( HH29bisbis := cop_exchange2 x B A C);
rewrite HH29bisbis in HH29bis;rewrite HH29bis in HH29.
assert( HH35 := col_shift B C x);assert( HH35bis := col_exchange C x B);assert( HH35bisbis := col_exchange2 x C B);
rewrite HH35bisbis in HH35bis;rewrite HH35bis in HH35;rewrite HH35 in H20;assert( HH36 := cop_trans_bis_bis x B C A D H20 HH29 HH34).
repeat split;my_cop2.
(* 2 - 2 *)
destruct H19.
assert( HH29 := cop_trans_bis x x1 A B C H18 HH21 HH22).
assert( HH30 := cop_trans_bis x x1 A B D H18 HH21 HH20bis).
assert( HH31 := cop_trans_bis x x1 A C D H18 HH22 HH20bis).
assert( HH21bisbis := cop_exchange2 x x1 A B);rewrite HH21bisbis in HH21.
assert( HH32 := cop_trans_bis x x1 B A C H19 HH21 HH20).
assert( HH33 := cop_trans_bis x x1 B A D H19 HH21 HH21bis).
assert( HH34 := cop_trans_bis x x1 B C D H19 HH20 HH21bis).
(* 2 - 2 - 1 *)
assert( HH35 := matroid3_aux17_bis_bis_aux6 A B C x H17).
destruct HH35.
assert( HH36 := col_shift A B x);assert( HH36bis := col_exchange B x A);assert( HH36bisbis := col_exchange2 x B A);
rewrite HH36bisbis in HH36bis;rewrite HH36bis in HH36;rewrite HH36 in H20;assert( HH37 := cop_trans_bis_bis x A B C D H20 HH29 HH30).
repeat split;my_cop2.
(* 2 - 2 - 2 *)
destruct H20.
assert( HH36 := col_shift A C x);assert( HH36bis := col_exchange C x A);assert( HH36bisbis := col_exchange2 x C A);
rewrite HH36bisbis in HH36bis;rewrite HH36bis in HH36;rewrite HH36 in H20.
assert( HH37 := cop_exchange2 x A B C);rewrite HH37 in HH29;assert( HH38 := cop_trans_bis_bis x A C B D H20 HH29 HH31).
repeat split;my_cop2.
(* 2 - 2 - 3 *)
assert( HH36 := col_shift B C x);assert( HH36bis := col_exchange C x B);assert( HH36bisbis := col_exchange2 x C B);
rewrite HH36bisbis in HH36bis;rewrite HH36bis in HH36;rewrite HH36 in H20.
assert( HH37 := cop_exchange2 x B A C);rewrite HH37 in HH32;assert( HH38 := cop_trans_bis_bis x B C A D H20 HH32 HH34).
repeat split;my_cop2.
(* 2 - 3 *)
assert( HH29 := cop_trans_bis_bis x x1 A B C H18 HH21 HH22).
assert( HH30 := cop_trans_bis_bis x x1 A B D H18 HH21 HH20bis).
assert( HH31 := cop_trans_bis_bis x x1 A C D H18 HH22 HH20bis).
assert( HH32bis := cop_exchange2 x0 x1 A B);rewrite HH32bis in HH24.
assert( HH32 := cop_trans_bis_bis x0 x1 B A C H19 HH24 HH23).
assert( HH33 := cop_trans_bis_bis x0 x1 B A D H19 HH24 HH24bis).
assert( HH34 := cop_trans_bis_bis x0 x1 B C D H19 HH23 HH24bis).
(* 2 - 3 - 1 *)
assert( HH35 := matroid3_aux17_bis_bis_aux6 A B C x1 H17).
destruct HH35.
assert( HH36 := col_shift A B x1);assert( HH36bis := col_exchange B x1 A);assert( HH36bisbis := col_exchange2 x1 B A);
rewrite HH36bisbis in HH36bis;rewrite HH36bis in HH36;rewrite HH36 in H20;assert( HH37 := cop_trans_bis_bis x1 A B C D H20 HH29 HH30).
repeat split;my_cop2.
(* 2 - 3 - 2 *)
destruct H20.
assert( HH36 := col_shift A C x1);assert( HH36bis := col_exchange C x1 A);assert( HH36bisbis := col_exchange2 x1 C A);
rewrite HH36bisbis in HH36bis;rewrite HH36bis in HH36;rewrite HH36 in H20.
assert( HH37 := cop_exchange2 x1 A B C);rewrite HH37 in HH29;assert( HH38 := cop_trans_bis_bis x1 A C B D H20 HH29 HH31).
repeat split;my_cop2.
(* 2 - 3 - 3 *)
assert( HH36 := col_shift B C x1);assert( HH36bis := col_exchange C x1 B);assert( HH36bisbis := col_exchange2 x1 C B);
rewrite HH36bisbis in HH36bis;rewrite HH36bis in HH36;rewrite HH36 in H20.
assert( HH37 := cop_exchange2 x1 B A C);rewrite HH37 in HH32;assert( HH38 := cop_trans_bis_bis x1 B C A D H20 HH32 HH34).
repeat split;my_cop2.
destruct HH27.
(* 3 - 1 *)    
assert( HH29 := cop_trans_bis x0 x1 A B C H18 HH24 HH25).
assert( HH30 := cop_trans_bis x0 x1 A B D H18 HH24 HH23bis).
assert( HH31 := cop_trans_bis x0 x1 A C D H18 HH25 HH23bis).
assert( HH32bis := cop_exchange2 x x0 A B);rewrite HH32bis in HH8.
assert( HH32 := cop_trans_bis_bis x x0 B A C H19 HH8 HH9).
assert( HH33 := cop_trans_bis_bis x x0 B A D H19 HH8 HH14).
assert( HH34 := cop_trans_bis_bis x x0 B C D H19 HH9 HH14).
(* 3 - 1 - 1 *)
assert( HH35 := matroid3_aux17_bis_bis_aux6 A B C x0 H17).
destruct HH35.
assert( HH35 := col_exchange A B x0);assert( HH35bis := col_shift B A x0);assert( HH35bisbis := col_exchange A x0 B);
rewrite HH35bisbis in HH35bis;rewrite HH35bis in HH35;rewrite HH35 in H20;assert( HH36 := cop_trans_bis_bis x0 A B C D H20 HH29 HH30).
repeat split;my_cop2.
(* 3 - 1 - 2 *)
destruct H20.
assert( HH29bis := cop_exchange2 x0 A B C);rewrite HH29bis in HH29.
assert( HH35 := col_exchange A C x0);assert( HH35bisbis := col_shift C A x0);assert( HH35bisbisbis := col_exchange A x0 C);
rewrite HH35bisbisbis in HH35bisbis;rewrite HH35bisbis in HH35;rewrite HH35 in H20;assert( HH36 := cop_trans_bis_bis x0 A C B D H20 HH29 HH31).
repeat split;my_cop2.
(* 3 - 1 - 3 *)
assert( HH29bis := cop_exchange3 x0 A B C);assert( HH29bisbis := cop_exchange2 x0 B A C);
rewrite HH29bisbis in HH29bis;rewrite HH29bis in HH29.
assert( HH35 := col_shift B C x0);assert( HH35bis := col_exchange C x0 B);assert( HH35bisbis := col_exchange2 x0 C B);
rewrite HH35bisbis in HH35bis;rewrite HH35bis in HH35;rewrite HH35 in H20;assert( HH36 := cop_trans_bis_bis x0 B C A D H20 HH29 HH34).
repeat split;my_cop2.
(* 3 - 2 *)
destruct H19.
assert( HH29 := cop_trans_bis_bis x0 x1 A B C H18 HH24 HH25).
assert( HH30 := cop_trans_bis_bis x0 x1 A B D H18 HH24 HH23bis).
assert( HH31 := cop_trans_bis_bis x0 x1 A C D H18 HH25 HH23bis).
assert( HH21bisbis := cop_exchange2 x x1 A B);rewrite HH21bisbis in HH21.
assert( HH32 := cop_trans_bis_bis x x1 B A C H19 HH21 HH20).
assert( HH33 := cop_trans_bis_bis x x1 B A D H19 HH21 HH21bis).
assert( HH34 := cop_trans_bis_bis x x1 B C D H19 HH20 HH21bis).
(* 2 - 2 - 1 *)
assert( HH35 := matroid3_aux17_bis_bis_aux6 A B C x1 H17).
destruct HH35.
assert( HH36 := col_shift A B x1);assert( HH36bis := col_exchange B x1 A);assert( HH36bisbis := col_exchange2 x1 B A);
rewrite HH36bisbis in HH36bis;rewrite HH36bis in HH36;rewrite HH36 in H20;assert( HH37 := cop_trans_bis_bis x1 A B C D H20 HH29 HH30).
repeat split;my_cop2.
(* 3 - 2 - 2 *)
destruct H20.
assert( HH36 := col_shift A C x1);assert( HH36bis := col_exchange C x1 A);assert( HH36bisbis := col_exchange2 x1 C A).
rewrite HH36bisbis in HH36bis;rewrite HH36bis in HH36;rewrite HH36 in H20.
assert( HH37 := cop_exchange2 x1 A B C);rewrite HH37 in HH29;assert( HH38 := cop_trans_bis_bis x1 A C B D H20 HH29 HH31).
repeat split;my_cop2.
(* 3 - 2 - 3 *)
assert( HH36 := col_shift B C x1);assert( HH36bis := col_exchange C x1 B);assert( HH36bisbis := col_exchange2 x1 C B);
rewrite HH36bisbis in HH36bis;rewrite HH36bis in HH36;rewrite HH36 in H20.
assert( HH37 := cop_exchange2 x1 B A C);rewrite HH37 in HH32;assert( HH38 := cop_trans_bis_bis x1 B C A D H20 HH32 HH34).
repeat split;my_cop2.
(* 3 - 3 *)
assert( HH29 := cop_trans_bis x0 x1 A B C H18 HH24 HH25).
assert( HH30 := cop_trans_bis x0 x1 A B D H18 HH24 HH23bis).
assert( HH31 := cop_trans_bis x0 x1 A C D H18 HH25 HH23bis).
assert( HH32bis := cop_exchange2 x0 x1 A B);rewrite HH32bis in HH24.
assert( HH32 := cop_trans_bis x0 x1 B A C H19 HH24 HH23).
assert( HH33 := cop_trans_bis x0 x1 B A D H19 HH24 HH24bis).
assert( HH34 := cop_trans_bis x0 x1 B C D H19 HH23 HH24bis).
(* 3 - 3 - 1 *)
assert( HH35 := matroid3_aux17_bis_bis_aux6 A B C x0 H17).
destruct HH35.
assert( HH36 := col_shift A B x0);assert( HH36bis := col_exchange B x0 A);assert( HH36bisbis := col_exchange2 x0 B A).
rewrite HH36bisbis in HH36bis;rewrite HH36bis in HH36;rewrite HH36 in H20;assert( HH37 := cop_trans_bis_bis x0 A B C D H20 HH29 HH30).
repeat split;my_cop2.
(* 3 - 3 - 2 *)
destruct H20.
assert( HH36 := col_shift A C x0);assert( HH36bis := col_exchange C x0 A);assert( HH36bisbis := col_exchange2 x0 C A);
rewrite HH36bisbis in HH36bis;rewrite HH36bis in HH36;rewrite HH36 in H20.
assert( HH37 := cop_exchange2 x0 A B C);rewrite HH37 in HH29;assert( HH38 := cop_trans_bis_bis x0 A C B D H20 HH29 HH31).
repeat split;my_cop2.
(* 3 - 3 - 3 *)
assert( HH36 := col_shift B C x0);assert( HH36bis := col_exchange C x0 B);assert( HH36bisbis := col_exchange2 x0 C B).
rewrite HH36bisbis in HH36bis;rewrite HH36bis in HH36;rewrite HH36 in H20.
assert( HH37 := cop_exchange2 x0 B A C);rewrite HH37 in HH32;assert( HH38 := cop_trans_bis_bis x0 B C A D H20 HH32 HH34).
repeat split;my_cop2.
Qed.

Lemma matroid3_aux29_bis_bis_aux :
forall l m,
rkl l = 3 ->
rkl m = 3 ->
rkl (list_inter l m) = 3 ->
rkl (l ++ m) = 3.
Proof.
my_rank;
apply matroid3_aux17_bis_bis_aux2;apply matroid3_aux17_bis_bis_aux2 in H;
apply matroid3_aux17_bis_bis_aux2 in H0;apply matroid3_aux17_bis_bis_aux2 in H1.
assert(HH : inclA eq l (l ++ m));[my_inA|];my_rank.
assert( HH0 := contains_three_non_collinear_points_sublist l (l ++ m) HH H);my_rank.
rewrite contains_2_cop;my_rank;assert( HH1 := H1);rewrite (list_inter_reverse l m) in H1.
apply InA_app_iff in H5.
apply InA_app_iff in H6.
apply InA_app_iff in H7.
apply InA_app_iff in H8.
destruct H5;destruct H6;destruct H7;destruct H8.
rewrite contains_2_cop in H4;my_rank. 
apply matroid3_aux29_bis_aux1 with (l:=l) (m:=m) (A:=A) (B:=B) (C:=C) (D:=D);assumption.
apply matroid3_aux29_bis_aux1 with (l:=l) (m:=m) (A:=A) (B:=B) (C:=D) (D:=C);assumption.
apply matroid3_aux29_bis_aux2 with (l:=l) (m:=m) (A:=A) (B:=B) (C:=C) (D:=D);assumption.
apply matroid3_aux29_bis_aux1 with (l:=l) (m:=m) (A:=A) (B:=C) (C:=D) (D:=B);assumption.
apply matroid3_aux29_bis_aux2 with (l:=l) (m:=m) (A:=A) (B:=C) (C:=B) (D:=D);assumption.
apply matroid3_aux29_bis_aux2 with (l:=l) (m:=m) (A:=A) (B:=D) (C:=B) (D:=C);assumption.
apply matroid3_aux29_bis_aux1 with (l:=m) (m:=l) (A:=B) (B:=C) (C:=D) (D:=A);assumption.
apply matroid3_aux29_bis_aux1 with (l:=l) (m:=m) (A:=B) (B:=C) (C:=D) (D:=A);assumption.
apply matroid3_aux29_bis_aux2 with (l:=l) (m:=m) (A:=B) (B:=C) (C:=A) (D:=D);assumption.
apply matroid3_aux29_bis_aux2 with (l:=l) (m:=m) (A:=B) (B:=D) (C:=A) (D:=C);assumption.
apply matroid3_aux29_bis_aux1 with (l:=m) (m:=l) (A:=A) (B:=C) (C:=D) (D:=B);assumption.
apply matroid3_aux29_bis_aux2 with (l:=l) (m:=m) (A:=C) (B:=D) (C:=A) (D:=B);assumption.
apply matroid3_aux29_bis_aux1 with (l:=m) (m:=l) (A:=A) (B:=B) (C:=D) (D:=C);assumption.
apply matroid3_aux29_bis_aux1 with (l:=m) (m:=l) (A:=A) (B:=B) (C:=C) (D:=D);assumption.
rewrite contains_2_cop in H3;my_rank. 
Qed.

Lemma matroid3_aux29_bis_bis :
forall l m,
rkl l = 3 ->
rkl m = 3 ->
rkl (l ++ m) + rkl (list_inter l m) <= 6.
Proof.
my_rank;induction l;my_rank.
inversion H.
unfold list_inter;simpl;case_eq(l ++ m);case_eq(Inb a m);my_rank;rewrite list_inter_rewrite.
- assert(HH := matroid3_aux27 l m a H);my_rank.
- assert(HH := matroid3_aux15 l m a H);my_rank.
- assert(HH := matroid3_aux1_cop (p :: l0) a H3);rewrite H4 in HH;my_rank.
- assert(HH := matroid3_aux1 (p :: l0) a H5);rewrite H6 in HH;my_rank.
- assert(HH := matroid3_aux27 l m a H);my_rank.
- assert(HH := matroid3_aux27 l m a H);my_rank.
- assert(HH := matroid3_aux27 l m a H);my_rank.
- assert(HH := matroid3_aux27 l m a H);my_rank.
- assert(HH := matroid3_aux27 l m a H); progress intuition.
  assert(HH0 := Inb_aux1 a m H1);assert(HH1 : rkl(list_inter (a :: l) m) = 3);
  [unfold list_inter;simpl;case_eq(Inb a m);rewrite list_inter_rewrite;my_rank|]. rewrite H5 in H1;my_rank.
  assert(HH2 := matroid3_aux1_cop_bis (p :: l0) a H3);rewrite <-H2 in HH2;
  assert(HH3 := matroid3_aux3_bis_bis (a :: l ++ m) HH2).
  assert(HH4 := matroid3_aux29_bis_bis_aux (a :: l) m H H0 HH1);
  assert(HH5 : equivlistA eq ((a :: l) ++ m) (a :: l ++ m));[my_inA|];
  rewrite HH5 in HH4;my_rank.
- assert(HH := matroid3_aux1_cop (p :: l0) a H3);rewrite H4 in HH;my_rank.
- assert(HH := matroid3_aux1 (p :: l0) a H5);rewrite H6 in HH;my_rank.
- assert(HH := matroid3_aux15 l m a H);my_rank.
- assert(HH := matroid3_aux15 l m a H);my_rank.
- assert(HH := matroid3_aux15 l m a H);my_rank.
- assert(HH := matroid3_aux15 l m a H);my_rank.
- assert(HH := matroid3_aux15 l m a H); progress intuition.
  assert(HH1 : rkl(list_inter (a :: l) m) = 3);
  [unfold list_inter;simpl;case_eq(Inb a m);rewrite list_inter_rewrite;my_rank|]. rewrite H5 in H1;my_rank.
  assert(HH2 := matroid3_aux1_cop_bis (p :: l0) a H3);rewrite <-H2 in HH2;
  assert(HH3 := matroid3_aux3_bis_bis (a :: l ++ m) HH2).
  assert(HH4 := matroid3_aux29_bis_bis_aux (a :: l) m H H0 HH1);
  assert(HH5 : equivlistA eq ((a :: l) ++ m) (a :: l ++ m));[my_inA|];
  rewrite HH5 in HH4;my_rank.
Qed.

Lemma matroid3_aux29_bis_bis_bis :
forall l m,
rkl l = 4 ->
rkl m = 3 ->
rkl (l ++ m) + rkl (list_inter l m) <= 7.
Proof.
my_rank;induction l;my_rank.
inversion H.
unfold list_inter;simpl;case_eq(l ++ m);case_eq(Inb a m);my_rank;rewrite list_inter_rewrite.
- assert(HH := matroid3_aux28 l m a H);my_rank.
- assert(HH := matroid3_aux16 l m a H);my_rank.
- assert(HH := matroid3_aux1_cop (p :: l0) a H3);rewrite H4 in HH;my_rank.
- assert(HH := matroid3_aux1 (p :: l0) a H5);rewrite H6 in HH;my_rank.
- assert(HH := matroid3_aux28 l m a H);my_rank.
- assert(HH := matroid3_aux28 l m a H);my_rank.
- assert(HH := matroid3_aux28 l m a H);my_rank.
- assert(HH := matroid3_aux28 l m a H);my_rank.
- assert(HH := matroid3_aux28 l m a H);my_rank. progress intuition.
  assert(HH0 : inclA eq (a :: list_inter l m) (a :: m));[apply inclA_aux5;apply inclA_inter_bis|];
  assert(HH1 := matroid3_aux9_bis_bis_bis m H0);
  assert(HH2 := matroid3_aux9_alt (a :: list_inter l m) H5);
  assert(HH3 := contains_four_non_coplanar_points_sublist (a :: list_inter l m) (a :: m) HH0 HH2).
  assert(HH4 := Inb_aux1 a m H1);assert(HH5 : equivlistA eq (a :: m) m);[my_inA|];
  rewrite <-HH5 in H0;assert(HH6 := matroid3_aux9_bis_bis_bis (a :: m) H0);rewrite HH6 in HH3;my_rank.
- assert(HH := matroid3_aux1_cop (p :: l0) a H3);rewrite H4 in HH;my_rank.
- assert(HH := matroid3_aux1 (p :: l0) a H5);rewrite H6 in HH;my_rank.
- assert(HH := matroid3_aux16 l m a H);my_rank.
- assert(HH := matroid3_aux16 l m a H);my_rank.
- assert(HH := matroid3_aux16 l m a H);my_rank.
- assert(HH := matroid3_aux16 l m a H);my_rank.
- assert(HH := matroid3_aux16 l m a H); progress intuition.
  assert(HH0 : inclA eq (list_inter l m) m);[apply inclA_inter_bis|];
  assert(HH1 := matroid3_aux9_bis_bis_bis m H0);
  assert(HH2 := matroid3_aux9_alt (list_inter l m) H5);
  assert(HH3 := contains_four_non_coplanar_points_sublist (list_inter l m) m HH0 HH2);
  rewrite HH3 in HH1;my_rank.
Qed.

Lemma matroid3_aux30 :
forall l m,forall a,
rkl (a :: l) = 1 ->
rkl m = 4 ->
rkl (a :: list_inter l m) = 1.
Proof.
my_rank;apply matroid3_aux13;my_rank.
Qed.

Lemma matroid3_aux31 :
forall l m,forall a,
rkl (a :: l) = 2 ->
rkl m = 4 ->
rkl (a :: list_inter l m) = 1 \/ rkl (a :: list_inter l m) = 2.
Proof.
my_rank;simpl;
assert(HH : inclA eq (list_inter l m) (a :: l));
[apply inclA_aux4_bis;apply inclA_inter|].
assert(HH0 : inclA eq (a :: list_inter l m) (a :: l));
[apply inclA_aux5;apply inclA_inter|].
case_eq(list_inter l m);my_rank.
assert(HH1 := matroid3_aux1_cop (p :: l0) a H2);rewrite H3 in HH1;inversion HH1.
rewrite <-H1 in *;assert(HH2 := matroid3_aux1 (list_inter l m) a H4);rewrite H5 in HH2;inversion HH2.
assert(HH1 := matroid3_aux1_col_bis (p :: l0) a H4);rewrite <-H1 in *;
assert(HH2 := contains_three_non_collinear_points_sublist (a :: list_inter l m) (a :: l) HH0 HH1);
assert(HH3 := matroid3_aux9_bis_bis_aux (a :: l) H);rewrite HH2 in HH3;my_rank.
assert(HH1 := matroid3_aux1_cop_bis (p :: l0) a H2);rewrite <-H1 in *;
assert(HH2 := contains_four_non_coplanar_points_sublist (a :: list_inter l m) (a :: l) HH0 HH1);
assert(HH3 := matroid3_aux9_bis_bis_alt (a :: l) H);rewrite HH2 in HH3;my_rank.
Qed.

Lemma matroid3_aux32 :
forall l m,forall a,
rkl (a :: l) = 3 ->
rkl m = 4 ->
rkl (a :: list_inter l m) = 1 \/ rkl (a :: list_inter l m) = 2 \/ rkl (a :: list_inter l m) = 3.
Proof.
my_rank;simpl;
assert(HH : inclA eq (list_inter l m) (a :: l));
[apply inclA_aux4_bis;apply inclA_inter|].
assert(HH0 : inclA eq (a :: list_inter l m) (a :: l));
[apply inclA_aux5;apply inclA_inter|].
case_eq(list_inter l m);my_rank.
assert(HH1 := matroid3_aux1_cop (p :: l0) a H2);rewrite H3 in HH1;inversion HH1.
assert(HH1 := matroid3_aux1_cop_bis (p :: l0) a H2);rewrite <-H1 in *;
assert(HH2 := contains_four_non_coplanar_points_sublist (a :: list_inter l m) (a :: l) HH0 HH1);
assert(HH3 := matroid3_aux9_bis_bis_bis (a :: l) H);rewrite HH2 in HH3;my_rank.
Qed.

Lemma matroid3_aux33 :
forall l m,forall a,
rkl (a :: l) = 4 ->
rkl m = 4 ->
rkl (a :: list_inter l m) = 1 \/ rkl (a :: list_inter l m) = 2 \/ rkl (a :: list_inter l m) = 3 \/ rkl (a :: list_inter l m) = 4.
Proof.
my_rank;assert( HH0 := all_rank (a :: list_inter l m));destruct HH0.
assert( HH1 := rk_nil (a :: list_inter l m) H1);inversion HH1.
my_rank.
Qed.

Lemma matroid3_aux34 :
forall l m,
rkl l = 1 ->
rkl m = 4 ->
rkl (l ++ m) + rkl (list_inter l m) <= 5.
Proof.
my_rank.
assert(HH := list_inter_reverse l m). rewrite HH.
assert(HH0 := list_concat_reverse l m). rewrite HH0.
apply matroid3_aux24_bis_bis_bis;my_rank.
Qed.

Lemma matroid3_aux34_bis :
forall l m,
rkl l = 2 ->
rkl m = 4 ->
rkl (l ++ m) + rkl (list_inter l m) <= 6.
Proof.
my_rank.
assert(HH := list_inter_reverse l m). rewrite HH.
assert(HH0 := list_concat_reverse l m). rewrite HH0.
apply matroid3_aux17_bis_bis_bis;my_rank.
Qed.

Lemma matroid3_aux34_bis_bis :
forall l m,
rkl l = 3 ->
rkl m = 4 ->
rkl (l ++ m) + rkl (list_inter l m) <= 7.
Proof.
my_rank.
assert(HH := list_inter_reverse l m). rewrite HH.
assert(HH0 := list_concat_reverse l m). rewrite HH0.
apply matroid3_aux29_bis_bis_bis;my_rank.
Qed.

Lemma matroid3_aux34_bis_bis_bis :
forall l m,
rkl l = 4 ->
rkl m = 4 ->
rkl (l ++ m) + rkl (list_inter l m) <= 8.
Proof.
my_rank;induction l;my_rank.
inversion H.
unfold list_inter;simpl;case_eq(l ++ m);case_eq(Inb a m);my_rank;rewrite list_inter_rewrite.
- assert(HH := matroid3_aux33 l m a H);my_rank.
- assert(HH := matroid3_aux16 l m a H);my_rank.
- assert(HH := matroid3_aux1_cop (p :: l0) a H3);rewrite H4 in HH;my_rank.
- assert(HH := matroid3_aux1 (p :: l0) a H5);rewrite H6 in HH;my_rank.
- assert(HH := matroid3_aux33 l m a H);my_rank.
- assert(HH := matroid3_aux33 l m a H);my_rank.
- assert(HH := matroid3_aux33 l m a H);my_rank.
- assert(HH := matroid3_aux33 l m a H);my_rank.
- assert(HH := matroid3_aux33 l m a H);my_rank.
- assert(HH := matroid3_aux1_cop (p :: l0) a H3);rewrite H4 in HH;my_rank.
- assert(HH := matroid3_aux1 (p :: l0) a H5);rewrite H6 in HH;my_rank.
- assert(HH := matroid3_aux16 l m a H);my_rank.
- assert(HH := matroid3_aux16 l m a H);my_rank.
- assert(HH := matroid3_aux16 l m a H);my_rank.
- assert(HH := matroid3_aux16 l m a H);my_rank.
- assert(HH := matroid3_aux16 l m a H);my_rank.
Qed.

Lemma rk_pasch_aux0 : forall a b, ~a[==]b -> 
rkl (a :: a :: b :: nil) = 2 /\ 
rkl (a :: b :: a :: nil) = 2 /\ 
rkl (b :: a :: a :: nil) = 2.
Proof.
my_rank;simpl;my_rank.
- generalize H0;case_eq (collinear a a b);my_rank.
assert(HH0 := col_1 a b);my_rank;rewrite HH0 in H1;my_rank.
assert(HH0 := col_1 a b);rewrite HH0 in H2;my_rank.
- generalize H0;case_eq(coplanar a a b b);my_rank.
assert(HH0 := cop_1 a b b);rewrite HH0 in H1;my_rank.
- generalize H0;case_eq (collinear a b a);my_rank.
assert(HH0 := col_1 a b);my_rank;rewrite col_exchange2 in H1;rewrite HH0 in H1;my_rank.
assert(HH0 := col_1 a b);rewrite col_exchange2 in H2;rewrite HH0 in H2;my_rank.
- generalize H0;case_eq(coplanar a b a a);my_rank.
assert(HH0 := cop_3 a b a);rewrite HH0 in H1;my_rank.
- my_subst;my_rank.
- generalize H0;case_eq (collinear b a a);my_rank.
assert(HH0 := col_2 b a);my_rank;rewrite HH0 in H1;my_rank.
assert(HH0 := col_2 b a);rewrite HH0 in H2;my_rank.
- generalize H0;case_eq(coplanar b a a a);my_rank.
assert(HH0 := cop_3 b a a);rewrite HH0 in H1;my_rank.
Qed.

Lemma rk_pasch_aux1 :
forall a b c, collinear a b c = false ->
~ a[==]b /\ ~ a[==]c /\ ~ b[==]c.
Proof.
intros.
generalize H.
unfold collinear.
case_eq(eq_dec_u a b).
intros.
inversion H1.
destruct(a1_exist a b).
simpl.
case_eq(incid_dec c x).
intros.
inversion H2.
intros.
split.
assumption.
split.
intro.
clear H0.
rewrite <-H3 in n.
destruct a0.
contradiction.
intro.
clear H0.
rewrite <-H3 in n.
destruct a0.
contradiction.
Qed.

Lemma rk_pasch_aux2 :
forall a b c d,
coplanar a b c d = true -> 
collinear a b c = false ->
exists e, rkl (a :: b :: e :: nil) = 2 /\ rkl (c :: d :: e :: nil) = 2.
Proof.
intros.
generalize H0.
unfold collinear.
case_eq(eq_dec_u a b).
intros.
inversion H2.
destruct(a1_exist a b).
intros.
simpl in H2.
generalize H2.
case_eq(incid_dec c x).
intros.
inversion H4.
intros.
generalize H.
unfold coplanar.
case_eq(eq_dec_u a b).
intros.
contradiction.
case_eq(eq_dec_u c d).
intros.
rewrite <-e.
exists a.
split.
apply rk_pasch_aux0;my_rank.
assert(HH := rk_pasch_aux1 a b c H0).
my_rank.
unfold rkl.
case_eq(contains_four_non_coplanar_points (c :: c :: a :: nil)).
intros.
generalize H13.
simpl.
case_eq(coplanar c c a a).
intros.
inversion H15.
intros.
assert(HH := cop_1 c a a).
rewrite HH in H14;inversion H14.
intros.
case_eq(contains_three_non_collinear_points (c :: c :: a :: nil)).
intros.
generalize H14.
simpl.
case_eq(collinear c c a).
intros.
inversion H16.
intros.
assert(HH := col_1 c a).
rewrite HH in H15;inversion H15.
intros.
case_eq(contains_two_distinct_points (c :: c :: a :: nil)).
intros.
reflexivity.
intros.
generalize H15.
simpl.
case_eq(eq_dec_u c c).
case_eq(eq_dec_u c a).
intros.
rewrite e0 in H9.
apply False_ind.
apply H9.
reflexivity.
intros.
inversion H18.
intros.
inversion H17.
destruct (a1_exist a b).
destruct (a1_exist c d).
intros.
simpl in H7.
generalize H7.
case_eq(eq_dec_l x0 x1).
intros.
rewrite e in *.
destruct a0;destruct a1.
assert(HH := uniqueness a b x x1 H10 H11 H12 H13).
destruct HH. 
contradiction.
rewrite <-H14 in *.
destruct a2.
contradiction.
case_eq(eq_dec_p x0 x1).
intros.
unfold Intersect in i.
destruct i.
exists x2.
destruct a3.
simpl.
case_eq(coplanar a b x2 x2).
case_eq(collinear a b x2).
case_eq(eq_dec_u a b).
intros.
contradiction.
intros.
split.
reflexivity.
case_eq(coplanar c d x2 x2).
case_eq(collinear c d x2).
case_eq(eq_dec_u c d).
intros.
contradiction.
reflexivity.
intros.
generalize H14.
unfold collinear.
case_eq(eq_dec_u c d).
intros.
contradiction.
destruct(a1_exist c d);simpl.
case_eq(incid_dec x2 x3).
intros.
inversion H18.
intros.
destruct a2,a3.
assert(HH := uniqueness c d x1 x3 H19 H20 H21 H22).
destruct HH.
contradiction.
clear H8.
rewrite H23 in i0.
contradiction.
intros.
assert(HH := cop_3 c d x2).
rewrite H14 in HH;my_rank.
intros.
generalize H11.
unfold collinear.
case_eq(eq_dec_u a b).
intros.
contradiction.
destruct(a1_exist a b).
simpl.
case_eq(incid_dec x2 x3).
intros.
inversion H15.
intros.
destruct a1,a3.
assert(HH := uniqueness a b x0 x3 H16 H17 H18 H19).
destruct HH.
contradiction.
clear H8.
rewrite H20 in i.
contradiction.
intros.
assert(HH := cop_3 a b x2).
rewrite HH in H11.
inversion H11.
intros.
inversion H10.
Qed.

Lemma rk_pasch_aux3 : 
forall a b c,
~ a[==]b -> 
collinear a b c = true ->
rkl (a :: b :: c :: nil) = 2.
Proof.
intros.
simpl.
case_eq(coplanar a b c c).
case_eq(collinear a b c).
case_eq(eq_dec_u a b).
case_eq(eq_dec_u b c).
intros.
contradiction.
reflexivity.
reflexivity.
intros.
rewrite H0 in H1;inversion H1.
intros.
assert(HH := cop_3 a b c).
rewrite H1 in HH.
inversion HH.
Qed.

Lemma list_cardinal_aux0 : forall l,
rkl l = 0 -> cardinal l = 0.
Proof.
intros.
induction l.
simpl.
reflexivity.
simpl.
generalize H.
simpl.
case_eq l.
intros.
inversion H1.
intro.
intro.
case_eq (if coplanar_with_all a (all_triples (p :: l0))
    then contains_four_non_coplanar_points (p :: l0)
    else true).
intros.
inversion H2.
case_eq (if collinear_with_all a (all_pairs (p :: l0))
    then contains_three_non_collinear_points (p :: l0)
    else true).
intros.
inversion H3.
case_eq (if eq_dec_u a p then contains_two_distinct_points (p :: l0) else true).
intros.
inversion H4.
intros.
inversion H4.
Qed.

Lemma list_cardinal_aux1 : forall l,
rkl l = 1 -> cardinal l >= 1.
Proof.
intros.
induction l.
inversion H.
assert(HH := matroid3_aux10_aux4 l a H).
destruct HH.
assert(HH := rk_nil l H0).
rewrite HH;my_rank.
assert(HH := IHl H0).
simpl.
solve [intuition].
Qed.

Lemma list_cardinal_aux2 : forall l,
rkl l = 2 -> cardinal l >=2.
Proof.
intros.
induction l.
inversion H.
assert(HH := matroid3_aux10_aux6 l a H).
destruct HH.
assert(HH := list_cardinal_aux1 l H0).
simpl.
solve [intuition].
assert(HH := IHl H0).
simpl.
solve [intuition].
Qed.

Lemma list_cardinal_aux3 : forall l,
rkl l = 3 -> cardinal l >=3.
Proof.
intros.
induction l.
inversion H.
assert(HH := matroid3_aux10_aux5 l a H).
destruct HH.
assert(HH := list_cardinal_aux2 l H0).
simpl.
solve [intuition].
assert(HH := IHl H0).
simpl.
solve [intuition].
Qed.

Lemma list_cardinal_aux4 : forall l,
rkl l = 4 -> cardinal l >=4.
Proof.
intros.
induction l.
inversion H.
assert(HH := matroid3_aux10_aux7 l a H).
destruct HH.
assert(HH := list_cardinal_aux3 l H0).
simpl.
solve [intuition].
assert(HH := IHl H0).
simpl.
solve [intuition].
Qed.

End s_psohEquivCRk_2.