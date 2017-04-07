Require Export ProjectiveGeometry.Dev.p_equiv_c3p.

(*****************************************************************************)
(** Rkl **)


Section s_pEquivRk_1.

Context `{PSLEU : ProjectiveStructureLEU}.
Context `{EP : EqDecidability Point}.
Context `{OP : OrderedType Point}.

(*** Definition rkl ***)
Definition rkl  l := match l with
| nil => 0
| x :: nil => 1
| l => if contains_three_non_collinear_points l then 3 else
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
(* 5 *)
intros l _x m Hm _y n Hl Hl1 Hl2.
intros y; elim y using rkl_ind.
intros; subst.
assert (T: InA eq _x (_x :: _y :: n)).
solve [intuition].
destruct (H _x) as [Hx1 Hx2].
generalize (Hx1 T); intros Hinv; inversion Hinv.
intros; subst.
solve [trivial].
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
Qed.

End s_pEquivRk_1.


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


Section s_pEquivRk_2.

Context `{PSLEU : ProjectiveStructureLEU}.
Context `{EP : EqDecidability Point}.
Context `{OP : OrderedType Point}.

Lemma all_rank : forall l, rkl l = 0 \/ rkl l = 1 \/ rkl l = 2 \/ rkl l = 3.
Proof.
my_rank;unfold rkl;case_eq l;my_rank.
Qed.

Lemma matroid1': rkl nil = 0.
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

Lemma rank_max_3 : forall e, rkl(e) <= 3.
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
forall l, forall a,
rkl (a :: a :: l) = rkl (a :: l).
Proof.
my_rank.
apply rank_morph.
my_inA.
Qed.

Lemma rk_decr_reverse :
forall l, forall a,
rkl (a :: l) = rkl (a :: a :: l).
Proof.
my_rank.
apply rank_morph.
my_inA.
Qed.

Lemma matroid3_aux1_bis :
forall l,forall a,
collinear_with_all a (all_pairs l) = false ->
contains_three_non_collinear_points (a :: l) = true.
Proof.
my_rank;induction l;simpl;my_rank.
inversion H;rewrite H0 in H3;my_rank.
Qed.

Lemma matroid3_aux1_bis_bis : forall l, forall a,
collinear_with_all a (all_pairs (l)) = true ->
contains_three_non_collinear_points (a :: l) = false.
Proof.
my_rank;induction l;simpl;my_rank.
assert(HH := matroid3_aux1 l a0 H1);my_rank.
assert(HH := matroid3_aux0_bis l a a0 H);rewrite H1 in HH;my_rank.
inversion H;rewrite H2 in H0;my_rank.
Qed.

Lemma matroid3_aux2 : 
forall l,
contains_two_distinct_points l = true ->
contains_three_non_collinear_points l = false ->
rkl l = 2.
Proof.
my_rank;induction l;simpl;my_rank.
inversion H.
rewrite H1 in H;inversion H.
assert (HH := matroid3_aux1 (p::l0) a H2);rewrite H3 in HH;my_rank.
assert(inclA eq (p::l) (p::l0));my_inA;assert (HH := contains_two_distinct_points_sublist (p :: p :: l0) (p::l0) H6 H);rewrite H5 in HH;my_rank.
subst; assert (HH := matroid3_aux1_bis (p :: l0) a H2);rewrite HH in H0;my_rank.
Qed.

Lemma matroid3_aux2_bis :
forall l,
contains_three_non_collinear_points l = true ->
contains_two_distinct_points l = true.
Proof.
my_rank;induction l;simpl;my_rank;case_eq l;my_rank.
subst;inversion H.
subst;apply IHl;my_subst;rewrite <-H;apply contains_three_morph;my_inA.
Qed.

Lemma matroid3_aux2_bis_bis :
forall l,
contains_two_distinct_points l = false ->
contains_three_non_collinear_points l = false.
Proof.
my_rank;induction l;my_rank;simpl;my_rank.
assert( HH := matroid3_aux1 l a H0);my_rank.
assert( HH := matroid3_aux1_bis l a H0);assert ( HH0 := matroid3_aux2_bis (a::l) HH);rewrite HH0 in H;my_rank.
Qed.

Lemma matroid3_aux3 : 
forall l,
contains_two_distinct_points l = false ->
rkl l = 0 \/ rkl l = 1.
Proof.
my_rank;case_eq l;my_rank.
unfold rkl;case_eq l0;my_rank.
subst;assert(HH := matroid3_aux2_bis_bis (p :: p0 :: l1) H);rewrite H2 in HH;my_rank.
subst;rewrite H in H3;my_rank.
Qed.

Lemma matroid3_aux3_bis :
forall l, l <> nil ->
rkl(l) = 1 \/ rkl(l) = 2 \/ rkl(l) = 3.
Proof.
my_rank;case_eq l;my_rank.
unfold rkl;case_eq l0;my_rank.
Qed.

Lemma matroid3_aux9 :
forall l,
contains_three_non_collinear_points l = true->
rkl l = 3.
Proof.
my_rank;unfold rkl;case_eq l;my_rank.
subst;inversion H.
subst;inversion H.
subst;rewrite H2 in H;my_rank.
subst;rewrite H2 in H;my_rank.
Qed.

Lemma matroid3_aux9_reverse :
forall l,
rkl l = 3 ->
contains_three_non_collinear_points l = true.
Proof.
unfold rkl;intros l;case_eq l. my_rank.
intros p l0;case_eq l0;my_rank.
generalize H1;case_eq (contains_three_non_collinear_points (p :: p0 :: l1));case_eq(contains_two_distinct_points (p :: p0 :: l1));my_rank.
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
generalize H1;case_eq (contains_three_non_collinear_points (p :: p0 :: l1));case_eq(contains_two_distinct_points (p :: p0 :: l1));my_rank;inversion H4.
Qed.

Lemma matroid3_aux9_bis_bis_alt :
forall l,
rkl l = 1 ->
contains_three_non_collinear_points l = false.
Proof.
unfold rkl;intros l;case_eq l. my_rank.
intros p l0;case_eq l0;my_rank.
generalize H1;case_eq (contains_three_non_collinear_points (p :: p0 :: l1));case_eq(contains_two_distinct_points (p :: p0 :: l1));my_rank;inversion H4.
Qed.

Lemma matroid3_aux9_bis_bis_reverse :
forall l,
rkl l = 2 ->
contains_two_distinct_points l = true.
Proof.
unfold rkl;intros l;case_eq l. my_rank.
intros p l0;case_eq l0;my_rank.
generalize H1;case_eq (contains_three_non_collinear_points (p :: p0 :: l1));case_eq(contains_two_distinct_points (p :: p0 :: l1));my_rank.
Qed.

Lemma matroid3_aux9_bis_bis_aux :
forall l,
rkl l = 2 ->
contains_three_non_collinear_points l = false.
Proof.
unfold rkl;intros l;case_eq l. my_rank.
intros p l0;case_eq l0;my_rank.
generalize H1;case_eq (contains_three_non_collinear_points (p :: p0 :: l1));case_eq(contains_two_distinct_points (p :: p0 :: l1));my_rank;inversion H4.
Qed.

Lemma matroid3_aux10 :
forall l, forall a,
rkl (a :: l) = 1 ->
rkl l = 1 ->
InA eq a l.
Proof.
my_rank;generalize H;unfold rkl;case_eq l;my_rank;subst;[inversion H0|].
generalize H2;case_eq(contains_three_non_collinear_points (a :: p :: l0));case_eq(contains_two_distinct_points(a :: p :: l0));my_rank;inversion H4.
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
my_rank;induction l;my_rank.
simpl;case_eq l;my_rank;subst;generalize H;simpl;[case_eq(eq_dec_u a a0)|];my_rank.
assert(HH0 : equivlistA eq (a :: p :: p :: l0) (a :: p :: l0));[my_inA|];
my_subst;assert(HH := matroid3_aux3 (p :: l0) H4);rewrite HH0 in H;my_rank.
Qed.

Lemma matroid3_aux10_aux6 :
forall l, forall a,
rkl (a :: l) = 2 ->
rkl l = 1 \/ rkl l = 2.
Proof.
my_rank;induction l;my_rank;simpl;case_eq l;my_rank;subst.
assert(HH := matroid3_aux1 (p :: l0) a0 H1);rewrite H2 in HH;my_rank.
subst;assert(HH0 := matroid3_aux1_bis (p :: l0) a0 H1);assert(HH1 : inclA eq (a0 :: p :: l0)(a :: a0 :: p :: l0));[my_inA|];
assert(HH2 := matroid3_aux9_bis_bis_aux (a :: a0 :: p :: l0) H);
assert(HH3 := contains_three_non_collinear_points_sublist (a0 :: p :: l0) (a :: a0 :: p :: l0) HH1 HH0);rewrite HH3 in HH2;inversion HH2.
Qed.

Lemma matroid3_aux10_bis :
forall l m,
rkl m = 1 ->
rkl (list_inter l m) = 0 \/ rkl(list_inter l m) = 1.
Proof.
my_rank;induction l;my_rank.
unfold list_inter;simpl;case_eq(Inb a m);my_rank;simpl;case_eq(list_inter l m);my_rank;rewrite list_inter_rewrite in H2.
rewrite H2 in H1;inversion H1.
rewrite H2 in H1;inversion H1.
rewrite H2 in H1;inversion H1.
rewrite H2 in H1;inversion H1.
assert(HH := matroid3_aux1 (p0 :: l1) a H3);rewrite H4 in HH;my_rank.
subst;assert(HH := matroid3_aux2 (p0 :: l1) H6 H4);rewrite <-H2 in HH;my_rank.
assert(HH := Inb_aux1 a m H0);assert(HH0 : equivlistA eq (a :: m) m);[my_inA|];rewrite <-HH0 in *;
assert(HH1 := matroid3_aux9_bis l1 a p0 n);
assert(HH2 : inclA eq (a :: list_inter l m) (a :: m));[apply inclA_aux5;apply inclA_inter_bis|];rewrite <-H2 in *;
assert(HH3 := contains_two_distinct_points_sublist (a :: list_inter l m) (a :: m) HH2 HH1);
assert(HH4 := matroid3_aux9_bis_bis (a :: m) H);rewrite HH4 in HH3;my_rank.
assert(HH1 := matroid3_aux1_bis (p0 :: l1) a H3);
assert(HH := Inb_aux1 a m H0);assert(HH0 : equivlistA eq (a :: m) m);[my_inA|];rewrite <-HH0 in *;
assert(HH2 : inclA eq (a :: list_inter l m) (a :: m));[apply inclA_aux5;apply inclA_inter_bis|];rewrite <-H2 in *;
assert(HH3 := contains_three_non_collinear_points_sublist (a :: list_inter l m) (a :: m) HH2 HH1);
assert(HH4 := matroid3_aux9_bis_bis_alt (a :: m) H);rewrite HH4 in HH3;my_rank.
Qed.

Lemma matroid3_aux11 :
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

assert(HH2 := matroid3_aux1 (list_inter l m) a H1);rewrite H2 in HH2;inversion HH2.
assert(HH2 := contains_two_distinct_points_sublist (list_inter l m) (a :: l) HH H4);
assert(HH3 := matroid3_aux9_bis_bis (a :: l) H);rewrite HH2 in HH3;my_rank.
assert(HH2 := matroid3_aux9_bis l0 a p n);rewrite <-H0 in HH2;
assert(HH3 := contains_two_distinct_points_sublist (a :: list_inter l m) (a :: l) HH0 HH2);
assert(HH4 := matroid3_aux9_bis_bis (a :: l) H);rewrite HH3 in HH4;my_rank.
assert(HH2 := matroid3_aux1_bis (list_inter l m) a H1);
assert(HH3 := contains_three_non_collinear_points_sublist (a :: list_inter l m) (a :: l) HH0 HH2);
assert(HH4 := matroid3_aux9_bis_bis_alt (a :: l) H);rewrite HH3 in HH4;my_rank.
Qed.

Lemma matroid3_aux11_bis :
forall l m, forall a,
rkl (a :: l) = 1 ->
rkl (list_inter l m) = 0 \/ rkl(list_inter l m) = 1.
Proof.
my_rank;unfold rkl;
assert(HH : inclA eq (list_inter l m) (a :: l));
[apply inclA_aux4_bis;apply inclA_inter|].
assert(HH0 : inclA eq (a :: list_inter l m) (a :: l));
[apply inclA_aux5;apply inclA_inter|].
case_eq(list_inter l m);my_rank.
subst;rewrite <-H0 in *;assert(HH1 := contains_three_non_collinear_points_sublist (list_inter l m) (a :: l) HH H2);
assert(HH2 := matroid3_aux9_bis_bis_alt (a :: l) H);rewrite HH1 in HH2;my_rank.
subst;rewrite <-H0 in *;assert(HH1 := contains_two_distinct_points_sublist (list_inter l m) (a :: l) HH H3);
assert(HH2 := matroid3_aux9_bis_bis (a :: l) H);rewrite HH1 in HH2;my_rank.
Qed.

Lemma matroid3_aux12 :
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
subst;rewrite <-H0 in *;assert(HH1 := contains_three_non_collinear_points_sublist (list_inter l m) (a :: l) HH H2);
assert(HH2 := matroid3_aux9_bis_bis_aux (a :: l) H);rewrite HH1 in HH2;my_rank.
Qed.

Lemma matroid3_aux12_bis :
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
assert(HH1 := matroid3_aux1 (p :: l0) a H2);rewrite H3 in HH1;inversion HH1.
assert(HH1 := matroid3_aux1_bis (p :: l0) a H2);rewrite <-H1 in *;
assert(HH2 := contains_three_non_collinear_points_sublist (a :: list_inter l m) (a :: l) HH0 HH1);
assert(HH3 := matroid3_aux9_bis_bis_aux (a :: l) H);rewrite HH2 in HH3;my_rank.
Qed.

Lemma matroid3_aux13 :
forall l m, forall a,
rkl (a :: l) = 3 ->
rkl (list_inter l m) = 0 \/ rkl (list_inter l m) = 1 \/ rkl(list_inter l m) = 2 \/ rkl(list_inter l m) =3.
Proof.
my_rank;unfold rkl;case_eq(list_inter l m);my_rank.
Qed.

Lemma matroid3_aux13_bis :
forall l m, forall a,
rkl (a :: l) = 3 ->
rkl m = 2 ->
rkl (a :: list_inter l m) = 1 \/ rkl (a :: list_inter l m) =2 \/ rkl (a :: list_inter l m) = 3.
Proof.
my_rank;simpl;case_eq(list_inter l m);my_rank.
Qed.

Lemma matroid3_aux14 :
forall l m,
rkl l = 1 ->
rkl m = 2 ->
rkl (l ++ m) + rkl (list_inter l m) <= 3.
Proof.
my_rank;induction l;my_rank.
inversion H.
unfold list_inter;simpl;case_eq(l ++ m);case_eq(Inb a m);my_rank;rewrite list_inter_rewrite.
- assert(HH := matroid3_aux11 l m a H);my_rank.
- assert(HH := matroid3_aux11_bis l m a H);my_rank.
- assert(HH := matroid3_aux1 (p :: l0) a H3);rewrite H4 in HH;my_rank.
- assert(HH := matroid3_aux11 l m a H);my_rank.
- assert(HH := matroid3_aux11 l m a H);my_rank.
- assert(HH := matroid3_aux11 l m a H);my_rank.
- assert(HH := matroid3_aux1_bis (p :: l0) a H3);assert(HH0 := matroid3_aux9 (a :: p :: l0) HH);
  assert(HH1 := matroid3_aux10_aux4 l a H);assert(HH2 := Inb_aux1 a m H1);destruct HH1.
  + assert(HH3 := rk_nil l H4); rewrite HH3 in H2; simpl in H2;rewrite <-H2 in HH0;
    assert(HH4: equivlistA eq (a :: m) m);[my_inA|];
    rewrite HH4 in HH0;rewrite H0 in HH0;my_rank.
  + assert(HH3 := matroid3_aux10 l a H H4); assert(HH4 : equivlistA eq (a :: l ++ m) (l ++ m));[my_inA|];
    assert(HH5 := IHl H4);rewrite <-H2 in HH0;rewrite HH4 in HH0;rewrite <-HH0 in HH5;
    assert(HH6 := list_inter_split_reverse a l m HH2 HH3);
    assert(HH7 : equivlistA eq (a :: list_inter l m) (list_inter l m));[my_inA|];
    rewrite HH7;my_rank.
- assert(HH := matroid3_aux1 (p :: l0) a H3);rewrite H4 in HH;my_rank.
- assert(HH := matroid3_aux11_bis l m a H);my_rank.
- assert(HH := matroid3_aux11_bis l m a H);my_rank.
- assert(HH := matroid3_aux11_bis l m a H);my_rank.
- assert(HH := matroid3_aux1_bis (p :: l0) a H3);assert(HH0 := matroid3_aux9 (a :: p :: l0) HH);
  rewrite <-H2 in HH0;assert(HH1 := matroid3_aux10_aux4 l a H);destruct HH1.
  + assert(HH3 := rk_nil l H4);rewrite HH3;my_rank.
  + assert(HH3 := matroid3_aux10 l a H H4);
    assert(HH4: equivlistA eq (a :: l ++ m) (l ++ m));[my_inA|].
    assert(HH5 := IHl H4);rewrite HH4 in HH0;rewrite HH0 in HH5;my_rank.
Qed.

Lemma matroid3_aux14_bis_aux1 :
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

Lemma matroid3_aux14_bis_aux2 :
forall l,
rkl l = 2 <-> contains_two_distinct_points l = true /\ contains_three_non_collinear_points l = false.
Proof.
my_rank.
apply matroid3_aux9_bis_bis_reverse;my_rank.
apply matroid3_aux9_bis_bis_aux;my_rank.
apply matroid3_aux2;my_rank.
Qed.

Lemma matroid3_aux14_bis_aux3 :
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
my_rank;apply matroid3_aux14_bis_aux1 in H0;destruct H0;destruct H0;my_rank;
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

Lemma matroid3_aux14_bis_aux :
forall l m,
rkl l = 2 ->
rkl m = 2 ->
rkl (list_inter l m) = 2 ->
rkl (l ++ m) = 2.
Proof.
my_rank;
apply matroid3_aux14_bis_aux2;apply matroid3_aux14_bis_aux2 in H;
apply matroid3_aux14_bis_aux2 in H0;apply matroid3_aux14_bis_aux2 in H1;
assert(HH : inclA eq l (l ++ m));[my_inA|];my_rank;
assert( HH0 := contains_two_distinct_points_sublist l (l ++ m) HH H);my_rank.
rewrite contains_2;my_rank;assert( HH1 := H1);rewrite (list_inter_reverse l m) in H1.
apply InA_app_iff in H5.
apply InA_app_iff in H6.
apply InA_app_iff in H7.
destruct H5;destruct H6;destruct H7.
rewrite contains_2 in H4;my_rank.
apply matroid3_aux14_bis_aux3 with (l:=l) (m:=m) (A:=A) (B:=B) (C:=C);assumption.
apply matroid3_aux14_bis_aux3 with (l:=l) (m:=m) (A:=A) (B:=C) (C:=B);assumption.
apply matroid3_aux14_bis_aux3 with (l:=m) (m:=l) (A:=B) (B:=C) (C:=A);assumption.
apply matroid3_aux14_bis_aux3 with (l:=l) (m:=m) (A:=B) (B:=C) (C:=A);assumption.
apply matroid3_aux14_bis_aux3 with (l:=m) (m:=l) (A:=A) (B:=C) (C:=B);assumption.
apply matroid3_aux14_bis_aux3 with (l:=m) (m:=l) (A:=A) (B:=B) (C:=C);assumption.
rewrite contains_2 in H3;my_rank.
Qed.

Lemma matroid3_aux14_bis :
forall l m,
rkl l = 2 ->
rkl m = 2 ->
rkl (l ++ m) + rkl (list_inter l m) <= 4.
Proof.
my_rank;induction l;my_rank.
inversion H.
unfold list_inter;simpl;case_eq(l ++ m);case_eq(Inb a m);my_rank;rewrite list_inter_rewrite.
- assert(HH := matroid3_aux12_bis l m a H);my_rank.
- assert(HH := matroid3_aux12 l m a H);my_rank.
- assert(HH := matroid3_aux1 (p :: l0) a H3);rewrite H4 in HH;my_rank.
- assert(HH := matroid3_aux12_bis l m a H);my_rank.
- assert(HH := matroid3_aux12_bis l m a H);my_rank.
- assert(HH := matroid3_aux12_bis l m a H);my_rank.
- assert(HH := matroid3_aux1_bis (p :: l0) a H3);assert(HH0 := matroid3_aux9 (a :: p :: l0) HH);
  assert(HH1 := matroid3_aux12_bis l m a H H0);destruct HH1. rewrite H4; solve[intuition].
  assert(HH2 : rkl(list_inter (a :: l) m) = 2);[unfold list_inter;simpl;rewrite list_inter_rewrite in *|];case_eq(Inb a m);
  my_rank;rewrite H1 in *;my_rank;
  assert(HH3 := matroid3_aux14_bis_aux (a::l) m H H0 HH2);
  simpl in HH3;rewrite <-H2 in HH0;simpl in HH0;rewrite HH0 in HH3;my_rank.
- assert(HH := matroid3_aux1 (p :: l0) a H3);rewrite H4 in HH;my_rank.
- assert(HH := matroid3_aux12 l m a H);my_rank.
- assert(HH := matroid3_aux12 l m a H);my_rank.
- assert(HH := matroid3_aux12 l m a H);my_rank.
- assert(HH := matroid3_aux12 l m a H);my_rank;
  assert(HH1 := matroid3_aux1_bis (p :: l0) a H3);assert(HH2 := matroid3_aux9 (a :: p :: l0) HH1).
  destruct HH. rewrite H4;solve[intuition].
  destruct H4. rewrite H4;solve[intuition].
  assert(HH3 : rkl(list_inter (a :: l) m) = 2);[unfold list_inter;simpl;rewrite list_inter_rewrite in *|];case_eq(Inb a m);
  my_rank;rewrite H5 in *;my_rank.
  assert(HH4 := matroid3_aux14_bis_aux (a::l) m H H0 HH3).
  simpl in HH4;rewrite <-H2 in HH2;simpl in HH2;rewrite HH2 in HH4;my_rank.
Qed.

Lemma matroid3_aux14_bis_bis :
forall l m,
rkl l = 3 ->
rkl m = 2 ->
rkl (l ++ m) + rkl (list_inter l m) <= 5.
Proof.
my_rank;induction l;my_rank.
inversion H.
unfold list_inter;simpl;case_eq(l ++ m);case_eq(Inb a m);my_rank;rewrite list_inter_rewrite.
- assert(HH := matroid3_aux13_bis l m a H);my_rank.
- assert(HH := matroid3_aux13 l m a H);my_rank.
- assert(HH := matroid3_aux1 (p :: l0) a H3);rewrite H4 in HH;my_rank.
- assert(HH := matroid3_aux13_bis l m a H);my_rank.
- assert(HH := matroid3_aux13_bis l m a H);my_rank.
- assert(HH := matroid3_aux13_bis l m a H);my_rank.
- assert(HH := matroid3_aux13_bis l m a H H0);my_rank.
  destruct HH. rewrite H4;solve[intuition].
  destruct H4. rewrite H4;solve[intuition].
  assert(HH0 := Inb_aux1 a m H1);assert(HH : equivlistA eq (a :: m) m);[my_inA|];
  rewrite <-HH in H0;assert(HH1 : inclA eq (a :: list_inter l m) (a :: m));[apply inclA_aux5;apply inclA_inter_bis|];
  assert(HH2 := matroid3_aux9_reverse (a :: list_inter l m) H4);
  assert(HH3 := matroid3_aux9_bis_bis_aux (a :: m) H0);
  assert(HH4 := contains_three_non_collinear_points_sublist (a :: list_inter l m) (a :: m) HH1 HH2);
  rewrite HH4 in HH3;my_rank.
- assert(HH := matroid3_aux1 (p :: l0) a H3);rewrite H4 in HH;my_rank.
- assert(HH := matroid3_aux13 l m a H);my_rank.
- assert(HH := matroid3_aux13 l m a H);my_rank.
- assert(HH := matroid3_aux13 l m a H);my_rank.
- assert(HH := matroid3_aux13 l m a H);my_rank.
  destruct HH. rewrite H4;solve[intuition].
  destruct H4. rewrite H4;solve[intuition].
  destruct H4. rewrite H4;solve[intuition].
  assert(HH1 : inclA eq (list_inter l m) m);[apply inclA_inter_bis|];
  assert(HH2 := matroid3_aux9_reverse (list_inter l m) H4);
  assert(HH3 := matroid3_aux9_bis_bis_aux m H0);
  assert(HH4 := contains_three_non_collinear_points_sublist (list_inter l m) m HH1 HH2);
  rewrite HH4 in HH3;my_rank.
Qed.

Lemma matroid3_aux17 :
forall l m, forall a,
rkl (a :: l) = 1 ->
rkl m = 1 ->
rkl (a :: list_inter l m) = 1.
Proof.
my_rank;apply matroid3_aux11;my_rank.
Qed.

Lemma matroid3_aux18 :
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
assert(HH1 := matroid3_aux1 (p :: l0) a H2);rewrite H3 in HH1;inversion HH1.
assert(HH1 := matroid3_aux1_bis (p :: l0) a H2);rewrite <-H1 in *;
assert(HH2 := contains_three_non_collinear_points_sublist (a :: list_inter l m) (a :: l) HH0 HH1);
assert(HH3 := matroid3_aux9_bis_bis_aux (a :: l) H);rewrite HH2 in HH3;my_rank.
Qed.

Lemma matroid3_aux19 :
forall l m, forall a,
rkl (a :: l) = 3 ->
rkl m = 1 ->
rkl (a :: list_inter l m) = 1 \/ rkl (a :: list_inter l m) = 2.
Proof.
my_rank;simpl;case_eq(list_inter l m);my_rank.
assert(HH0 := matroid3_aux1 (p :: l0) a H2);rewrite H3 in HH0;my_rank.
assert(HH1 := matroid3_aux10_bis l m H0);
assert(HH2 := matroid3_aux1_bis (p :: l0) a H2);rewrite <-H1 in *;
assert(HH4 := matroid3_aux9 (a :: list_inter l m) HH2);
assert(HH5 := matroid3_aux10_aux5 (list_inter l m) a HH4);my_rank.
Qed.

Lemma matroid3_aux20 :
forall l m,
rkl l = 1 ->
rkl m = 1 ->
rkl (l ++ m) + rkl (list_inter l m) <= 2.
Proof.
my_rank;induction l;my_rank.
inversion H.
unfold list_inter;simpl;case_eq(l ++ m);case_eq(Inb a m);my_rank;rewrite list_inter_rewrite.
- assert(HH := matroid3_aux17 l m a H);my_rank.
- assert(HH := matroid3_aux11_bis l m a H);my_rank.
- assert(HH := matroid3_aux1 (p :: l0) a H3);rewrite H4 in HH;my_rank.
- assert(HH := matroid3_aux10_aux4 l a H);destruct HH.
  + assert(HH0 := rk_nil l H7);rewrite HH0 in H2;simpl in H2;rewrite <-H2 in *.
    assert(HH1 := matroid3_aux9_bis_bis m H0).
    rewrite H6 in HH1;my_rank.
  + assert(HH0 := matroid3_aux10 l a H H7).
    assert(HH1 := Inb_aux1 a m H1).
    assert(HH2 : equivlistA eq (a :: l ++ m) (l ++ m));[my_inA|].
    assert(HH3 := IHl H7);assert(HH4 := list_inter_split_reverse).
    assert(HH5 : equivlistA eq (a :: list_inter l m) (list_inter l m));[my_inA|].
    rewrite HH5;assert(HH6 := matroid3_aux2 (p :: l0) H6 H4);rewrite <-H2 in HH6;
    my_rank.
- assert(HH := matroid3_aux11 l m a H);my_rank.
- assert(HH := matroid3_aux10_aux4 l a H);destruct HH.
  + assert(HH0 := rk_nil l H6);rewrite HH0 in H2;simpl in H2;rewrite <-H2 in *;
    assert(HH1 := matroid3_aux9_bis_bis m H0);
    assert(HH2 : InA eq p m);[my_inA|];assert(HH3 := Inb_aux1 a m H1).
    assert(HH4 := matroid3_aux9_bis m a p n);
    assert(HH5 : equivlistA eq (a :: p :: m) m);[my_inA|];
    rewrite HH5 in HH4;rewrite HH1 in HH4;my_rank.
  + assert(HH0 := matroid3_aux10 l a H H6);assert(HH1 := Inb_aux1 a m H1);
    assert(HH2 : equivlistA eq (a :: l ++ m) (l ++ m));[my_inA|];
    assert(HH3 := IHl H6);assert(HH4 := list_inter_split_reverse);
    assert(HH5 : equivlistA eq (a :: list_inter l m) (list_inter l m));[my_inA|];
    assert(HH6 := matroid3_aux9_bis l0 a p n);rewrite <-H2 in H4;
    rewrite <-H2 in HH6;rewrite HH2 in HH6;
    assert(HH7 := matroid3_aux2 (l ++ m) HH6);rewrite HH5;my_rank.
- assert(HH := matroid3_aux10_aux4 l a H);destruct HH.
  + assert(HH0 := rk_nil l H4);rewrite HH0 in H2;simpl in H2;rewrite <-H2 in *;
    assert(HH1 := matroid3_aux9_bis_bis_alt m H0);
    assert(HH2 := matroid3_aux1_bis m a H3);assert(HH3 := Inb_aux1 a m H1);
    assert(HH4 : equivlistA eq (a :: m) m);[my_inA|];rewrite HH4 in HH2;
    rewrite HH2 in HH1;my_rank.
  + assert(HH0 := matroid3_aux10 l a H H4);assert(HH1 := Inb_aux1 a m H1);
    assert(HH2 : equivlistA eq (a :: l ++ m) (l ++ m));[my_inA|];
    assert(HH3 := IHl H4);assert(HH4 := list_inter_split_reverse);
    assert(HH5 : equivlistA eq (a :: list_inter l m) (list_inter l m));[my_inA|];
    rewrite HH5;assert(HH6 := matroid3_aux1_bis (p :: l0) a H3);rewrite <-H2 in HH6;
    assert(HH7 := matroid3_aux9 (a :: l ++ m) HH6);rewrite HH2 in HH7;my_rank.
- assert(HH := matroid3_aux1 (p :: l0) a H3);rewrite H4 in HH;my_rank.
- assert(HH := matroid3_aux10_aux4 l a H);destruct HH.
  + assert(HH0 := rk_nil l H7);rewrite HH0 in *;my_rank.
  + assert(HH0 := IHl H7);assert(HH1 := matroid3_aux2 (p :: l0) H6 H4);
    rewrite <-H2 in HH1;my_rank.
- assert(HH := matroid3_aux11_bis l m a H);my_rank.
- assert(HH := matroid3_aux10_aux4 l a H);destruct HH.
  + assert(HH0 := rk_nil l H6);rewrite HH0 in *;my_rank.
  + assert(HH0 := IHl H6);assert(HH1 := matroid3_aux9_bis l0 a p n);
    assert(HH2 := matroid3_aux1_bis_bis (p :: l0) a H3);rewrite <-H2 in HH2;
    rewrite <-H2 in HH1;assert(HH3 := matroid3_aux2 (a :: l ++ m) HH1 HH2);
    assert(HH4 := matroid3_aux10 l a H H6);assert(HH5 : equivlistA eq (a :: l ++ m) (l ++ m));[my_inA|];
   rewrite HH5 in HH3;my_rank.
- assert(HH := matroid3_aux10_aux4 l a H);destruct HH.
  + assert(HH0 := rk_nil l H4);rewrite HH0 in H2;simpl in H2;rewrite <-H2 in *.
    assert(HH1 := matroid3_aux1_bis m a H3);assert(HH2 := matroid3_aux9 (a :: m) HH1);
    assert(HH3 := matroid3_aux10_aux5 m a HH2);my_rank.
  + assert(HH0 := matroid3_aux10 l a H H4);
    assert(HH2 : equivlistA eq (a :: l ++ m) (l ++ m));[my_inA|].
    assert(HH3 := matroid3_aux1_bis (p :: l0) a H3);rewrite <-H2 in HH3;
    assert(HH4 := matroid3_aux9 (a :: l ++ m) HH3);rewrite HH2 in HH4;
    assert(HH5 := IHl H4);my_rank.
Qed.

Lemma matroid3_aux20_bis :
forall l m,
rkl l = 2 ->
rkl m = 1 ->
rkl (l ++ m) + rkl (list_inter l m) <= 3.
Proof.
my_rank.
assert(HH := list_inter_reverse l m). rewrite HH.
assert(HH0 := list_concat_reverse l m). rewrite HH0.
apply matroid3_aux14;my_rank.
Qed.

Lemma matroid3_aux20_bis_bis :
forall l m,
rkl l = 3 ->
rkl m = 1 ->
rkl (l ++ m) + rkl (list_inter l m) <= 4.
Proof.
my_rank;induction l;my_rank.
inversion H.
unfold list_inter;simpl;case_eq(l ++ m);case_eq(Inb a m);my_rank;rewrite list_inter_rewrite.
- assert(HH := matroid3_aux19 l m a H);my_rank.
- assert(HH := matroid3_aux13 l m a H);my_rank.
- assert(HH := matroid3_aux1 (p :: l0) a H3);rewrite H4 in HH;my_rank.
- assert(HH := matroid3_aux19 l m a H);my_rank.
- assert(HH := matroid3_aux19 l m a H);my_rank.
- assert(HH := matroid3_aux19 l m a H);my_rank.
- assert(HH0 := Inb_aux1 a m H1);
  assert(HH1 : equivlistA eq (a :: m) m);[my_inA|];
  rewrite <-HH1 in H0;
  assert(HH2 := matroid3_aux11 m l a H0);
  assert(HH3 := list_inter_reverse l m);
  rewrite HH3;my_rank.
- assert(HH := matroid3_aux10_bis l m H0);my_rank.
- assert(HH := matroid3_aux10_bis l m H0);my_rank.
- assert(HH := matroid3_aux10_bis l m H0);my_rank.
- assert(HH := matroid3_aux10_bis l m H0);my_rank.
- assert(HH := matroid3_aux10_bis l m H0);my_rank.
Qed.

Lemma matroid3_aux23 :
forall l m, forall a,
rkl (a :: l) = 1 ->
rkl m = 3 ->
rkl (a :: list_inter l m) = 1 .
Proof.
my_rank;simpl;
assert(HH : inclA eq (list_inter l m) (a :: l));
[apply inclA_aux4_bis;apply inclA_inter|].
assert(HH0 : inclA eq (a :: list_inter l m) (a :: l));
[apply inclA_aux5;apply inclA_inter|].
case_eq(list_inter l m);my_rank.
assert(HH1 := matroid3_aux1 (p :: l0) a H2);rewrite H3 in HH1;inversion HH1.
rewrite <-H1 in H3,H5;
assert(HH1 := contains_two_distinct_points_sublist (list_inter l m) (a :: l) HH H5);
assert(HH2 := matroid3_aux9_bis_bis (a :: l) H);rewrite HH1 in HH2;my_rank.
assert(HH1 := matroid3_aux9_bis l0 a p n);rewrite <-H1 in HH1;
assert(HH2 := contains_two_distinct_points_sublist (a :: list_inter l m) (a :: l) HH0 HH1);
assert(HH3 := matroid3_aux9_bis_bis (a :: l) H);rewrite HH2 in HH3;my_rank.
assert(HH1 := matroid3_aux1_bis (p :: l0) a H2);rewrite <-H1 in *;
assert(HH2 := contains_three_non_collinear_points_sublist (a :: list_inter l m) (a :: l) HH0 HH1);
assert(HH3 := matroid3_aux9_bis_bis_alt (a :: l) H);rewrite HH2 in HH3;my_rank.
Qed.

Lemma matroid3_aux24 :
forall l m, forall a,
rkl (a :: l) = 2 ->
rkl m = 3 ->
rkl (a :: list_inter l m) = 1 \/ rkl (a :: list_inter l m) = 2.
Proof.
my_rank;simpl;
assert(HH0 : inclA eq (a :: list_inter l m) (a :: l));
[apply inclA_aux5;apply inclA_inter|].
case_eq(list_inter l m);my_rank.
assert(HH1 := matroid3_aux1 (p :: l0) a H2);rewrite H3 in HH1;inversion HH1.
assert(HH1 := matroid3_aux1_bis (p :: l0) a H2);rewrite <-H1 in *;
assert(HH2 := contains_three_non_collinear_points_sublist (a :: list_inter l m) (a :: l) HH0 HH1);
assert(HH3 := matroid3_aux9_bis_bis_aux (a :: l) H);rewrite HH2 in HH3;my_rank.
Qed.

Lemma matroid3_aux25 :
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
Qed.

Lemma matroid3_aux26 :
forall l m,
rkl l = 1 ->
rkl m = 3 ->
rkl (l ++ m) + rkl (list_inter l m) <= 4.
Proof.
my_rank.
assert(HH := list_inter_reverse l m). rewrite HH.
assert(HH0 := list_concat_reverse l m). rewrite HH0.
apply matroid3_aux20_bis_bis;my_rank.
Qed.

Lemma matroid3_aux26_bis :
forall l m,
rkl l = 2 ->
rkl m = 3 ->
rkl (l ++ m) + rkl (list_inter l m) <= 5.
Proof.
my_rank.
assert(HH := list_inter_reverse l m). rewrite HH.
assert(HH0 := list_concat_reverse l m). rewrite HH0.
apply matroid3_aux14_bis_bis;my_rank.
Qed.

Lemma matroid3_aux26_bis_bis :
forall l m,
rkl l = 3 ->
rkl m = 3 ->
rkl (l ++ m) + rkl (list_inter l m) <= 6.
Proof.
my_rank;induction l;my_rank.
inversion H.
unfold list_inter;simpl;case_eq(l ++ m);case_eq(Inb a m);my_rank;rewrite list_inter_rewrite.
- assert(HH := matroid3_aux25 l m a H);my_rank.
- assert(HH := matroid3_aux13 l m a H);my_rank.
- assert(HH := matroid3_aux1 (p :: l0) a H3);rewrite H4 in HH;my_rank.
- assert(HH := matroid3_aux25 l m a H);my_rank.
- assert(HH := matroid3_aux25 l m a H);my_rank.
- assert(HH := matroid3_aux25 l m a H);my_rank.
- assert(HH := matroid3_aux25 l m a H);my_rank.
- assert(HH := matroid3_aux13 l m a H);my_rank.
- assert(HH := matroid3_aux13 l m a H);my_rank.
- assert(HH := matroid3_aux13 l m a H);my_rank.
- assert(HH := matroid3_aux13 l m a H);my_rank.
- assert(HH := matroid3_aux13 l m a H);my_rank.
Qed.

Lemma rk_inter_aux0 : forall a b, ~a[==]b -> 
rkl (a :: a :: b :: nil) = 2 /\ 
rkl (a :: b :: a :: nil) = 2 /\ 
rkl (b :: a :: a :: nil) = 2.
Proof.
my_rank;simpl;my_rank.
- generalize H0;case_eq (collinear a a b);my_rank.
assert(HH0 := col_1 a b);my_rank;rewrite HH0 in H1;my_rank.
- generalize H0;case_eq (collinear a b a);my_rank.
assert(HH0 := col_1 a b);my_rank;rewrite col_exchange2 in H1;rewrite HH0 in H1;my_rank.
- my_subst;my_rank.
- generalize H0;case_eq (collinear b a a);my_rank.
assert(HH0 := col_2 b a);my_rank;rewrite HH0 in H1;my_rank.
Qed.

Lemma rk_inter_aux1 : forall a b c d e : Point, 
~a[==]b -> 
~c[==]d /\ ~c[==]e /\ ~d[==]e ->
~c[==]a /\ ~c[==]b \/
~d[==]a /\ ~d[==]b \/
~e[==]a /\ ~e[==]b.
Proof.
my_col.
case_eq (eq_dec_u a c);case_eq (eq_dec_u b d);my_col;my_subst.
case_eq (eq_dec_u b c);case_eq (eq_dec_u a d);my_col;my_subst.
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
case_eq (if collinear_with_all a (all_pairs (p :: l0))
    then contains_three_non_collinear_points (p :: l0)
    else true).
intros.
inversion H2.
case_eq (if eq_dec_u a p then contains_two_distinct_points (p :: l0) else true).
intros.
inversion H3.
intros.
inversion H3.
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

End s_pEquivRk_2.