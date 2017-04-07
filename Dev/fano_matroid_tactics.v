Require Export ProjectiveGeometry.Dev.basic_matroid_list.

Ltac use H := decompose [and ex] H; clear H.

Ltac my_split := 
  repeat match goal with [H : _ /\ _ |- _] => destruct H end.

(** Tag hypothèse **)
Definition rk_tagged A := rk A.

Lemma rk_rk_tagged : forall A , rk A = rk_tagged A.
Proof.
trivial.
Qed.

Lemma rk_tagged_rk : forall A , rk_tagged A = rk A.
Proof.
trivial.
Qed.

Ltac tag_all :=
repeat match goal with
| H : rk _ = _ |- _ => rewrite rk_rk_tagged in H
end.

Ltac untag_all :=
repeat match goal with
| H : rk_tagged _ = _ |- _ => rewrite rk_tagged_rk in H
end.

Ltac tag H := rewrite rk_rk_tagged in H.

Ltac untag H := rewrite rk_tagged_rk in H.

(** Lemmes simplification inversion droite/plan **)

Ltac rk_couple_bis A B :=
match goal with
| H : rk(A :: B :: nil) = _ |- _ => assumption
| H : rk(B :: A :: nil) = _ |- _ => rewrite couple_equal in H;assumption
end.

Ltac rk_couple_bis_bis :=
match goal with
| H : _ |- rk(?A :: ?B :: nil) = _ => solve [rk_couple_bis A B]
end.

Lemma rk_triple_2_3_0 : forall A B C, 
rk(A :: B :: C :: nil) = 2 -> rk(A :: B :: C :: nil) = 3 -> False.
Proof.
intros;rewrite H in H0;intuition.
Qed.

Lemma rk_triple_2_3_1 : forall A B C, 
rk(A :: B :: C :: nil) = 2 -> rk(A :: C :: B :: nil) = 3 -> False.
Proof.
intros;rewrite <-triple_equal_1 in H0;rewrite H in H0;intuition.
Qed.

Lemma rk_triple_2_3_2 : forall A B C, 
rk(A :: B :: C :: nil) = 2 -> rk(B :: A :: C :: nil) = 3 -> False.
Proof.
intros;rewrite <-triple_equal_2 in H0;rewrite H in H0;intuition.
Qed.

Lemma rk_triple_2_3_3 : forall A B C, 
rk(A :: B :: C :: nil) = 2 -> rk(B :: C :: A :: nil) = 3 -> False.
Proof.
intros;rewrite <-triple_equal_3 in H0;rewrite H in H0;intuition.
Qed.

Lemma rk_triple_2_3_4 : forall A B C, 
rk(A :: B :: C :: nil) = 2 -> rk(C :: A :: B :: nil) = 3 -> False.
Proof.
intros;rewrite <-triple_equal_4 in H0;rewrite H in H0;intuition.
Qed.

Lemma rk_triple_2_3_5 : forall A B C, 
rk(A :: B :: C :: nil) = 2 -> rk(C :: B :: A :: nil) = 3 -> False.
Proof.
intros;rewrite <-triple_equal_5 in H0;rewrite H in H0;intuition.
Qed.

Lemma rk_triple_3_2_0 : forall A B C, 
rk(A :: B :: C :: nil) = 3 -> rk(A :: B :: C :: nil) = 2 -> False.
Proof.
intros;rewrite H in H0;intuition.
Qed.

Lemma rk_triple_3_2_1 : forall A B C, 
rk(A :: B :: C :: nil) = 3 -> rk(A :: C :: B :: nil) = 2 -> False.
Proof.
intros;rewrite <-triple_equal_1 in H0;rewrite H in H0;intuition.
Qed.

Lemma rk_triple_3_2_2 : forall A B C, 
rk(A :: B :: C :: nil) = 3 -> rk(B :: A :: C :: nil) = 2 -> False.
Proof.
intros;rewrite <-triple_equal_2 in H0;rewrite H in H0;intuition.
Qed.

Lemma rk_triple_3_2_3 : forall A B C, 
rk(A :: B :: C :: nil) = 3 -> rk(B :: C :: A :: nil) = 2 -> False.
Proof.
intros;rewrite <-triple_equal_3 in H0;rewrite H in H0;intuition.
Qed.

Lemma rk_triple_3_2_4 : forall A B C, 
rk(A :: B :: C :: nil) = 3 -> rk(C :: A :: B :: nil) = 2 -> False.
Proof.
intros;rewrite <-triple_equal_4 in H0;rewrite H in H0;intuition.
Qed.

Lemma rk_triple_3_2_5 : forall A B C, 
rk(A :: B :: C :: nil) = 3 -> rk(C :: B :: A :: nil) = 2 -> False.
Proof.
intros;rewrite <-triple_equal_5 in H0;rewrite H in H0;intuition.
Qed.

(** Tactiques de simplification/mise en correspondance droite/droite droite/plan ou plan/plan **)

Ltac rk_triple :=
match goal with
| H : rk(?A :: ?B :: ?C :: nil) = _ |- rk(?A :: ?B :: ?C :: nil) = _ => assumption
| H : rk(?A :: ?B :: ?C :: nil) = _ |- rk(?A :: ?C :: ?B :: nil) = _ => rewrite <-triple_equal_1 in H;assumption
| H : rk(?A :: ?B :: ?C :: nil) = _ |- rk(?B :: ?A :: ?C :: nil) = _ => rewrite <-triple_equal_2 in H;assumption
| H : rk(?A :: ?B :: ?C :: nil) = _ |- rk(?B :: ?C :: ?A :: nil) = _ => rewrite <-triple_equal_3 in H;assumption
| H : rk(?A :: ?B :: ?C :: nil) = _ |- rk(?C :: ?A :: ?B :: nil) = _ => rewrite <-triple_equal_4 in H;assumption
| H : rk(?A :: ?B :: ?C :: nil) = _ |- rk(?C :: ?B :: ?A :: nil) = _ => rewrite <-triple_equal_5 in H;assumption
end.

Ltac rk_triple_bis A B C :=
match goal with
| H : rk(A :: B :: C :: nil) = _ |- _ => assumption
| H : rk(A :: C :: B :: nil) = _ |- _ => rewrite <-triple_equal_1 in H;assumption
| H : rk(B :: A :: C :: nil) = _ |- _ => rewrite <-triple_equal_2 in H;assumption
| H : rk(B :: C :: A :: nil) = _ |- _ => rewrite <-triple_equal_3 in H;assumption
| H : rk(C :: A :: B :: nil) = _ |- _ => rewrite <-triple_equal_4 in H;assumption
| H : rk(C :: B :: A :: nil) = _ |- _ => rewrite <-triple_equal_5 in H;assumption
end.

Ltac rk_triple_bis_bis :=
match goal with
| H : _ |- rk(?A :: ?B :: ?C :: nil) = _ => solve [rk_triple_bis A B C]
end.

Ltac rk_triple_2_3 :=
repeat match goal with
| H : rk(?A :: ?B :: ?C :: nil) = 2 ,H0 : rk(?A :: ?B :: ?C :: nil) = 3 |- _ => let HH:= fresh in assert(HH := rk_triple_2_3_0 A B C H H0);elim HH
| H : rk(?A :: ?B :: ?C :: nil) = 2 ,H0 : rk(?A :: ?C :: ?B :: nil) = 3 |- _ => let HH:= fresh in assert(HH := rk_triple_2_3_1 A B C H H0);elim HH
| H : rk(?A :: ?B :: ?C :: nil) = 2 ,H0 : rk(?B :: ?A :: ?C :: nil) = 3 |- _ => let HH:= fresh in assert(HH := rk_triple_2_3_2 A B C H H0);elim HH
| H : rk(?A :: ?B :: ?C :: nil) = 2 ,H0 : rk(?B :: ?C :: ?A :: nil) = 3 |- _ => let HH:= fresh in assert(HH := rk_triple_2_3_3 A B C H H0);elim HH
| H : rk(?A :: ?B :: ?C :: nil) = 2 ,H0 : rk(?C :: ?A :: ?B :: nil) = 3 |- _ => let HH:= fresh in assert(HH := rk_triple_2_3_4 A B C H H0);elim HH
| H : rk(?A :: ?B :: ?C :: nil) = 2 ,H0 : rk(?C :: ?B :: ?A :: nil) = 3 |- _ => let HH:= fresh in assert(HH := rk_triple_2_3_5 A B C H H0);elim HH
end.

Ltac rk_triple_2_3_bis HH0 A B C :=
match goal with
| H0 : rk(A :: B :: C :: nil) = 3 |- _ => let HH:= fresh in assert(HH := rk_triple_2_3_0 A B C HH0 H0);elim HH
| H0 : rk(A :: C :: B :: nil) = 3 |- _ => let HH:= fresh in assert(HH := rk_triple_2_3_1 A B C HH0 H0);elim HH
| H0 : rk(B :: A :: C :: nil) = 3 |- _ => let HH:= fresh in assert(HH := rk_triple_2_3_2 A B C HH0 H0);elim HH
| H0 : rk(B :: C :: A :: nil) = 3 |- _ => let HH:= fresh in assert(HH := rk_triple_2_3_3 A B C HH0 H0);elim HH
| H0 : rk(C :: A :: B :: nil) = 3 |- _ => let HH:= fresh in assert(HH := rk_triple_2_3_4 A B C HH0 H0);elim HH
| H0 : rk(C :: B :: A :: nil) = 3 |- _ => let HH:= fresh in assert(HH := rk_triple_2_3_5 A B C HH0 H0);elim HH
end.

Ltac rk_triple_2_3_bis_bis :=
match goal with
| H : rk(?A :: ?B :: ?C :: nil) = 2 |- _ => solve [rk_triple_2_3_bis H A B C]
end.

Ltac rk_triple_3_2_bis HH0 A B C :=
match goal with
| H0 : rk(A :: B :: C :: nil) = 2 |- _ => let HH:= fresh in assert(HH := rk_triple_3_2_0 A B C HH0 H0);elim HH
| H0 : rk(A :: C :: B :: nil) = 2 |- _ => let HH:= fresh in assert(HH := rk_triple_3_2_1 A B C HH0 H0);elim HH
| H0 : rk(B :: A :: C :: nil) = 2 |- _ => let HH:= fresh in assert(HH := rk_triple_3_2_2 A B C HH0 H0);elim HH
| H0 : rk(B :: C :: A :: nil) = 2 |- _ => let HH:= fresh in assert(HH := rk_triple_3_2_3 A B C HH0 H0);elim HH
| H0 : rk(C :: A :: B :: nil) = 2 |- _ => let HH:= fresh in assert(HH := rk_triple_3_2_4 A B C HH0 H0);elim HH
| H0 : rk(C :: B :: A :: nil) = 2 |- _ => let HH:= fresh in assert(HH := rk_triple_3_2_5 A B C HH0 H0);elim HH
end.

Ltac rk_triple_3_2_bis_bis :=
match goal with
| H : rk(?A :: ?B :: ?C :: nil) = 3 |- _ => solve [rk_triple_3_2_bis H A B C]
end.

Ltac equal_degens := 
match goal with
| [H : ~ ?X = ?X |- _] => apply False_ind;apply H;reflexivity
end.

