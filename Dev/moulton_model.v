Require Export Reals.
Require Export Fourier.
Require Export Nsatz.
Require Export ProjectiveGeometry.Dev.projective_plane_axioms.
Require Export ProjectiveGeometry.Dev.field_variable_isolation_tactics.

Section s_MoultonModel.

Open Scope R_scope.

Lemma R_eq_dec: forall r1 r2 : R, {r1 <> r2} + {r1 = r2}.
Proof.
intros.
elim (Req_EM_T r1 r2);intuition.
Qed.

Lemma zero_neq_minus_one : 0 <> -(1).
Proof.
auto with real.
Qed.

Hint Resolve zero_neq_minus_one : field_hints.

Lemma one_not_two : 1 <> 2.
Proof.
discrR.
Qed.

Hint Resolve one_not_two : field_hints.

(** Here we build a non-desarguesian plane : **)
(** Moulton plane. **)

(* points and lines with one infinite line for intersection purposes *)
Inductive IndPoint : Set :=
 | P : R -> R -> IndPoint 
 | dir : option R -> IndPoint.
(* affine points together with an additionnal point bearing the direction possibly vertical *)

Inductive IndLine : Set :=
 | L : option R -> R -> IndLine 
 | Infinite :  IndLine.
(* affine lines with an additionnal line *)

Definition Point : Set := IndPoint.
Definition Line : Set := IndLine.

Axiom R_pos_neg : forall x : R, {x<0%R}+{x>=0%R}.

Definition Incid : Point -> Line -> Prop := 
fun P L => 
match P with 
| P x y => 
  match L with L None b=> x=b
  | L (Some m) b => 
  if (R_pos_neg m) 
  then if (R_pos_neg x) then  y=m*x+b else y =2*m*x+b 
  else y=m*x+b
  | Infinite => False
  end
| dir None => match L with L None _      => True  
                                          | L (Some _) _ => False
                                          | Infinite => True
                       end
| dir (Some m) => match L with L None _      => False
                                          | L (Some m') _ => if (R_eq_dec m m') then False else True
                                          | Infinite => True
                              end
end. 

Lemma incid_dec :  forall (A:Point)(l:Line), {Incid A l} + {~Incid A l}.
Proof.
intros A; case A.
intros x y l; case l.
intro o; case o; [intros m b | intro b].
simpl.
elim (R_pos_neg m).
intros Hm.
elim (R_pos_neg x).
intros.
generalize (R_eq_dec y (m * x + b)).
intuition.
intros.
generalize (R_eq_dec y (2* m * x +b)).
intuition.
intros.
generalize (R_eq_dec y (m *x + b)).
intuition.
simpl.
generalize (R_eq_dec x b).
intuition.
right.
intuition.
intro o; case o; [intros m | idtac]; intros l; case l.
intros m'; case m'; clear m'.
intros m' b.
simpl.
elim (R_eq_dec m m').
right; intuition.
left; trivial.
right; intuition.
simpl;left; trivial.
intro m'; case m'; clear m'.
intros m' b.
right; intuition.
simpl;left; trivial.
simpl; left; trivial.
Qed.

Lemma eq_point_dec : forall A B : Point, {A[==]B} + {A<>B}.
Proof.
intros A; case A.
intros xA yA. 
intros B; case B.
intros xB yB.
elim (R_eq_dec xA xB).
intros; right.
intro H; injection H; intuition.
intros HxAxB.
elim (R_eq_dec yA yB).
intros; right.
intro H; injection H; intuition.
intros HyAyB.
subst.
left; trivial.
right; discriminate.
intros o; case o.
intros m B; case B.
right; discriminate.
intros o'; case o'.
intros r.
elim (R_eq_dec m r).
intros Hmr.
right; intro H; apply Hmr; injection H; auto.
left; subst;trivial.
right; discriminate.
intros B; case B.
right;discriminate.
intro o'; case o'.
right; discriminate.
left; trivial.
Qed. 

Lemma strict_or_not : forall x:R, x>=0 -> {x=0}+{x>0}.
Proof.
intros x Hx.
generalize (total_order_T x 0); intros Ht; intuition.
Qed.

Lemma hint0 : forall xA xB, xA <0 -> xB >0 -> 2*xB - xA <> 0.
Proof.
intros xA xB HxA HxB.
apply Rlt_dichotomy_converse.
right.
assert (0 + 0 < 2 * xB + - xA).
apply (Rplus_lt_compat 0 (2*xB) 0 (-xA)).
fourier.
fourier.
fourier.
Qed.

Lemma hint1 : forall m1 m2, m1<0 -> m2>=0 -> m1-m2<>0.
Proof.
intros.
apply Rlt_dichotomy_converse.
left.
assert (m1+0<0+m2).
apply (Rplus_lt_le_compat m1 0 0 m2); fourier .
fourier.
Qed.

Lemma hint2 : forall m1 m2, m1<0 -> m2>=0 -> 2*m1-m2<>0.
Proof.
intros.
apply Rlt_dichotomy_converse.
left.
assert (2*m1+0<0+m2).
apply (Rplus_lt_le_compat (2*m1) 0 0 m2); fourier .
fourier.
Qed.

Lemma hint2' : forall m1 m2, m1<0 -> m2>=0 -> m1-2*m2<>0.
Proof.
intros.
apply Rlt_dichotomy_converse.
left.
assert (2*m1+0<0+m2).
apply (Rplus_lt_le_compat (2*m1) 0 0 m2); fourier .
fourier.
Qed.

Lemma hint2'' : forall m1 m2, m2<=0 -> m1>0 -> m1-2*m2<>0.
Proof.
intros.
apply Rlt_dichotomy_converse.
right.
fourier.
Qed.

Lemma hint3 : forall m1 m2, m1<0 -> m2>=0 -> 2*m1-2*m2<>0.
Proof.
intros.
apply Rlt_dichotomy_converse.
left.
assert (2*m1+0<0+2*m2).
apply (Rplus_lt_le_compat (2*m1) 0 0 (2*m2)); fourier .
fourier.
Qed.

Hint Resolve hint0 hint1 hint2 hint2' hint2'' hint3 : real .

Lemma hint4 : forall (b1 : R)(b2 : R)(m1 : R)(m2 : R)
(Hm1 : m1 < 0)(Hm2 : m2 >= 0)(b : (b2 - b1) / (m1 - m2) >= 0)
(Ha : (b2 - b1) / (2 * m1 - m2) < 0), False.
Proof.
intros b1 b2 m1 m2 Hm1 Hm2 Ha Hb.
assert ((b2-b1)<=0).
replace (b2-b1) with ((m1-m2)*((b2-b1)/(m1-m2))) by (field;auto with real).
replace 0 with ((m1-m2) * 0)  by field.
apply Rmult_le_compat_neg_l.
fourier.
auto with real.
assert (b2-b1>0).
replace (b2 - b1) with ((2*m1-m2)*((b2 - b1) / (2 * m1 - m2)) ) by (field; auto with real).
replace 0 with ( (2*m1-m2) * 0) by field.
apply Rmult_lt_gt_compat_neg_l.
fourier.
assumption.
fourier.
Qed.

Hint Resolve hint4 : real.

Lemma hint5 : forall x, x<0 -> x>=0 -> False.
Proof.
intros.
fourier.
Qed.

Hint Resolve hint5 : real.

Lemma hint6 : forall (b1 : R)(b2 : R)(m1 : R)(m2 : R)(Hm1 : m1 < 0)(Hm2 : m2 < 0)
(Hm1m2 : m1 <> m2)(Hm : (b2 - b1) / (m1 - m2) >= 0)(Ha : (b2 - b1) / (2 * m1 - 2 * m2) < 0),False.
Proof.
intros.
replace ((b2-b1)/(2*m1 - 2*m2)) with (((b2-b1)/(m1-m2))/2) in Ha.
assert ((b2 - b1) / (m1 - m2) <0).
replace ((b2 - b1) / (m1 - m2)) with (2* ((b2 - b1) / (m1 - m2) /2) ) by (field; auto with real).
replace 0 with (2 * 0) by field.
apply Rmult_lt_compat_l.
fourier.
assumption.
eauto with real.
field.
assert (m1-m2<>0).
auto with real.
split.
replace (2*m1 - 2*m2) with (2*(m1-m2)) by field.
apply Rlt_dichotomy_converse.
elim (R_pos_neg (m1-m2)).
left.
replace 0 with (2 * 0) by field.
apply Rmult_lt_compat_l.
fourier.
assumption.
intros.
elim (strict_or_not (m1-m2) b).
intros.
assert (m1=m2).
cut False.
intros Hf; elim Hf.
auto.
subst.
replace (m2-m2) with 0  in H by field.
cut False.
intros Hf; elim Hf.
apply H.
auto with real.
intros Hm1m2'.
right.
replace 0 with (2 * 0) by field.
apply Rmult_gt_compat_l.
fourier.
assumption.
auto.
Qed.

Hint Resolve hint6 : real.

Lemma hint7 : forall (m1 : R) (m2 : R) (Hm1m2:m1<>m2),
2 * m1 - 2 * m2 <> 0.
Proof.
intros.
replace (2*m1-2*m2) with (2*(m1-m2)) by field.
assert ((m1-m2)<>0).
auto with real.
apply Rmult_integral_contrapositive_currified.
discrR.
assumption.
Qed.

Hint Resolve hint7 : real.


Lemma sub_lemma1 : forall 
(xA : R)
(yA : R)
(xB : R)
(yB : R)
(HxAxB : xB - xA <> 0)
(m := (yB - yA) / (xB - xA) : R)
(Hm : m < 0)
(HxA : xA < 0)
(HxB : xB >= 0),
{l : Line | Incid (P xA yA) l /\ Incid (P xB yB) l}.
Proof.
intros.
elim (strict_or_not xB HxB).
(* xB=0 *)
intros HxB'.
exists (L (Some m) yB).
simpl.
case (R_pos_neg m).
intros Hm'.
case (R_pos_neg xA).
intros HxA'.
case (R_pos_neg xB).
intros HxB''.
fourier.
intros HxB''.
split.
unfold m;rewrite HxB' in *; field; auto with real.
unfold m; rewrite HxB' in *; field; auto with real.
intros; fourier.
intros; fourier.
(* xB > 0 *)
intros HxB'.
pose (m' := (((2*yA*xB-yB*xA)/(2*xB-xA))-yA)/(-xA)).
pose (b:=(2*yA*xB-yB*xA)/(2*xB-xA)).
exists (L (Some m') b).
simpl.
case (R_pos_neg m).
intros Hm'.
case (R_pos_neg xA).
intros HxA'.
case (R_pos_neg xB).
intros HxB''.
fourier.
intros HxB''.
(* m' < 0 *)
case (R_pos_neg m').
intros Hm''.
split.
unfold b,m' in *;field.
split.
auto with real.
auto with real.
unfold b,m' in *;field.
split.
auto with real.
auto with real.
(* m' >=0 *)
intros Hm''.
assert (m'<0).
assert (((2 * yA * xB - yB * xA) / (2 * xB - xA) - yA) <0).
apply (Rmult_lt_reg_l (2*xB-xA)).
fourier.
replace ((2 * xB - xA) * 0) with 0 by field.
replace ((2 * xB - xA) * ((2 * yA * xB - yB * xA) / (2 * xB - xA) - yA))
with ((-xA)*(yB-yA)) by (field; auto with real).
replace 0 with ((-xA)*0) by field.
apply Rmult_lt_compat_l.
fourier.
assert (0<xB-xA).
fourier.
unfold b,m,m' in *.
assert ((xB - xA) * ((yB - yA) / (xB - xA)) < (xB - xA) * 0 ).
apply (Rmult_lt_compat_l (xB-xA) ((yB-yA)/(xB-xA)) 0); auto.
replace ((xB-xA) * 0) with 0 in H0 by field.
replace ((xB - xA) * ((yB - yA) / (xB - xA)) ) with
(yB-yA) in H0.
assumption.
field.
auto with real.
unfold m'.
apply  (Rmult_lt_reg_l (-xA)).
fourier.
replace (- xA * (((2 * yA * xB - yB * xA) / (2 * xB - xA) - yA) / - xA)) with
((2 * yA * xB - yB * xA) / (2 * xB - xA) - yA) by 
(field; split; [auto with real | auto with real]).
replace (-xA * 0) with 0 by field.
assumption.
fourier.
intros; fourier.
intros; fourier.
Qed.

Lemma sub_lemma2 : forall (xA : R) (yA : R) (o : option R), {l : Line | Incid (P xA yA) l /\ Incid (dir o) l}.
Proof.
intros xA yA o ; case o.
intros r.
elim (R_pos_neg r).
intros Hr.
elim (R_pos_neg xA).
intros HxA.
exists (L (Some r) (yA-r*xA)).
simpl.
elim (R_pos_neg r).
intros Hr'.
split.
elim (R_pos_neg xA).
intros HxA'.
field.
intros; fourier.
elim (R_eq_dec r r); intuition.
intros; fourier.
exists (L (Some r) (yA-2*r*xA)).
simpl.
elim (R_pos_neg r).
intros Hr'.
split.
elim (R_pos_neg xA).
intros HxA'.
intros; fourier.
intros; field.
elim (R_eq_dec r r); intuition.
intros; fourier.
intros Hr'.
exists (L (Some r) (yA-r*xA)).
simpl.
elim (R_pos_neg r).
intros Hr''.
intros; fourier.
intros.
split.
field.
elim (R_eq_dec r r); intuition.
exists (L None xA).
simpl; solve [auto].
Qed.

Lemma a1_exist : forall (A B : Point) ,{l:Line | Incid A l /\ Incid B l}.
Proof.
intros A; elim A.
intros xA yA.
intros B; elim B.
intros xB yB.
elim (R_eq_dec (xB-xA) 0).
intros HxAxB.
pose (m:=((yB-yA)/(xB-xA))).
(* m < 0 *)
elim (R_pos_neg m).
intros Hm.
elim (R_pos_neg xA).
intros HxA.
elim (R_pos_neg xB).
intros HxB.
(* xA < 0 and xB < 0 *)
pose (b:=yB - m*xB).
exists (L (Some m) b).
simpl.
case (R_pos_neg m).
intros Hm'.
case (R_pos_neg xA).
intros HxA'.
case (R_pos_neg xB).
intros HxB'.
split.
unfold b,m in *.
field; assumption.
unfold b,m in *.
field; assumption.
intros; fourier.
intros; fourier.
intros; fourier.
(* xA <0 and xB >=0 *)
intros HxB.
apply sub_lemma1; auto.
(* xA >=0 !!! re-using sublemma1 *)
intros HxA.
elim (R_pos_neg xB).
intros HxB.
pose (m2:=(yA-yB)/(xA-xB)).
assert (Hm2 : m2 < 0).
replace m2 with m by (unfold m2,m in *;field; auto with real).
assumption.
assert ({l : Line | Incid (P xB yB) l /\ Incid (P xA yA) l}).
apply (sub_lemma1 xB yB xA yA); auto.
auto with real.
elim H; intros l (HlB,HlA).
exists l; auto.
(* xA >=0 and xB >=0 *)
intros HxB.
exists (L (Some (m/2)) (yA -(yB-yA)/(xB-xA)*xA)).
simpl.
case (R_pos_neg (m/2)).
intros Hm2.
case (R_pos_neg xA).
intros; fourier.
intros HxA'.
case (R_pos_neg xB).
intros; fourier.
intros HxB'.
split; unfold m in *;field; auto.
intros; fourier.
(* m >= 0 *)
intros Hm.
pose (b:= yB - m*xB).
exists (L (Some m) b).
simpl.
case (R_pos_neg m).
intros; fourier.
intros Hm'.
unfold b,m in *.
split.
field; assumption.
field; assumption.
(* vertical line *)
intros HxBxA.
exists (L None xA).
simpl;intuition.
(* added projective lines *) 
apply sub_lemma2.
intros o B; case B.
intros xB yB.
assert ({l : Line | Incid (P xB yB) l /\ Incid (dir o) l}).
apply (sub_lemma2 xB yB).
elim H; intros l H'; exists l; intuition.
intros o'.
exists Infinite.
simpl; case o; case o'; auto.
Qed.

Lemma sub_lemma3 : forall (b1 : R) (b2 : R) (m1 : R) (m2 : R) (Hm1 : m1 < 0) (Hm2 : m2 >= 0),
{A : Point | Incid A (L (Some m1) b1) /\ Incid A (L (Some m2) b2)}.
Proof.
intros b1 b2 m1 m2 Hm1 Hm2.
elim (R_pos_neg ((b2-b1)/(m1-m2))).
intros H.
exists (P ((b2-b1) / (m1-m2)) (m1*(b2-b1)/(m1-m2)+b1)).
simpl.
elim (R_pos_neg m1).
intros Hm1'.
elim (R_pos_neg ((b2-b1) / (m1 - m2))).
intros H'.
split.
field;auto with real.
elim (R_pos_neg m2).
intros; fourier.
intros Hm2'.
field; auto with real.
intros.
cut False.
intros Hf; elim Hf.
eauto with real.
intros; fourier.
intros.
elim (R_pos_neg ((b2-b1)/(2*m1-m2))).
intros Ha.
cut False.
intros Hf; elim Hf.
eauto with real.
intros Hb0. 
exists (P ((b2-b1)/(2*m1-m2)) (m2*(b2-b1)/(2*m1-m2)+b2)).
simpl.
elim (R_pos_neg m1).
intros Hm1'.
elim (R_pos_neg ((b2 - b1) / (2*m1 - m2))).
intros Hb'.
cut False.
intros Hf; elim Hf.
eauto with real.
intros.
split.
field; auto with real.
elim (R_pos_neg m2).
intros; fourier.
intros Hm2'.
field.
auto with real.
intros;fourier.
Qed.

Lemma sub_lemma4 : forall (b1 : R)(b2 : R)(m1 : R),
{A : Point | Incid A (L (Some m1) b1) /\ Incid A (L None b2)}.
Proof.
intros.

elim (R_pos_neg m1).
intros Hm1.
elim (R_pos_neg b2).
intros Hb2.

exists (P b2 (m1*b2+b1)).
simpl.
elim (R_pos_neg m1).
intros Hm1'.
elim (R_pos_neg b2).
intros Hb2'.
split; field.
intros; fourier.
intros; fourier.
intros Hb2.
exists (P b2 (2*m1*b2+b1)).
simpl.
elim (R_pos_neg m1).
intros Hm1'.
elim (R_pos_neg b2).
intros; fourier.
intros Hb2'.
split; field.
intros; fourier.
intros Hm1.
exists (P b2 (m1*b2+b1)).
simpl.
elim (R_pos_neg m1).
intros; fourier.
intros Hm1'.
elim (R_pos_neg b2).
intros Hb2'.
split; field.
intros Hb2.
split; field.
Qed.

Lemma a2_exist : forall (l1 l2:Line), {A:Point | Incid A l1 /\ Incid A l2}.
Proof.
intros l1; case l1.
intros m1' b1.
intros l2; case l2.
intros m2' b2.
case m1'.
intros m1.
case m2'.
intros m2.
case (R_pos_neg m1).
intros Hm1.
case (R_pos_neg m2).
intros Hm2.
elim (R_eq_dec m1 m2).
intros Hm1m2.

elim (R_pos_neg ((b2-b1)/(m1-m2))).
intros a.
exists (P ((b2-b1)/(m1-m2)) (m1*(b2-b1)/(m1-m2)+b1)).
simpl.
elim (R_pos_neg m1).
intros Hm1'.
elim (R_pos_neg  ((b2 - b1) / (m1 - m2))).
intros Ha.
split.
field; auto with real.
elim (R_pos_neg m2).
intros Hm2'.
field; auto with real.
intros; fourier.
intros.
cut False.
intros Hf; elim Hf.
eauto with real.
intros; fourier.

intros Hm.
elim (R_pos_neg ((b2-b1)/(2*m1-2*m2))).
intros Ha.
cut False.
intros Hf; elim Hf.
eapply (hint6 b1 b2 m1 m2); auto.
intros Hb0. 
exists (P ((b2-b1)/(2*m1-2*m2)) (2*m1*(b2-b1)/(2*m1-2*m2)+b1)).
simpl.
elim (R_pos_neg m1).
intros a0.
elim (R_pos_neg ((b2 - b1) / (2*m1 - 2*m2))).
intros Hb1.
cut False.
intros Hf; elim Hf.
eauto with real.
intros Hb.
split.
field; auto with real.
elim (R_pos_neg m2).
intros Hm2'.
field; auto with real.
intros; fourier.
intros; fourier.
intros Hm1m2.
subst m2.
exists (dir(Some m1)).
simpl.
elim (R_eq_dec m1 m1).
intros; intuition. 
auto.
intros Hm2.
apply sub_lemma3; auto.

intros Hm1.
elim (R_pos_neg m2).
intros Hm2.
assert {A : Point | Incid A (L (Some m2) b2) /\ Incid A (L (Some m1) b1)}.
apply (sub_lemma3 b2 b1 m2 m1); auto.
elim H; intros A' H'; exists A'; intuition.
intros Hm2.
elim (R_eq_dec m1 m2).
intros Hm1m2.
exists (P ((b2-b1)/(m1-m2)) (m1*((b2-b1)/(m1-m2))+b1)).
simpl.
elim (R_pos_neg m1).
intros Hm1'; fourier.
intros Hm1'.
split.
field;auto with real.
elim (R_pos_neg m2).
intros; fourier.
intros Hm2'.
field; auto with real.
intros Hm1m2.
subst m1.
exists (dir(Some m2)).
simpl.
elim (R_eq_dec m2 m2); intuition.

apply sub_lemma4.
case m2'.
intros m2.
assert {A : Point |  Incid A (L (Some m2) b2)/\Incid A (L None b1)}.
apply sub_lemma4.
elim H; intros A' H'; exists A'; intuition.
elim (R_eq_dec b1 b2).
intros Hb1b2.
exists (dir None).
simpl; auto.
intros; subst.
exists (P b2 0).
simpl; auto.
exists (dir m1').
simpl.
case m1'.
intros r; case (R_eq_dec r r); intuition.
auto.
intros l2; case l2.
intros o; case o.
intros m b.
exists (dir (Some m)).
simpl.
case (R_eq_dec m m); intuition.
intros b.
exists (dir None).
simpl; auto.
exists (dir None); simpl; auto.
Qed.

Lemma a3_1 : 
  (forall l:Line,{A:Point & {B:Point & {C:Point | (~A[==]B /\ ~A[==]C /\ ~B[==]C /\Incid A l /\Incid B l /\ Incid C l)}}}).
Proof.
intro l;case l.
intros o; case o.
intros m b.
case (R_pos_neg m).
intros Hm.
exists (P 0 b).
exists (P (-1) (b-m)).
exists (P 1 (b+2*m)).
simpl.
split.
intro;injection H; intuition.
split.
intro;injection H; intuition.
split.
intro;injection H; intros; assert (-1<>1) by discrR; intuition.
case (R_pos_neg m).
intros Hm'.
case (R_pos_neg 0).
intros; fourier.
intros.
case (R_pos_neg (-1)).
intros.
case (R_pos_neg 1).
intros; fourier.
intros.
repeat split; field.
intros; fourier.
intros; fourier.

intros Hm.
exists  (P 0 b).
exists (P (-1) (b-m)).
exists (P 1 (b+m)).
simpl.
split.
intro;injection H; intuition.
split.
intro;injection H; intuition.
split.
intro;injection H; intros; assert (-1<>1) by discrR; intuition.
case (R_pos_neg m).
intros; fourier.
intros Hm'.
repeat split; field.
intros b.
exists (P b 0).
exists (P b 1).
exists (P b (-1)).
split.
intro;injection H; intuition.
split.
intro;injection H; intuition.
split.
intro;injection H; intros; assert (-1<>1) by discrR; intuition.
repeat split; field.
exists (dir None).
exists (dir (Some 0)).
exists (dir (Some 1)).
split.
intro H; discriminate.
split.
intros H; discriminate.
split.
intros H; injection H.
change (~0=1).
discrR.
simpl; auto.
Qed.

Lemma a3_2 : {l1:Line & {l2:Line | l1 <> l2}}.
Proof.
exists (L None 0).
exists (L (Some 0) 0).
intro H; discriminate.
Qed.

Lemma equiv_eq: forall a b, a = b <-> a - b = 0.
Proof.
split.
intros.
rewrite H.
ring.
intro.
assert (a-b + b = 0 + b).
rewrite H.
ring.
ring_simplify in H0.
assumption.
Qed.

Lemma equiv_or: forall a b, a = 0 \/ b = 0 <-> a*b = 0.
Proof.
intros.
split.
intro.
case H;intros.
rewrite H0.
ring.
rewrite H0.
ring.
intro.
apply Rmult_integral.
assumption.
Qed.

Lemma equiv_and : forall a b, a = 0 /\ b = 0 <-> a*a + b*b = 0.
Proof.
intros.
intuition.
subst.
ring.
generalize (Rplus_sqr_eq_0 a b).
intuition.
generalize (Rplus_sqr_eq_0 a b).
intuition.
Qed.

Ltac replace_cons X Y := progress (
   match Y  with  
| 0 => idtac
| _ => setoid_replace (X=Y) with (X-Y=0) by (apply equiv_eq)
end).

Ltac injection_equiv := let H := fresh in 
(split;
intro H;[injection H;auto | decompose [and] H;subst;auto]).

Ltac reduce_prop :=  
match goal with
| H: _ |- context [?X = ?Y] => replace_cons X Y
| H: _ |- context [?X = 0 /\ ?Y=0] => setoid_replace (X = 0 /\ Y=0) with (X*X + Y*Y = 0) by apply equiv_and
| H: _ |- context [?X = 0 \/ ?Y=0] => setoid_replace (X = 0 \/ Y=0) with (X*Y = 0) by apply equiv_or
| H :_ |- context [(Some ?m1 = Some ?m2)/\?r3 = ?r4] => 
   setoid_replace (Some m1 = Some m2 /\ r3 = r4) with (m1=m2/\ r3=r4) 
   by let Ha := fresh in let Hb := fresh in 
        (split; [ intros (Ha,Hb); inversion Ha; solve [solve [intuition]] | intros (Ha,Hb); rewrite Ha; solve [intuition] ])
| H: _ |- context [(?P ?X1 ?X2 = ?P ?Y1 ?Y2)] => 
   setoid_replace (P X1 X2 = P Y1 Y2) with (X1 = Y1 /\ X2 = Y2) 
  by let H := fresh in (split;intro H;[inversion H;auto | elim H ; let H1:=fresh in (let H2:= fresh in (intros H1 H2; rewrite H1, H2; auto))])

(*| H: _  |- context [P0 = P0] => setoid_replace (P0 = P0) with True by try (split;auto)
| H: _  |- context [?P \/ False] => setoid_replace (P \/ False) with (P) by try intuition
| H: _  |- context [False \/ ?P] => setoid_replace (False \/ P) with (P) by try intuition

| H: _  |- context [?P \/ True] => setoid_replace (P \/ True) with (True) by try intuition
| H: _  |- context [True \/ ?P] => setoid_replace (True \/ P) with (True) by try intuition
| H: _ |- False => cut (1=0);[intro;intuition | idtac]*)
end.

Ltac normalize_prop := repeat reduce_prop.

Ltac simplify_eqs eq1 eq2 eq3 eq4 := 
  ring_simplify in eq1;try subst;
  ring_simplify in eq2;try subst;
  ring_simplify in eq3;try subst;
  ring_simplify in eq4;try subst.

Lemma normalize_not: forall p x, p*x -1 = 0 -> p<>0.
Proof.
intros.
intro.
subst.
ring_simplify in H.
intuition.
Qed.

Lemma not_eq_prod : forall a b, 
 a<>0 -> 
 a*b=0 -> 
 b=0.
Proof.
intros.
rewrite  <- equiv_or in H0.
intuition.
Qed.

Lemma sys_eqs_1 : forall xa ya xb yb m1 m2 b1 b2, 
xa <> xb ->
ya = m2 * xa + b2 ->
ya = m1 * xa + b1 ->
yb = m2 * xb + b2 -> 
yb = m1 * xb + b1 ->
m1 = m2 /\ b1 = b2.
Proof.
intros.
split.
assert ((xa-xb)*(m1-m2)=0) by nsatz.
assert (m1-m2=0).
apply not_eq_prod with (a:=xa-xb);auto with real.
auto with real.
assert ((xa-xb)*(b1-b2)=0) by nsatz.
assert (b1-b2=0).
apply not_eq_prod with (a:=xa-xb);auto with real.
auto with real.
Qed.

Lemma sys_eqs_2 : forall xa ya xb yb m1 m2 b1 b2, 
xa <> xb ->
xa - 2* xb <> 0 ->
ya = m2 * xa + b2 ->
ya = m1 * xa + b1 ->
yb = 2*m2 * xb + b2 -> 
yb = 2*m1 * xb + b1 ->
m1 = m2 /\ b1 = b2.
Proof.
intros.
split.
assert ((xa-xb)*(xa-2*xb)*(m1-m2)=0) by nsatz.
rewrite  <- equiv_or in H5.
rewrite  <- equiv_or in H5.
decompose [or] H5.
assert (xa=xb) by auto with real.
subst;intuition.
intuition.
auto with real.

assert ((xa-xb)*(xa-2*xb)*(b1-b2)=0) by nsatz.
rewrite  <- equiv_or in H5.
rewrite  <- equiv_or in H5.
decompose [or] H5.
assert (xa=xb) by auto with real.
subst;intuition.
intuition.
auto with real.
Qed.

Lemma sys_eqs_3 : forall xa ya xb yb m1 m2 b1 b2
(a : xa <> xb)
(b : xb >= 0)
(b0 : m1 >= 0)
(a0 : xa < 0)
(a1 : m2 < 0),
ya = m2 * xa + b2 ->
ya = m1 * xa + b1 ->
yb = 2*m2 * xb + b2 -> 
yb = m1 * xb + b1 ->
False.
Proof.
intros.
assert (0< -m1).
IsoleVar b2 H1.
IsoleVar b2 H.
IsoleVar b1 H2.
IsoleVar b1 H0.
rewrite H2 in H0; clear H2.
rewrite H1 in H; clear H1.
assert (yb-ya=(2*xb-xa)*m2) by nsatz.
assert (yb-ya=(xb-xa)*m1).
clear a.
nsatz.
rewrite H1 in H2; clear H1.
assert (xb-xa>0) by fourier.
assert (2*xb-xa >0) by fourier.
assert ( (-m2)*(2 * xb - xa)  > (-m2)*0).
apply Rmult_lt_compat_l.
fourier.
fourier.
replace  (- m2 * (2 * xb - xa) ) with  (-( (2 * xb - xa)*m2)) in H4 by field. 
replace (-m2*0) with (0*0) in H4 by field.
rewrite H2 in H4.
replace  (- ((xb - xa) * m1)) with ((xb-xa)*(-m1)) in H4 by field.
eapply (Rmult_lt_reg_l (xb-xa)).
fourier.
fourier.
fourier.
Qed.

Lemma sys_eqs_4 : forall xa ya xb yb m1 m2 b1 b2
(a : xa <> xb)
(b0 : m1 >= 0)
(a0 : m2 < 0)
(H2 : ya = 2 * m2 * xa + b2)
(H0 : ya = m1 * xa + b1)
(H3 : yb = 2 * m2 * xb + b2)
(H1 : yb = m1 * xb + b1),
False.
Proof.
intros.
assert (0>m1).
assert (ya-yb=2*m2*(xa-xb)).
IsoleVar b2 H3.
IsoleVar b2 H2.
rewrite H2 in H3.
nsatz.
assert (ya-yb=m1*(xa-xb)).
IsoleVar b1 H1.
IsoleVar b1 H0.
rewrite H1 in H0.
nsatz.
rewrite H in H4.
assert (2*m2=m1).
replace (2*m2) with ((2*m2*(xa-xb))/(xa-xb)) by (field; auto with real).
replace m1 with (m1 * (xa - xb)/(xa-xb)) by (field; auto with real).
rewrite H4; auto.
intros; fourier.
intros; fourier.
Qed.

Lemma uniqueness : forall A B :Point, forall l m : Line,
 Incid A l -> Incid B l  -> Incid A m -> Incid B m -> A[==]B\/l=m.
Proof.
intros A B l m.
case_eq A;intros;
case_eq B;intros;
case_eq l;intros;
case_eq m;intros; try solve [intuition].
case_eq o; 
  [(intros m1 Hm1 ; case_eq o0 ; 
       [intros m2 Hm2 | intros Hm2 ])| intros Hm1].

rename r into xa.
rename r0 into ya.
rename r1 into xb.
rename r2 into yb.
rename r3 into b1.
rename r4 into b2.

simpl in *.
subst.
elim (R_eq_dec xa xb).
intros;right.
simpl in *.
generalize H2 H0 H3 H1; clear H2 H0 H3 H1.
repeat (elim (R_pos_neg)).

intros.
assert (m1=m2 /\ b1 =b2).
eapply (sys_eqs_1);eauto.
intuition;subst;auto.

intros.
assert (m1=m2 /\ b1 =b2).
eapply ( sys_eqs_2);eauto;auto with real.
intuition;subst;auto.

intros;cut (m1=m2 /\ b1 =b2).
intuition;subst;auto.
eapply ( sys_eqs_1);eauto.

intros;cut (m1=m2 /\ b1 =b2).
intuition;subst;auto.
assert False.
eapply sys_eqs_3; eauto.
intuition.

intros;cut (m1=m2 /\ b1 =b2).
intuition;subst;auto.
eapply (sys_eqs_2 xb yb xa ya) ; auto.
auto with real.

intros.
cut (m1=m2 /\ b1=b2).
intuition;subst;auto.
assert (2*m1=2*m2/\b1=b2).
eapply (sys_eqs_1 xa ya xb yb (2*m1)) ; auto.
elim H; intros H'1 H'2; split; [nsatz | trivial].

intros.
assert False.
eapply (sys_eqs_3 xb yb xa ya m1 m2); eauto.
intuition.

intros.

assert False.
eapply (sys_eqs_4 xb yb xa ya m1 m2); eauto.
elim H.

intros.
cut (m1=m2 /\ b1=b2).
intuition;subst;auto.
eapply (sys_eqs_1 xb yb xa ya m1 m2) ; auto.

intros.
assert False.
eapply (sys_eqs_3 xa ya xb yb m2 m1); eauto.
intuition.

intros.
assert False.
eapply (sys_eqs_3 xb yb xa ya m2 m1); eauto.
intuition.

intros.

assert False.
eapply (sys_eqs_4 xb yb xa ya m2 m1); eauto; auto with real.
elim H.

intros.
cut (m1=m2 /\ b1=b2).
intuition;subst;auto.
eapply (sys_eqs_1 xa ya xb yb m1 m2) ;eauto.

intros; unfold Incid in *. (* let's consider what happens with y *)
elim (R_eq_dec ya yb).
intros b3.
right.
subst xa.
generalize H2 H0 H1 H3; clear H2 H0 H1 H3.
repeat (elim R_pos_neg) ; try (solve [intros;subst;intuition | intros;subst;fourier]).

intros; subst; left; auto.

subst.
generalize H2 H0 H3 H1; clear H2 H0 H3 H1.
simpl.
repeat elim R_pos_neg ; try (solve [intros;subst;intuition | intros;subst;fourier]).

subst.
generalize H2 H0 H3 H1; clear H2 H0 H3 H1.
simpl.
repeat elim R_pos_neg; case o0 ; try (solve [intros; subst; intuition | intros; subst;fourier]).
intros r5; repeat elim R_pos_neg; try (solve [intros; subst; intuition | intros; subst;fourier]).
intros r5; elim R_pos_neg; try (solve [intros; subst; intuition | intros; subst;fourier]).

intros; subst.
unfold Incid in *; simpl; intuition.

intros; subst.
unfold Incid in *; simpl; intuition.

intros; subst.
unfold Incid in *; simpl.
generalize H2 H0 H3 H1; clear H2 H0 H3 H1.
case_eq o1; case_eq o0; case_eq o; try (solve[intuition]).
intros r3 Hr3 r4 Hr4 r5 Hr5; repeat elim R_eq_dec; try (solve [intros;subst;intuition | intros;subst;fourier]).

repeat elim R_pos_neg; try (solve [intros;subst;intuition | intros;subst;fourier]).
intros; subst.

rewrite H0 in *; right.
assert (r1=r2) by nsatz.
apply f_equal; auto.
intros; subst.
assert (r1=r2) by nsatz.
right.
apply f_equal2; auto.

intros; subst.
rewrite H0 in *.
intros; subst.
assert (r1=r2) by nsatz.
right; apply f_equal2; auto.

intros; subst; unfold Incid in *; simpl in *; solve [intuition].

intros; subst; unfold Incid in *; simpl in *; solve [intuition].

intros; subst; unfold Incid in *; simpl in *.
generalize H2 H0 H3 H1; clear H2 H0 H3 H1.
case_eq o0; case_eq o; try (solve[intros;subst;intuition | intros;subst;fourier]).
intros; subst.

intros; subst; unfold Incid in *; simpl in *.
generalize H2 H0 H3 H1; clear H2 H0 H3 H1.
case_eq o; case_eq o1;  case_eq o0; try (solve[intros;subst;intuition | intros;subst;fourier]).
intros r3 Hr3 r4 Hr4 r5 Hr5.
repeat elim R_eq_dec; try (solve[intros;subst;intuition | intros;subst;fourier]) .
repeat elim R_pos_neg; try (solve[intros;subst;intuition | intros;subst;fourier]) .
intros; subst.
rewrite H1 in *.
assert (r1=r2).
nsatz.
right; apply f_equal2; auto.
intros; subst.
rewrite H1 in *.
assert (r1=r2).
nsatz.
right; apply f_equal2; auto.
intros; subst.
rewrite H1 in *.
assert (r1=r2).
nsatz. 
right; apply f_equal2; auto.

intros; subst; unfold Incid in *; simpl in *;solve[ intuition].

intros; subst; unfold Incid in *; simpl in *; solve [intuition].

intros; subst.
unfold Incid in *; simpl in *.
generalize H2 H0 H3 H1; clear H2 H0 H3 H1.
case_eq o1; case_eq o0; case_eq o; try (solve[intros;subst;intuition | intros;subst;fourier]).
intros r3 Hr3 r4 Hr4 r5 Hr5; repeat elim R_eq_dec; try (solve [intros;subst;intuition | intros;subst;fourier]).
intros; subst; left; auto.

intros; subst.
unfold Incid in *; simpl in *.
generalize H2 H0 H3 H1; clear H2 H0 H3 H1.
case_eq o1; case_eq o0; case_eq o; try (solve[intros;subst;intuition | intros;subst;fourier]).
intros r3 Hr3 r4 Hr4 r5 Hr5; repeat elim R_eq_dec; try (solve [intros;subst;intuition | intros;subst;fourier]).

subst;
generalize H2 H0 H3 H1; clear H2 H0 H3 H1;
unfold Incid in *; simpl in *;
case o; case o1; case o0; simpl; 
intros r0 r1 r2; repeat elim R_eq_dec ; try (solve [intuition]).
intros;left; subst; intuition.
Qed.

Definition on_line := fun A B C l => Incid A l /\ Incid B l /\ Incid C l. 
Definition collinear A B C :=  exists l, Incid A l /\ Incid B l /\ Incid C l.
Definition non_collinear A B C := forall l, ~(on_line A B C l).

Lemma is_equiv : forall A B C, ~collinear A B C <-> non_collinear A B C.
Proof.
intros; split; unfold collinear, non_collinear.
intros; intro.
apply H.
exists l.
unfold on_line in *; intuition.
intros.
intro.
elim H0.
intros l Hl.
pose (H l).
unfold on_line in *.
intuition.
Qed.

Lemma foo :
forall m b : R,
4 = m * -3 + b -> 8 = m * -35 + b -> 38 = 12 * m + 11 * b -> False.
Proof.
intros; fourier.
Qed.

Lemma non_desarguesian : 
exists O, exists P, exists Q, exists R, exists P', exists Q', exists R',
exists alpha, exists beta, exists gamma,
exists lP, exists lQ, exists lR, 
exists lPQ, exists lPR, exists lQR, 
exists lP'Q', exists lP'R', exists lQ'R',
((on_line P Q gamma lPQ) /\ (on_line P' Q' gamma lP'Q')) /\
((on_line P R beta lPR) /\ (on_line P' R' beta lP'R')) /\
((on_line Q R alpha lQR) /\ (on_line Q' R' alpha lQ'R')) /\
((on_line O P P' lP) /\ (on_line O Q Q' lQ) /\(on_line O R R' lR)) /\
non_collinear P Q R /\ non_collinear P' Q' R' /\ ((P<>P')\/(Q<>Q')\/(R<>R')) /\
 (lP<>lQ /\ lP<>lR /\ lQ <> lR) /\ non_collinear alpha beta gamma.
Proof.
(* see desargues.kig for details *)
exists (P (-4) 12). (* O *)

exists (P (-8) 8). (* A *)
exists (P (-5) 8). (* B *)
exists (P (-4) 6). (* C *)

exists (P (-14) 2). (* A' *)
exists (P (-7) 0). (* B' *)
exists (P (-4) 3). (* C' *)

exists (P (-3) 4). (* alpha *)
exists (P (6/11) (38/11)). (* beta is on the right side, so on the bended line *)
exists (P (-35) 8). (* gamma *)

exists (L (Some 1) 16).  (* line OAA' *)
exists (L (Some 4) 28). (* line OBB' *)
exists (L None (-4)). (* line OCC' *)

exists (L (Some 0) 8). (* line AB *)
exists (L (Some (-1/2)) 4). (* line AC *)
exists (L (Some (-2)) (-2)). (* line BC *)

exists (L (Some (-2/7)) (-2)). (* line A'B' *)
exists (L (Some (1/10)) (34/10)).  (* line A'C' *)
exists (L (Some 1) 7). (* line B'C' *)

split.
unfold on_line; simpl; 
repeat (elim R_pos_neg; intros; try fourier); 
repeat split; try field.
split.
unfold on_line; simpl; 
repeat (elim R_pos_neg; intros; try fourier); 
repeat split; try field.
split.
unfold on_line; simpl; 
repeat (elim R_pos_neg; intros; try fourier); 
repeat split; try field.
split.
(* perspective *)
unfold on_line; simpl; 
repeat (elim R_pos_neg; intros; try fourier); 
repeat split; try field.
split.
unfold non_collinear.
intros l; case l.
intros o; case o.
intros m b; unfold on_line; simpl.
repeat (elim R_pos_neg; intros; try fourier).
intro; intuition; fourier.
intro; intuition; fourier.
intros r; unfold on_line; simpl.
repeat (elim R_pos_neg; intros; try fourier).
intro; intuition; fourier.
unfold on_line; simpl;intuition.
split.
unfold non_collinear.
intros l; case l.
intros o; case o.
intros m b; unfold on_line; simpl.
repeat (elim R_pos_neg; intros; try fourier).
intro; intuition; fourier.
intro; intuition; fourier.
intros r; unfold on_line; simpl.
repeat (elim R_pos_neg; intros; try fourier).
intro; intuition; fourier.
unfold on_line; simpl;intuition.
split.
left; intro H; inversion H.
generalize H2.
change (~8=2).
discrR.
split.
repeat split; try(intro H; inversion H).
generalize H1; change (~1=4); discrR.

unfold non_collinear.
intros l; case l.
intros o; case o.
intros m b; unfold on_line; simpl.
repeat (elim R_pos_neg; intros; try fourier).
intro; intuition.
assert ((38 /11) *11= ((2 * m * (6 /11))+b)*11).
apply (f_equal2).
assumption.
field.
replace ((38/11)*11) with 38 in H1 by field.
replace (((2*m*(6/11))+b)*11) with (12*m + 11*b) in H1 by field.
apply (foo m b); auto. (*fourier actually.*)
intros; intuition; fourier.
intros r; unfold on_line; simpl.
intro; intuition; fourier.
unfold on_line; simpl;intuition.
Qed.

End s_MoultonModel.
