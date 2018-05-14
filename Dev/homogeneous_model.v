Require Export Reals.
Require Export Fourier.
Require Export Nsatz.
Require Export ProjectiveGeometry.Dev.projective_plane_axioms.
Require Export ProjectiveGeometry.Dev.field_variable_isolation_tactics.

Section s_HomogeneousModel.

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

(** To show that our axiom system is consistent we build a model. **)
(** Homogenous coordinates models. **)

Inductive IndPoint : Set :=
 | P2 : R -> R -> IndPoint (* (x1,x2,1) *)
 | P1 : R -> IndPoint (* (x1,1,0) *)
 | P0 : IndPoint. (* (1,0,0) *)

Inductive IndLine : Set :=
 | L2 : R -> R -> IndLine (* (x1,x2,1) *)
 | L1 : R -> IndLine (* (x1,1,0) *)
 | L0 : IndLine. (* (1,0,0) *)

Definition Point : Set := IndPoint.
Definition Line : Set := IndLine.

Definition triple_of_point  P := 
 match P with
  P2 a b => (a,b,1)
| P1 a    => (a,1,0)
| P0       => (1,0,0)
end.

Definition triple_of_line  L := 
 match L with
  L2 a b => (a,b,1)
| L1 a    => (a,1,0)
| L0       => (1,0,0)
end.

Definition point_of_triple t :=
 match t with (a,b,c) =>
  if (R_eq_dec c 0) then P2 (a/c) (b/c) else
  (if (R_eq_dec b 0) then P1 (a/b) else
  P0)
end.

Definition line_of_triple t :=
 match t with (a,b,c) =>
  if (R_eq_dec c 0) then L2 (a/c) (b/c) else
  (if (R_eq_dec b 0) then L1 (a/b) else
  L0)
end.

Lemma triple_point : forall P : Point, point_of_triple (triple_of_point P) = P.
Proof.
intros.
unfold point_of_triple, triple_of_point.
assert (1<>0).
auto with real.
elim P;intros.
elim (R_eq_dec 1 0);intros.
replace (r/ 1) with r.
replace (r0/ 1) with r0.
auto.
field.
field.
intuition.
elim (R_eq_dec 0 0);intro;intuition.
elim (R_eq_dec 1 0);intro;intuition.
replace (r/ 1) with r.
auto.
field.
elim (R_eq_dec 0 0);intro;intuition.
Qed.

Lemma point_triple : forall a b c : R, (a,b,c) <> (0,0,0) ->
exists l, l <> 0 /\ triple_of_point (point_of_triple (a,b,c)) = (a*l,b*l,c*l).
Proof.
intros.
unfold point_of_triple, triple_of_point.
elim (R_eq_dec c 0);intro.
exists (1/c).
split.
unfold not;intro.
assert (1 / c * c = 0 * c).
rewrite H0.
ring.
replace (1 / c * c) with (1) in H1.
ring_simplify in H1.
intuition.
field;assumption.

replace (a * (1 / c)) with (a/c).
replace (b * (1 / c)) with (b/c).
replace ( c * (1 / c)) with 1.
auto.
field;assumption.
field;assumption.
field;assumption.
elim (R_eq_dec b 0);intro.
exists (1/b).
split.

unfold not;intro.
assert (1 / b * b = 0 * b).
rewrite H0.
ring.
replace (1 / b * b) with (1) in H1.
ring_simplify in H1.
intuition.
field;assumption.

rewrite b0.
replace (b * (1 / b)) with 1.
replace (0 * (1 / b)) with 0.
replace (a * (1 / b)) with (a/b).
auto.
field;assumption.
field;assumption.
field;assumption.
exists (1/a).
split.
subst.
assert (a<>0).
intro;subst;intuition.

unfold not;intro.
assert (1 / a * a = 0 * a).
rewrite H1.
ring.
replace (1 / a * a) with (1) in H2.
ring_simplify in H2.
intuition.
field;assumption.

rewrite b0.
rewrite b1.
replace (a * (1 / a)) with 1.
replace (0 * (1 / a)) with 0.
auto.
assert (a<>0).
unfold not;intro.
congruence.
field;assumption.
assert (a<>0).
unfold not;intro.
congruence.
field;assumption.
Qed.

Lemma point_of_triple_functionnal: forall a b c l : R, (a,b,c) <> (0,0,0) -> l <> 0 ->
point_of_triple(a,b,c) = point_of_triple(a*l,b*l,c*l).
Proof.
intros.
unfold point_of_triple.
repeat (elim R_eq_dec;intros).
replace (a * l / (c * l)) with (a /c).
replace (b*l / (c * l)) with (b/ c).
reflexivity.
field;split;assumption.
field;split;assumption.
generalize (Rmult_integral c l b0).
intuition.
generalize (Rmult_integral c l b0).
intuition.
subst.
replace (0*l) with 0 in a1 by ring.
intuition.
replace (a * l / (b * l)) with (a/b).
reflexivity.
field;split;assumption.
generalize (Rmult_integral b l b2).
intuition.
subst.
replace (0*l) with 0 in a0 by ring.
intuition.
subst.
replace (0*l) with 0 in a0 by ring.
intuition.
reflexivity.
Qed.

Definition inner_product_triple A B :=
match (A,B) with
  ((a,b,c),(d,e,f)) => a*d+b*e+c*f 
end.

Definition Incid : Point -> Line -> Prop := fun P L =>
 inner_product_triple (triple_of_point P) (triple_of_line L) = 0.

Definition Incid_triple A B := inner_product_triple A B = 0.

Lemma incid_dec :  forall (A:Point)(l:Line), {Incid A l} + {~Incid A l}.
Proof.
intros.
unfold Incid.
generalize (R_eq_dec  (inner_product_triple (triple_of_point A) (triple_of_line l)) 0) .
intuition.
Qed.

Lemma eq_point_dec : forall A B : Point, {A[==]B} + {A<>B}.
Proof.
intros.
elim A;intros;elim B;intros; try (solve [(left; discriminate) || (right; discriminate)]).
elim (R_eq_dec r r1);intros.
right.
unfold not;intro.
inversion H.
intuition.
subst.
elim (R_eq_dec r0 r2);intros.
right.
unfold not;intro.
inversion H.
intuition.
subst.
left;auto.
elim (R_eq_dec r r0);intro.
right.
unfold not;intro.
inversion H.
intuition.
subst.
left.
intuition.
left.
trivial.
Qed.

Definition det2 a b c d := a * d - b * c.

Definition general_line_through P  Q := 
match triple_of_point P, triple_of_point Q with
 (y1,y2,y3),(z1,z2,z3) =>line_of_triple ((det2  y2 y3 z2 z3),(det2 y3 y1 z3 z1), (det2 y1 y2 z1 z2)) 
end.

(*
Definition line_through P Q := if (eq_point_dec P Q) then L0 else general_line_through P  Q.
*)

Definition general_point_through P Q :=
match triple_of_line P, triple_of_line Q with
 (y1,y2,y3),(z1,z2,z3) =>point_of_triple ((det2  y2 y3 z2 z3),(det2 y3 y1 z3 z1), (det2 y1 y2 z1 z2)) 
end.

Ltac unfold_all :=
(unfold general_point_through, general_line_through, Incid, inner_product_triple, det2, 
triple_of_point, point_of_triple, triple_of_line, line_of_triple in *).

Lemma normalize_compat_incid : forall a b c l1 l2 l3, (a,b,c) <> (0,0,0) -> Incid_triple (a,b,c) (l1,l2,l3) ->
Incid_triple (triple_of_point (point_of_triple (a,b,c))) (l1,l2,l3).
Proof.
intros.
unfold Incid_triple, inner_product_triple in *.
unfold triple_of_point, point_of_triple.
elim ( R_eq_dec c 0).
intro.
field_simplify.
replace (a * l1 + c * l3 + b * l2) with (a * l1 + b * l2 + c * l3) by ring.
rewrite H0.
field.
assumption.
assumption.
intro.
subst.
elim ( R_eq_dec b 0).
intro.
ring_simplify in H0.
field_simplify.
rewrite H0.
field.
assumption.
assumption.
intro.
subst.
ring_simplify in H0.
ring_simplify.
assert (a<>0).
intro;subst;intuition.
generalize (Rmult_integral a l1 H0).
intuition.
Qed.

Ltac ring_simplify_neq := match goal with 
H: ?X <> ?Y |- _ => (ring_simplify X Y in H)
end.

Lemma a1_exist : forall (A B : Point) ,{l:Line | Incid A l /\ Incid B l}.
Proof.
intros.
elim A.
(* Case A is P2 y1 y2 *)
intros y1 y2.
elim B.
intros z1 z2.
elim (R_eq_dec z2 y2); intro Hz2y2.

(* case z2<>y2*)
exists (general_line_through (P2 y1 y2) (P2 z1 z2)).
unfold_all.
elim (R_eq_dec (y1 * z2 - y2 * z1) 0);intros.

split.
field;assumption.
field;assumption.

elim (R_eq_dec (1 * z1 - y1 * 1) 0);intros.
split.
field_simplify.
replace (- y1 * z2 + y2 * z1) with (- (y1 * z2 - y2 * z1)) by ring.
rewrite b.

field.
replace (- y1 + z1) with (1 * z1 - y1 * 1) by ring.
intuition.
replace (z1 - y1) with (1 * z1 - y1 * 1) by ring.
intuition.
field_simplify.
replace (z1 * y2 - z2 * y1) with (- (y1 * z2 - y2 * z1)) by ring.
rewrite b.
field.
replace (z1 - y1) with (1 * z1 - y1 * 1) by ring.
intuition.
replace (z1 - y1) with (1 * z1 - y1 * 1) by ring.
intuition.
split.
ring_simplify.
ring_simplify in b.
ring_simplify in b0.
IsoleVar z1 b0.
rewrite b0 in *.
ring_simplify in b.
clear b0.

replace (y1 * z2 - y1 * y2) with (y1 *(z2-y2)) in b by ring.
elim (Rmult_integral y1 (z2 - y2) b);auto.
intro.
IsoleVar z2 H.
ring_simplify in H.
intuition.

ring_simplify.
ring_simplify in b0.
IsoleVar y1 b0.
subst.
ring_simplify in b.
replace (z1 * z2 - z1 * y2) with (z1 * (z2 - y2)) in b by ring.
elim (Rmult_integral z1 (z2 - y2) b);auto.
intro.
IsoleVar z2 H.
ring_simplify in H.
intuition.

(* Case z2 = y2 *)
subst.
unfold_all.

elim (R_eq_dec y2 0);intro Hy2.
exists (L2 0 (- (1)/y2)).
split.
field;assumption.
field;assumption.

exists (L1 0).
subst;split;ring.

intro z1.

exists (general_line_through (P2 y1 y2) (P1 z1)).
unfold_all.
elim (R_eq_dec);intro.
ring_simplify_neq.
split;field;auto.

elim (R_eq_dec  (1 * z1 - y1 * 0) 0);intros.
ring_simplify_neq.
split.
field_simplify.
replace (- y1 + y2 * z1) with (- (y1 * 1 - y2 * z1)) by ring.
rewrite b.
field;auto.
auto.
replace z1 with (1 * z1 - y1 * 0) by ring.
auto.
field_simplify.
field.
auto.
try auto. (* bizaarrre*)
split.
ring_simplify.
ring_simplify in b0.
subst.
ring_simplify in b.
auto.
ring_simplify in b0.
subst.
ring.

exists (general_line_through (P2 y1 y2) (P0)).
unfold_all.

elim (R_eq_dec (y1 * 0 - y2 * 1) 0);intro.
split.
field.
replace (y1 * 0 - y2 * 1) with (-y2) in a by ring.
auto with real.
field.
replace (y1 * 0 - y2 * 1) with (-y2) in a by ring.
auto with real.

elim (R_eq_dec  (1 * 1 - y1 * 0) 0);intro.
split.
field_simplify.
ring_simplify in b.
IsoleVar y2 b.
rewrite b.
field.
ring_simplify in b.
IsoleVar y2 b.
rewrite b.
field.
ring_simplify in b.
IsoleVar y2 b.
rewrite b.
ring_simplify in b0.
intuition.
cut False.
intuition.
intuition.
cut False.
intuition.
intuition.

(* Case A is P1 y1 *)
intro y1.

elim B.
intros z1 z2.

exists (general_line_through (P1 y1) (P2 z1 z2)).
unfold_all.

elim R_eq_dec;intro.
split.
field.
replace (y1 * z2 - z1) with (y1 * z2 - 1 * z1) by ring.
auto.
field.
replace (y1 * z2 - z1) with (y1 * z2 - 1 * z1) by ring.
auto.

elim R_eq_dec;intro.
split.
field.
replace (0 * z1 - y1 * 1) with (- y1) in a by ring.
auto with real.
field_simplify.
replace (z1 - z2 * y1) with (- (y1 * z2 - 1 * z1)) by ring.
rewrite b.
field.
replace (0 * z1 - y1 * 1) with (- y1) in a by ring.
auto with real.
replace (0 * z1 - y1 * 1) with (- y1) in a by ring.
auto with real.
split.
ring_simplify in b0.
ring_simplify in b.
ring_simplify.
IsoleVar y1 b0.
rewrite b0.
ring.
ring_simplify.
ring_simplify in b0.
IsoleVar y1 b0.
rewrite b0 in *.
ring_simplify in b.
IsoleVar z1 b.
rewrite b.
ring.

(* Case B = P1 z1 *)

intro z1.
unfold_all.

exists (L2 0 0).
split;ring.

(* Case B = P0 *)
unfold_all.
 
exists (L2 0 0).
split;ring.

(* Case A is P0 *)

elim B.

(* Case B is P2 z1 z2 *)
intros z1 z2.

exists (general_line_through (P0) (P2 z1 z2)).
unfold_all.

elim (R_eq_dec);intro.
split.
field.
replace (z2) with (1 * z2 - 0 * z1) by ring.
auto.
field.
replace (z2) with (1 * z2 - 0 * z1) by ring.
auto.

elim (R_eq_dec);intro.
split.
field.
intuition.
ring_simplify in b.
subst.
field.

split;
ring_simplify in b0;
cut False;intuition.

(* Case B is P2 z1 z2 *)
intros z1.
unfold_all.

exists (L2 0 0).
split;ring.

unfold_all.
exists (L2 0 0).
split;ring.
Qed.

Lemma a2_exist : forall (l1 l2:Line), {A:Point | Incid A l1 /\ Incid A l2}.
Proof.
intros A B.
elim A.
(* Case A is P2 y1 y2 *)
intros y1 y2.
elim B.
intros z1 z2.
elim (R_eq_dec z2 y2); intro Hz2y2.

(* case z2<>y2*)
exists (general_point_through (L2 y1 y2) (L2 z1 z2)).
unfold_all.

elim (R_eq_dec (y1 * z2 - y2 * z1) 0);intros.

split.
field;assumption.
field;assumption.

elim (R_eq_dec (1 * z1 - y1 * 1) 0);intros.
split.
field_simplify.
replace (y2 * z1 - z2 * y1) with (- (y1 * z2 - y2 * z1)) by ring.
rewrite b.
field.
replace (z1 - y1) with (1 * z1 - y1 * 1) by ring.
intuition.
replace (z1 - y1) with (1 * z1 - y1 * 1) by ring.
intuition.
field_simplify.
replace (y2 * z1 - z2 * y1) with (- (y1 * z2 - y2 * z1)) by ring.
rewrite b.
field.
replace (z1 - y1) with (1 * z1 - y1 * 1) by ring.
intuition.
replace (z1 - y1) with (1 * z1 - y1 * 1) by ring.
intuition.
split.
ring_simplify.
ring_simplify in b.
ring_simplify in b0.
IsoleVar z1 b0.
rewrite b0 in *.
ring_simplify in b.
clear b0.

replace (y1 * z2 - y1 * y2) with (y1 *(z2-y2)) in b by ring.
elim (Rmult_integral y1 (z2 - y2) b);auto.
intro.
IsoleVar z2 H.
ring_simplify in H.
intuition.

ring_simplify.
ring_simplify in b0.
IsoleVar y1 b0.
subst.
ring_simplify in b.
replace (z1 * z2 - z1 * y2) with (z1 * (z2 - y2)) in b by ring.
elim (Rmult_integral z1 (z2 - y2) b);auto.
intro.
IsoleVar z2 H.
ring_simplify in H.
intuition.

(* Case z2 = y2 *)
subst.
unfold_all.

elim (R_eq_dec y2 0);intro Hy2.
exists (P2 0 (- (1)/y2)).
split.
field;assumption.
field;assumption.

exists (P1 0).
subst;split;ring.

intro z1.

exists (general_point_through (L2 y1 y2) (L1 z1)).
unfold_all.
elim (R_eq_dec);intro.
split.
field.
replace (y1 - y2 * z1) with (y1 * 1 - y2 * z1) by ring.
auto.
field.
replace (y1 - y2 * z1) with (y1 * 1 - y2 * z1) by ring.
auto.

elim (R_eq_dec  (1 * z1 - y1 * 0) 0);intros.
split.
field_simplify.
replace (y2 * z1 - y1) with (- (y1 * 1 - y2 * z1)) by ring.
rewrite b.
field.
replace z1 with (1 * z1 - y1 * 0) by ring.
auto.
replace z1 with (1 * z1 - y1 * 0) by ring.
auto.
field_simplify.
field.
replace z1 with (1 * z1 - y1 * 0) by ring.
auto.
try (ring_simplify (1 *z1 - y1*0) in a; auto). 
split.
ring_simplify.
ring_simplify in b0.
subst.
ring_simplify in b.
auto.
ring_simplify in b0.
subst.
ring.

exists (general_point_through (L2 y1 y2) (L0)).
unfold_all.

elim (R_eq_dec (y1 * 0 - y2 * 1) 0);intro.
split.
field.

replace (y1 * 0 - y2 * 1) with (- y2) in a by ring.
auto with real.

field.
replace (y1 * 0 - y2 * 1) with (- y2) in a by ring.
auto with real.

elim (R_eq_dec  (1 * 1 - y1 * 0) 0);intro.
split.
field_simplify.
ring_simplify in b.
IsoleVar y2 b.
rewrite b.
field.
intuition.
intuition.
ring_simplify in b.
IsoleVar y2 b.
rewrite b.
field.
ring_simplify in b.
IsoleVar y2 b.
rewrite b.
ring_simplify in b0.
intuition.
cut False.
intuition.
intuition.
cut False.
intuition.
intuition.

(* Case A is P1 y1 *)
intro y1.

elim B.
intros z1 z2.

exists (general_point_through (L1 y1) (L2 z1 z2)).
unfold_all.

elim R_eq_dec;intro.
split.
field.
replace (y1 * z2 - z1) with (y1 * z2 - 1 * z1) by ring.
auto.
field.
replace (y1 * z2 - z1) with (y1 * z2 - 1 * z1) by ring.
auto.

elim R_eq_dec;intro.
split.
field.
replace ( 0 * z1 - y1 * 1) with (- y1) in a by ring.
auto with real.
field_simplify.
replace (- z2 * y1 + z1) with (- (y1 * z2 - 1 * z1)) by ring.
rewrite b.
field.
replace ( 0 * z1 - y1 * 1) with (- y1) in a by ring.
auto with real.
replace ( 0 * z1 - y1 * 1) with (- y1) in a by ring.
auto with real.
split.

ring_simplify in b0.
ring_simplify in b.
ring_simplify.
IsoleVar y1 b0.
rewrite b0.
ring.
ring_simplify.
ring_simplify in b0.
IsoleVar y1 b0.
rewrite b0 in *.
ring_simplify in b.
IsoleVar z1 b.
rewrite b.
ring.

(* Case B = P1 z1 *)

intro z1.
unfold_all.

exists (P2 0 0).
split;ring.

(* Case B = P0 *)
unfold_all.
 
exists (P2 0 0).
split;ring.

(* Case A is P0 *)

elim B.

(* Case B is P2 z1 z2 *)
intros z1 z2.

exists (general_point_through (L0) (L2 z1 z2)).

unfold_all.

elim (R_eq_dec);intro.
split.
field.
replace (z2) with (1 * z2 - 0 * z1) by ring.
auto.
field.
replace (z2) with (1 * z2 - 0 * z1) by ring.
auto.

elim (R_eq_dec);intro.
split.
field.
intuition.
ring_simplify in b.
subst.
field.

split;
ring_simplify in b0;
cut False;intuition.

(* Case B is P2 z1 z2 *)
intros z1.
unfold_all.

exists (P2 0 0).
split;ring.

unfold_all.
exists (P2 0 0).
split;ring.
Qed.


Lemma a3_1 : 
  (forall l:Line,{A:Point & {B:Point & {C:Point | (~A[==]B /\ ~A[==]C /\ ~B[==]C /\Incid A l /\Incid B l /\ Incid C l)}}}).
Proof.
intro.
case l.
intros x1 x2.
elim (R_eq_dec x1 0);intro.
elim (R_eq_dec x2 0);intro.

exists (P2 ((0- 1) / x1) 0).
exists (P2 0 ((0- 1) / x2)).
exists (P1 (- x2 / x1)).
repeat split.
intro H; inversion H.

assert ((0 - 1) / x1 * x1 = 0-1).
field;auto.
rewrite H1 in H0.
ring_simplify in H0.
auto with field_hints.

intro H;inversion H.
intro H;inversion H.

unfold_all;field;assumption.
unfold_all;field;assumption.
unfold_all;field;assumption.

exists (P2 (- (1) / x1) (1)).
exists (P2 (- (1) / x1) (0)).
exists (P2 (- (1) / x1) (2)).

repeat split;(intro H; inversion H;auto with real field_hints) || (subst;unfold_all;field;assumption).

assert (0 <> 2);auto with real.

elim (R_eq_dec x2 0);intro.

exists (P2  1 (- (1) / x2)).
exists (P2  0 (- (1) / x2)).
exists (P2  2 (- (1) / x2)).
repeat split;(intro H; inversion H;auto with real field_hints) || (subst;unfold_all;field;assumption).

assert (0 <> 2);auto with real.

exists (P1  2 ).
exists (P1  0 ).
exists (P1  1 ).

repeat split;(intro H; inversion H;auto with real field_hints) || (subst;unfold_all;field;assumption).

assert (0 <> 2);auto with real.

intro x1.

exists (P2 0 0).
elim (R_eq_dec x1 0);intro.

exists (P1 (- (1) / x1)).
exists (P2 (- (1) / x1) 1).

repeat split;(intro H; inversion H;auto with real field_hints) || (subst;unfold_all;field;assumption).

exists (P2 1 0).
exists (P2 2 0).

repeat split;(intro H; inversion H;auto with real field_hints) || (subst;unfold_all;field;assumption).

assert (0 <> 2);auto with real.

exists (P2 0 1).
exists (P2 0 0).
exists (P2 0 2).

repeat split;(intro H; inversion H;auto with real field_hints) || (subst;unfold_all;field;assumption).

assert (0<>2);auto with real.

Qed.

Lemma a3_2 : {l1:Line & {l2:Line | l1 <> l2}}.
Proof.
exists L0.
exists (L1 0).
intro H;inversion H.
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

Lemma eq_2 : forall X1 X2 Y1 Y2, 
P2 X1 X2 = P2 Y1 Y2 <-> (X1 = Y1 /\ X2 = Y2).
Proof.
intros X1 X2 Y1 Y2.
injection_equiv.
Qed.

Lemma eq_1 : forall X Y, 
P1 X = P1 Y <-> X = Y.
intros.
injection_equiv.
Qed.

Ltac reduce_prop :=  
match goal with
| H: _ |- context [?X = ?Y] => replace_cons X Y
| H: _ |- context [?X = 0 /\ ?Y=0] => setoid_replace (X = 0 /\ Y=0) with (X*X + Y*Y = 0) by apply equiv_and
| H: _ |- context [?X = 0 \/ ?Y=0] => setoid_replace (X = 0 \/ Y=0) with (X*Y = 0) by apply equiv_or
| H: _ |- context [(P1 ?X1 = P1 ?Y1)] => setoid_replace (P1 X1 = P1 Y1) with (X1 = Y1) by try injection_equiv
| H: _ |- context [(L1 ?X1 = L1 ?Y1)] => setoid_replace (L1 X1 = L1 Y1) with (X1 = Y1) by try injection_equiv

| H: _ |- context [(?P ?X1 ?X2 = ?P ?Y1 ?Y2)] => 
   setoid_replace (P X1 X2 = P Y1 Y2) with (X1 = Y1 /\ X2 = Y2) 
  by let H := fresh in (split;intro H;[inversion H;auto | decompose [and] H;subst;auto])
| H: _  |- context [P2 ?X ?Y = P1 ?Z] => setoid_replace (P2 X Y = P1 Z) with False by try (intuition;discriminate)
| H: _  |- context [P2 ?X ?Y = P0] => setoid_replace (P2 X Y = P0) with False by try (intuition;discriminate)
| H: _  |- context [P1 ?X = P0] => setoid_replace (P1 X = P0) with False by try (intuition;discriminate)
| H: _  |- context [L2 ?X ?Y = L1 ?Z] => setoid_replace (L2 X Y = L1 Z) with False by try (intuition;discriminate)
| H: _  |- context [L2 ?X ?Y = L0] => setoid_replace (L2 X Y = L0) with False by try (intuition;discriminate)
| H: _  |- context [L1 ?X = L0] => setoid_replace (L1 X = L0) with False by try (intuition;discriminate)

| H: _  |- context [P1 ?Z = P2 ?X ?Y] => setoid_replace (P1 Z = P2 X Y) with False by try (intuition;discriminate)
| H: _  |- context [P0 = P2 ?X ?Y] => setoid_replace (P0 = P2 X Y) with False by try (intuition;discriminate)
| H: _  |- context [P0 = P1 ?X] => setoid_replace (P0 = P1 X) with False by try (intuition;discriminate)
| H: _  |- context [L1 ?Z = L2 ?X ?Y] => setoid_replace (L1 Z = L2 X Y) with False by try (intuition;discriminate)
| H: _  |- context [L0 = L2 ?X ?Y] => setoid_replace (L0 = L2 X Y) with False by try (intuition;discriminate)
| H: _  |- context [L0 = L1 ?X] => setoid_replace (L0 = L1 X) with False by try (intuition;discriminate)

| H: _  |- context [L0 = L0] => setoid_replace (L0 = L0) with True by try (split;auto)
| H: _  |- context [P0 = P0] => setoid_replace (P0 = P0) with True by try (split;auto)

| H: _  |- context [?P \/ False] => setoid_replace (P \/ False) with (P) by try intuition
| H: _  |- context [False \/ ?P] => setoid_replace (False \/ P) with (P) by try intuition

| H: _  |- context [?P \/ True] => setoid_replace (P \/ True) with (True) by try intuition
| H: _  |- context [True \/ ?P] => setoid_replace (True \/ P) with (True) by try intuition
end.

Ltac normalize_prop := repeat reduce_prop.

Ltac simplify_eqs eq1 eq2 eq3 eq4 := 
  ring_simplify in eq1;try subst;
  ring_simplify in eq2;try subst;
  ring_simplify in eq3;try subst;
  ring_simplify in eq4;try subst.

Lemma triple_of_point_carac : forall A,
 let '(a,b,c) := triple_of_point A in
 (c=1 \/ c=0) /\
 (c=1 \/ b=1 \/ b=0) /\
 (c=1 \/ b=1 \/ a=1).
Proof.
 destruct A; simpl; intuition.
Qed.

Lemma triple_of_point_carac' : forall A,
 let '(a,b,c) := triple_of_point A in
 (c-1)*c=0 /\
 (c-1)*(b-1)*b=0 /\
 (c-1)*(b-1)*(a-1)=0.
Proof.
 intros A.
 generalize (triple_of_point_carac A).
 destruct triple_of_point as ((a,b),c).
 rewrite <- !equiv_or, <- !equiv_eq. intuition.
Qed.

Lemma triple_of_line_carac : forall l,
 let '(a,b,c) := triple_of_line l in
 (c=1 \/ c=0) /\
 (c=1 \/ b=1 \/ b=0) /\
 (c=1 \/ b=1 \/ a=1).
Proof.
 destruct l; simpl; intuition.
Qed.

Lemma triple_of_line_carac' : forall l,
 let '(a,b,c) := triple_of_line l in
 (c-1)*c=0 /\
 (c-1)*(b-1)*b=0 /\
 (c-1)*(b-1)*(a-1)=0.
Proof.
 intros l.
 generalize (triple_of_line_carac l).
 destruct triple_of_line as ((a,b),c).
 rewrite <- !equiv_or, <- !equiv_eq. intuition.
Qed.

Lemma pair_eq : forall A B (a a':A)(b b':B),
 (a,b) = (a',b') <-> a=a' /\ b=b'.
Proof.
 intros.
 split. injection 1; split; trivial.
 destruct 1; subst; trivial.
Qed.

Lemma triple_of_point_inj : forall A B,
 triple_of_point A = triple_of_point B <-> A [==] B.
Proof.
 intros. split; intros.
 rewrite <- (triple_point A), <- (triple_point B). rewrite H.
reflexivity.
rewrite H;reflexivity.
Qed.

Lemma triple_of_line_inj : forall l m,
 triple_of_line l = triple_of_line m <-> l = m.
Proof.
 destruct l, m; unfold_all; simpl; rewrite !pair_eq;
  intuition; subst; try congruence; exfalso; auto with real.
Qed.

Lemma uniqueness : forall A B :Point, forall l m : Line,
 Incid A l -> Incid B l  -> Incid A m -> Incid B m -> A[==]B \/ l=m.
Proof.
intros A B l m. intros.
unfold Incid in *.
rewrite <- triple_of_point_inj, <- triple_of_line_inj.
generalize (triple_of_point_carac' A)(triple_of_point_carac' B)
 (triple_of_line_carac' l)(triple_of_line_carac' m).
destruct (triple_of_point A) as ((a1,a2),a3).
destruct (triple_of_point B) as ((b1,b2),b3).
destruct (triple_of_line l) as ((l1,l2),l3).
destruct (triple_of_line m) as ((m1,m2),m3).
intros (EQa3 & EQa2 & EQa1).
intros (EQb3 & EQb2 & EQb1).
intros (EQl3 & EQl2 & EQl1).
intros (EQm3 & EQm2 & EQm1).
unfold_all.
rewrite !pair_eq.
normalize_prop.
nsatz.
Qed.

End s_HomogeneousModel.
