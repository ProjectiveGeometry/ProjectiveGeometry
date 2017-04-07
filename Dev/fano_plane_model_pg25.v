Require Export ProjectiveGeometry.Dev.projective_plane_axioms.

(*** PG(2,5)'s plane ***)

(** To show that our axiom system is consistent we build another finite model. **)
(** This model is harder to build than Fano plane because this creates proof 
with more than 900 000 cases **)

Section s_fanoPlaneModelPG25.

(* We define point and line by an inductive type representing the 31 possibilities *)
(* We can not use directly the inductive type for 
  a technical reason related to Coq's implementation. *)

Inductive ind_point : Set := P0 | P1 | P2 | P3 | P4 | P5 | P6 | P7 | P8 | P9
                                        | P10 | P11 | P12 | P13 | P14 | P15 | P16 | P17 | P18 | P19
                                        | P20 | P21 | P22 | P23 | P24 | P25 | P26 | P27 | P28 | P29 | P30.

Inductive ind_line    : Set :=  l0 | l1 | l2 | l3 | l4 | l5 | l6 | l7 | l8 | l9
                                        | l10 | l11 | l12 | l13 | l14 | l15 | l16 | l17 | l18 | l19
                                        | l20 | l21 | l22 | l23 | l24 | l25 | l26 | l27 | l28 | l29 | l30.

Definition Point : Set := ind_point.
Definition Line : Set := ind_line.

Definition Incid_bool : Point -> Line -> bool := fun P L =>
 match (P,L) with
  (P0, l0) | (P0, l1) | (P0,l3) | (P0,l8) | (P0,l12) | (P0, l18)
| (P1, l30) | (P1, l0) | (P1,l2) | (P1,l7) | (P1,l11) | (P1, l17)
| (P2, l29) | (P2, l30) | (P2,l1) | (P2,l6) | (P2,l10) | (P2, l16)
| (P3, l28) | (P3, l29) | (P3,l0) | (P3,l5) | (P3,l9) | (P3, l15)
| (P4, l27) | (P4, l28) | (P4,l30) | (P4,l4) | (P4,l8) | (P4, l14)
| (P5, l26) | (P5, l27) | (P5,l29) | (P5,l3) | (P5,l7) | (P5, l13)
| (P6, l25) | (P6, l26) | (P6,l28) | (P6,l2) | (P6,l6) | (P6, l12)
| (P7, l24) | (P7, l25) | (P7,l27) | (P7,l1) | (P7,l5) | (P7, l11)
| (P8, l23) | (P8, l24) | (P8,l26) | (P8,l0) | (P8,l4) | (P8, l10)
| (P9, l22) | (P9, l23) | (P9,l25) | (P9,l30) | (P9,l3) | (P9, l9) 
| (P10, l21) | (P10, l22) | (P10,l24) | (P10,l29) | (P10,l2) | (P10, l8)
| (P11, l20) | (P11, l21) | (P11,l23) | (P11,l28) | (P11,l1) | (P11, l7)
| (P12, l19) | (P12, l20) | (P12,l22) | (P12,l27) | (P12,l0) | (P12, l6)
| (P13, l18) | (P13, l19) | (P13,l21) | (P13,l26) | (P13,l30) | (P13, l5)
| (P14, l17) | (P14, l18) | (P14,l20) | (P14,l25) | (P14,l29) | (P14, l4)
| (P15, l16) | (P15, l17) | (P15,l19) | (P15,l24) | (P15,l28) | (P15, l3)
| (P16, l15) | (P16, l16) | (P16,l18) | (P16,l23) | (P16,l27) | (P16, l2)
| (P17, l14) | (P17, l15) | (P17,l17) | (P17,l22) | (P17,l26) | (P17, l1)
| (P18, l13) | (P18, l14) | (P18,l16) | (P18,l21) | (P18,l25) | (P18, l0)
| (P19, l12) | (P19, l13) | (P19,l15) | (P19,l20) | (P19,l24) | (P19, l30)
| (P20, l11) | (P20, l12) | (P20,l14) | (P20,l19) | (P20,l23) | (P20, l29)
| (P21, l10) | (P21, l11) | (P21,l13) | (P21,l18) | (P21,l22) | (P21, l28)
| (P22, l9) | (P22, l10) | (P22,l12) | (P22,l17) | (P22,l21) | (P22, l27)
| (P23, l8) | (P23, l9) | (P23,l11) | (P23,l16) | (P23,l20) | (P23, l26)
| (P24, l7) | (P24, l8) | (P24,l10) | (P24,l15) | (P24,l19) | (P24, l25)
| (P25, l6) | (P25, l7) | (P25,l9) | (P25,l14) | (P25,l18) | (P25, l24)
| (P26, l5) | (P26, l6) | (P26,l8) | (P26,l13) | (P26,l17) | (P26, l23)
| (P27, l4) | (P27, l5) | (P27,l7) | (P27,l12) | (P27,l16) | (P27, l22)
| (P28, l3) | (P28, l4) | (P28,l6) | (P28,l11) | (P28,l15) | (P28, l21)
| (P29, l2) | (P29, l3) | (P29,l5) | (P29,l10) | (P29,l14) | (P29, l20)
| (P30, l1) | (P30, l2) | (P30,l4) | (P30,l9) | (P30,l13) | (P30, l19)
  => true
| _ => false
end.

Definition Incid : Point -> Line -> Prop := fun P L => (Incid_bool P L =true).

Hint Unfold Incid Incid_bool.

Lemma incid_dec : forall (A:Point)(l:Line), {Incid A l} + {~Incid A l}.
Proof.
intros.
unfold Incid.
elim l;elim A;unfold Incid_bool;simpl;auto;right;discriminate.
Qed.

(* A1 : any two points lie on a unique line *) 

Ltac solve_ex L := solve [exists L;auto].

Ltac solve_line := first [solve_ex l0 | solve_ex l1  |  solve_ex l2  |  solve_ex l3  |  solve_ex l4  |  solve_ex l5  |  solve_ex l6  |  solve_ex l7 | solve_ex l8  |  solve_ex l9 
      | solve_ex l10 | solve_ex l11  |  solve_ex l12  |  solve_ex l13  |  solve_ex l14  |  solve_ex l15  |  solve_ex l16  |  solve_ex l17 | solve_ex l18  |  solve_ex l19 
      | solve_ex l20 | solve_ex l21  |  solve_ex l22  |  solve_ex l23  |  solve_ex l24  |  solve_ex l25  |  solve_ex l26  |  solve_ex l27 | solve_ex l28  |  solve_ex l29 
      | solve_ex l30
 ].

Ltac solve_point := first [solve_ex P0 | solve_ex P1  |  solve_ex P2  |  solve_ex P3  |  solve_ex P4  |  solve_ex P5  |  solve_ex P6  |  solve_ex P7 | solve_ex P8  |  solve_ex P9 
      | solve_ex P10 | solve_ex P11  |  solve_ex P12  |  solve_ex P13  |  solve_ex P14  |  solve_ex P15  |  solve_ex P16  |  solve_ex P17 | solve_ex P18  |  solve_ex P19 
      | solve_ex P20 | solve_ex P21  |  solve_ex P22  |  solve_ex P23  |  solve_ex P24  |  solve_ex P25  |  solve_ex P26  |  solve_ex P27 | solve_ex P28  |  solve_ex P29 
      | solve_ex P30
 ].

Lemma a1_exist : forall ( A B :Point) ,{l:Line | Incid A l /\ Incid B l}.
Proof.
intros.
elim A;elim B; solve_line.
Qed.

Ltac tac l m := abstract (induction l;try discriminate;induction m;try discriminate;reflexivity).

(* A2 : any two lines meet in a unique point *)
Lemma a2_exist : forall (l m:Line), {A:Point | Incid A l /\ Incid A m}.
Proof.
intros.
induction l;induction m;solve_point.
Qed.

Ltac tac' H l m := abstract ( induction l;try discriminate;induction m;try (elim H;reflexivity); reflexivity || (unfold Incid, Incid_bool in *;discriminate)).

Lemma uniqueness : forall A B :Point, forall l m : Line,
 Incid A l -> Incid B l  -> Incid A m -> Incid B m -> A=B\/l=m.
Proof.
intros.
induction A; induction B; try (left; reflexivity); try (right; reflexivity);
try (left; tac l m); try (right; tac l m).
Qed.

(* A3 : there exist four points with no three collinear *)
Lemma a3: {A:Point & {B :Point & {C:Point & {D :Point |
  (forall l :Line, A <> B /\ A <> C /\ A <> D /\ B <> C /\ B <> D /\ C <> D /\
    (Incid A l /\ Incid B l -> ~Incid C l /\ ~Incid D l)
    /\ (Incid A l /\ Incid C l -> ~Incid B l /\ ~Incid D l)
    /\  (Incid A l /\ Incid D l -> ~Incid C l /\ ~Incid B l)
    /\  (Incid C l /\ Incid B l -> ~Incid A l /\ ~Incid D l)
    /\ (Incid D l /\ Incid B l -> ~Incid C l /\ ~Incid A l)
    /\  (Incid C l /\ Incid D l -> ~Incid B l /\ ~Incid A l))}}}}.
Proof.
exists P0.
exists P1.
exists P2.
exists P5.
intros.
split.
intuition;discriminate.
elim l;unfold Incid, Incid_bool;intuition;try discriminate.
Qed.

End s_fanoPlaneModelPG25.