Require Import Setoid ssrbool ssreflect.
(*Require Import perm.*)
     
Lemma ab_bool_lr : forall a b, a && b -> a /\ b.
Proof.
  intros a b; case a; case b; intros H; inversion H; split; assumption.
Qed.

Lemma ab_bool : forall a b, a && b <-> a /\ b.
Proof.
  intros a b; split.
  apply ab_bool_lr.
  case a;case b; intros (ha,hb); solve [inversion ha | inversion hb | reflexivity].
Qed.
   
Lemma wrapperAB : forall S:Type, forall A B:S,forall le:S->S->bool, forall le_total:(forall x y:S, le x y || le y x), forall P:S-> S -> Type, forall Pwlog:(forall x y:S, le x y -> P x y), forall Psym:(forall x y:S,  P y x -> P x y),  P A B.
  Proof.
    intros S A B le le_total P Pwlog Psym; 
      destruct (Bool.orb_true_elim _ _ (le_total A B)) as [i | i];
    [exact (Pwlog _ _ i) | exact  (Psym _ _ (Pwlog _ _ i))].
  Defined.

(*Ltac revert_all_except1 x :=
  repeat match goal with
           [ H : _ |- _ ]  =>
           match H with x => fail 1 | _ => revert H end end.

Ltac revert_all_except2 x y :=
  repeat match goal with
           [ H : _ |- _ ]  =>
           match H with x => fail 1 | y=> fail 1 | _ => revert H end end.

Ltac revert_all_except3 x y  z:=
  repeat match goal with
           [ H : _ |- _ ]  =>
           match H with x => fail 1 | y => fail 1 | z => fail 1 | _ => revert H end end.
*)

Ltac wlog2 vA vB vle vle_total tac_sym tac_wlog:=
  let X:= fresh "X" in
  let Y:= fresh "Y" in
  let Xsym := fresh "Xsym" in
  let Xle := fresh "Xle" in
  pattern vA,vB; 
  match goal with vA:?ty |- (?P vA vB) =>
                  cbv beta;
                  revert vA vB; 
                  assert (Xle:forall x y:ty, vle x y -> P x y);
                  [first [tac_wlog | idtac "You have to prove " Xle "."] |
                   assert (Xsym:forall x y:ty, P y x -> P x y);
                   [first [tac_sym |  idtac "You have to prove " Xsym "."] |
                    intros X Y; apply (wrapperAB  _ X Y vle vle_total _ Xle Xsym)
                  ]]
  end.

Lemma wrapABC : forall S:Type, forall A B C:S,
      forall le:S->S->bool, forall le_total:(forall x y:S, le x y || le y x),
          forall P:S->S->S->Type,
            forall Pwlog: (forall x y z : S, le x y && le y z -> P x y z),
      (forall x y z : S, P x z y -> P x y z) ->
      (forall x y z : S, P y x z -> P x y z) ->
      (forall x y z : S, P y z x -> P x y z) ->
      (forall x y z : S, P z x y -> P x y z) ->
      (forall x y z : S, P z y x -> P x y z) ->
      P A B C.
Proof.
  intros S A B C le le_total P Pwlog Psym1 Psym2 Psym3 Psym4 Psym5;
    destruct (Bool.orb_true_elim _ _ (le_total A B)) as [i | i];
    destruct (Bool.orb_true_elim _ _ (le_total A C)) as [j | j];
    destruct (Bool.orb_true_elim _ _ (le_total B C)) as [k | k];
    [
      apply Pwlog; try rewrite i; try rewrite j; try rewrite k; reflexivity
    | apply Psym1; apply Pwlog; try rewrite i; try rewrite j; try rewrite k; reflexivity
    | apply Pwlog; try rewrite i; try rewrite j; try rewrite k; reflexivity
    | apply Psym4; apply Pwlog; try rewrite i; try rewrite j; try rewrite k; reflexivity
    | apply Psym2; apply Pwlog; try rewrite i; try rewrite j; try rewrite k; reflexivity
    | apply Psym2; apply Pwlog; try rewrite i; try rewrite j; try rewrite k; reflexivity
    | apply Psym3; apply Pwlog; try rewrite i; try rewrite j; try rewrite k; reflexivity
    | apply Psym5; apply Pwlog; try rewrite i; try rewrite j; try rewrite k; reflexivity
    ].
Qed.

Ltac wlog3 vA vB vC vle vle_total tac_sym tac_wlog :=
  let X:= fresh "A" in
  let Y:= fresh "B" in
  let Z:= fresh "C" in
  let Xsym := fresh "Xsym" in
  let Xsym1 := fresh "Xsym1" in
  let Xsym2 := fresh "Xsym2" in
  let Xle := fresh "Xle" in
  pattern vA,vB,vC; 
  match goal with vA:?ty |- (?P vA vB vC) =>
                  cbv beta;
                  revert vA vB vC;
                  assert (Xle:forall A B C:ty, vle A B && vle B C -> P A B C) ;
                  [ tac_wlog |
                    intros X Y Z; apply (wrapABC _ X Y Z vle vle_total _ Xle);clear Xle; tac_sym]
  end.
(*
Lemma l03 : 0<3.
Proof.
  auto.
Qed.

Lemma l13 : 1<3.
Proof.
  auto.
Qed.

Lemma l23 : 2<3.
Proof.
  auto.
Qed.
Inductive Point :=
| P0 | P1 | P2 | P3 | P4 | P5 | P6 | P7 | P8 | P9 | P10 | P11 | P12 | P13 | P14 .

Inductive Line :=
| L0 | L1 | L2 | L3 | L4 | L5 | L6 | L7 | L8 | L9 | L10 | L11 | L12 | L13 | L14 | L15 | L16 | L17 | L18 | L19 | L20 | L21 | L22 | L23 | L24 | L25 | L26 | L27 | L28 | L29 | L30 | L31 | L32 | L33 | L34 .


Parameter incid_lp : Point -> Line -> bool.
Parameter P:Line -> Line -> Line -> Prop.
Parameter leL:Line -> Line -> bool.
Parameter eqL:Line -> Line -> bool.
Parameter leL_total:(forall x y:Line, leL x y || leL y x).

(*  Definition f2, f4, f5 and so on... *)
Definition f3 (A:Type) (i:'I_3)  (x y z:A) : A.
case i.
intros m; case m; clear m.
intros; exact x.
intros m; case m; clear m.
intros; exact y.
intros m; case m; clear m.
intros; exact z.
intros; by [].
Defined.
Definition f3' := f3 Line.

Definition dist_3l (A B C :Line) : bool :=
    (negb (eqL A B)) && (negb (eqL A C)) && (negb (eqL B C)).

Parameter eqL_sym : forall x y, eqL x y = eqL y x.

Ltac d_tac H := revert H; repeat rewrite ab_bool; firstorder; rewrite eqL_sym; assumption.

Lemma dist_3l_ok_simple : forall x y z, dist_3l x y z -> dist_3l y z x.
Proof.
  (*unfold dist_3l;*) intros x y z H; d_tac H.
Qed.

(*Lemma dist_3l_ok_simple' : forall x y z, dist_3l x y z ->> dist_3l y z x.
Proof.
  (*unfold dist_3l;*) intros x y z; unfold dist_3l; repeat rewrite ab_bool; firstorder. d_tac H.
Qed.
*)
Lemma dist_3l_ok : forall s:'S_3, forall x y z,  dist_3l x y z -> 

                        dist_3l (f3' (s (Ordinal l03)) x y z) (f3' (s (Ordinal l13)) x y z) (f3' (s (Ordinal l23)) x y z).
Proof.
  intros s; pattern s; case s.
  intros pval; case pval.
  
  Check apermE.
case pval. intros.

  admit.


Admitted.  

(*  Definition is_inv (P:A->A->A->bool) : bool :=
  forall x y z dist_3l x y z <-> *)
Definition Intersect_In (l1 l2 :Line) (P:Point) := incid_lp P l1 && incid_lp P l2.

Definition exists_Point (f:Point -> bool) : bool :=
  f P0 || f P1 || f P2 || f P3 || f P4 || f P5 || f P6 || f P7 || f P8 || f P9 || f P10 || f P11 || f P12 || f P13 || f P14.

Definition exists_Line (f:Line -> bool) : bool :=
  f L0 || f L1 || f L2 || f L3 || f L4 || f L5 (*|| f P6 || f P7 || f P8 || f P9 || f P10 || f P11 || f P12 || f P13 || f P14*).

Lemma foo : forall a b:bool, a -> b -> a && b. 
Proof.
  intros a b; case a; case b; solve [reflexivity | discriminate].
Qed.

Lemma exists_exists_Point : forall P:Point->bool, (exists p:Point, P p) -> exists_Point P.
Proof.
unfold exists_Point; intros P x.
elim x; intros t; case t.
Admitted.
Lemma exists_exists_Line : forall P:Line->bool, (exists p:Line, P p) -> exists_Line P.
Proof.
Admitted.
Lemma exists_exists_Line2 : forall P:Line->bool,  exists_Line P -> (exists p:Line, P p).
Proof.
Admitted.

Definition forall_Line (f:Line-> bool) : bool := f L0 && f L1 && f L2 && f L3 && f L4 && f L5 && f L6 && f L7 && f L8 && f L9 && f L10 && f L11 && f L12 && f L13 && f L14 &&
f L15 && f L16 && f L17 && f L18 && f L19 && f L20 && f L21 && f L22 && f L23 && f L24 && f L25 && f L26 && f L27 && f L28 && f L29 && f L30 && f L31 && f L32 && f L33 && f L34.


Lemma a3_3 : forall v1 v2 v3:Line,
      dist_3l v1 v2 v3 -> exists v4 :Line, ( exists T1:Point, exists T2:Point, exists T3:Point,
             (Intersect_In v1 v4 T1) && (Intersect_In v2 v4 T2) && (Intersect_In v3 v4 T3)).
  Proof.
    idtac "-> proving a3_3".
    intros v1 v2 v3.
    wlog3 v1 v2 v3 leL leL_total idtac idtac.
admit.
intros.
lapply H.
(*Ltac first_order' := let H:= fresh in intros H; repeat match goal with H':exists t:_,_ |- _ => destruct H' end; revert H; repeat rewrite ab_bool.
first_order'.
firstorder. intros.
repeat match goal with H:exists t:_,_ |- _ => destruct H end.
match goal with HT:exists t:?A, ?P t |- _ => idtac "coucou" end.*)
admit.
d_tac H0.
intros; lapply H.
admit.
d_tac H0.
intros; lapply H.
admit.
d_tac H0.
intros; lapply H.
admit.
d_tac H0.
intros; lapply H.
admit.
d_tac H0.
Admitted.
(* comprendre exists et ex dans bool *)
Lemma ff : forall Q:Line->Point->bool, False -> exists p:Line, exists x:Point, Q p x.
Proof.
  intros.
Print ex.
Check is_true.
(*apply exists_exists_Line2.
Lemma xx (a b:bool) : is_true (andb a b) <-> a/\b.
Admitted.*)
(*
Definition exists_Point (f:Point -> bool) : bool :=
  f P0 || f P1 || f P2 || f P3 || f P4 || f P5 || f P6 || f P7 || f P8 || f P9 || f P10 || f P11 || f P12 || f P13 || f P14.

*)
Check ab_bool.
Lemma ttt : forall A B C:Line->Point->Point->Point->bool, exists x:Line, exists T1 T2 T3, A x T1 T2 T3 && B x T1 T2 T3 && C x T1 T2 T3 <-> exists x:Line,exists T1 T2 T3, A x T1 T2 T3 /\ B x T1 T2 T3/\ C x T1 T2 T3.
Proof.
Admitted.
(*rewrite ttt.
rewrite (ab_bool  (andb (Intersect_In x v4 T1) (Intersect_In y v4 T2))).
intros (v4, (T1, (T2, (T3 ,H')))).
exists v4; exists T1; exists T3; exists T2.
Set Printing All.
Check ab_bool.


repeat rewrite ab_bool in H'.
revert H'; repeat rewrite ab_bool; firstorder.*)
(*Lemma t : forall a b, a && b -> b && a.
  intros.
rewrite ab_bool in H.  
rewrite ab_bool in H'.
apply ab_bool.
assumption.*)



(*

match goal with |- @ex Line (fun v4 : Line => ?P v4) => idtac "coucou" end.
Set Printing All.
match goal with
    |- @ex Line
    (fun v4 : Line =>
     @ex Point
       (fun T1 : Point =>
        @ex Point
          (fun T2 : Point =>
           @ex Point
             (fun T3 : Point => ?P v4 T1 T2 T3)))) => idtac "coucou" end. exists (v4:Line)(T1 T2 T3:Point), Intersect_In x v4 T1 && Intersect_In y v4 T2 && Intersect_In z v4 T3 => idtac "coucou" end.
Ltac exchange_2last :=
  match goal with
    H:_ |- exists (P:?X), ?Y P => idtac "coucou" end.
exchange_2last.

applymodulo 
assert (dist_3l x z y).
admit.
apply H.*)
Lemma t : forall x y z:Line, P x y z.
Proof.
  intros.
  wlog3 x y z leL leL_total idtac idtac.
  admit.
  Definition w := 'I_3.
  Locate "'S_".
  Print  perm_of.
  Locate "'I_".
  Locate ordinal.
Admitted.
 
  
    
  Lemma  u:  forall s:'S_3, s (Ordinal l03) = s (Ordinal l23).
  Admitted.


Eval compute in (f3' (Ordinal l03)).
Eval compute in (f3' (Ordinal l13)).
Eval compute in (f3' (Ordinal l23)).

Lemma vt: forall s:'S_3,
      forall x y z:Line, P x y z -> 

                        P (f3' (s (Ordinal l03)) x y z) (f3' (s (Ordinal l13)) x y z) (f3' (s (Ordinal l23)) x y z).
Proof.
intros.
case s; intros; simpl.
rewrite PermDef.fun_of_permE.
simpl.
case pval.
intros t0; case t0.
intros tval; case tval.
intros; simpl.
Admitted. (*simpl.
Search _ Finfun.

unfold f3',f3; simpl.
Print Finfun.
simpl.
Search _ pval.

rewrite pvalE.
reunfold f3',f3; simpl.
Check pvalE.

(* rewrite pvalE. *)
Search _ pval.
unfold f3.

Search _ pval. 
Search _ aperm.
Admitted.
*)
Admitted.
  Admitted.
 *)

  
(* Local Variables: *)
(* coq-prog-name: "/Users/magaud/.opam/4.07.0/bin/coqtop" *)
(* coq-load-path: (("/Users/magaud/containers/theories" "Containers") ("/Users/magaud/galapagos/dev/trunk/ProjectiveGeometry/Dev" "ProjectiveGeometry.Dev")) *)
(* suffixes: .v *)
(* End: *)


