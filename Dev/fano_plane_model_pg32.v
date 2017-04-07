Require Export ProjectiveGeometry.Dev.projective_space_axioms.

(** MAJOR ISSUE : WORK ONLY WITH COQ8.4pl6 **)

(**  PG(3,2). **)

(** To show that our axiom system is consistent we build a finite model. **)

Section s_fanoSpaceModelPG32.

(** PG(3,2) the smallest projective space: http://demonstrations.wolfram.com/15PointProjectiveSpace/ **)
(** 15 points and 35 lines, 15 planes **)

(** We define point and line by an inductive type representing the thirteen possibilities. **)
(** We can not use directly the inductive type for a technical reason related to Coq's implementation. **)

(* 15 points *)
Inductive Point := A | B | C | D | E | F | G | H | I | J | K | L | M | N | O.

(* 35 lines *)
Inductive Line := ABC | ADE | AFG | AHI | AKJ | ALM | ANO |   (* 7 *)
                  BEG | BIK | BMO | BHJ | BNL | BDF |         (* 13 *)
                  CHK | CLO | CDG | CMN | CEF | CIJ |         (* 19 *)
                  DKO | DIM | DJN | DHL |                     (* 23 *)
                  EJO | EIL | EKN | EHM |                     (* 27 *)
                  FIO | FHN | FJL | FKM |                     (* 31 *)
                  GHO | GIN | GJM | GKL.                      (* 35 *)

Definition Incid_bool : Point -> Line -> bool := fun P l =>
 match P with
| A =>
    match l with
    | ABC | ADE | AFG | AHI | AKJ | ALM | ANO => true
    | _ => false
    end
| B =>
    match l with
    | ABC | BEG | BIK | BMO | BHJ | BNL | BDF => true
    | _ => false
    end
| C =>
    match l with
    | ABC | CHK | CLO | CDG | CMN | CEF | CIJ => true
    | _ => false
    end
| D =>
    match l with
    | ADE | BDF | CDG | DKO | DIM | DJN | DHL => true
    | _ => false
    end
| E =>
    match l with
    | ADE | BEG | CEF | EJO | EIL | EKN | EHM => true
    | _ => false
    end
| F =>
    match l with
    | AFG | BDF | CEF | FIO | FHN | FJL | FKM => true
    | _ => false
    end
| G =>
    match l with
    | AFG | BEG | CDG | GHO | GIN | GJM | GKL => true
    | _ => false
    end
| H =>
    match l with
    | AHI | BHJ | CHK | DHL | EHM | FHN | GHO => true
    | _ => false
    end
| I => 
    match l with
    | AHI | BIK | CIJ | DIM | EIL | FIO | GIN => true
    | _ => false
    end
| J => 
    match l with
    | AKJ | BHJ | CIJ | DJN | EJO | FJL | GJM => true
    | _ => false
    end
| K =>
    match l with
    | AKJ | BIK | CHK | DKO | EKN | FKM | GKL => true
    | _ => false
    end
| L =>
    match l with
    | ALM | BNL | CLO | DHL | EIL | FJL | GKL => true
    | _ => false
    end
| M =>
    match l with
    | ALM | BMO | CMN | DIM | EHM | FKM | GJM => true
    | _ => false
    end
| N =>
    match l with
    | ANO | BNL | CMN | DJN | EKN | FHN | GIN => true
    | _ => false
    end
| O =>
    match l with
    | ANO | BMO | CLO | DKO | EJO | FIO | GHO => true
    | _ => false
    end
 end.

Lemma sub_lemma : forall T:Type, forall t:T, forall P:Prop, t<>t->P.
Proof.
solve [intuition].
Qed.

Lemma sub_lemma2 : forall P:Type, false=true -> P.
Proof.
intros P H; inversion H.
Qed.

Ltac clean := match goal with
    | H : false = true |- ?G => exact (sub_lemma2 G H)
    | H: ?A <> ?A |- ?G => exact (sub_lemma _ A G H)
    end.

(** A tactic which chooses one element and tries to solve the goal *)
Ltac solve_ex L tac := solve [exists L;abstract (tac)].
Ltac tac1 := split; exact (@refl_equal bool true).

(** A tactic which tries all possible lines **)
Ltac solve_ex_l tac :=
  first [
      solve_ex ABC tac | solve_ex ADE tac | solve_ex AFG tac | solve_ex AHI tac | solve_ex AKJ tac | solve_ex ALM tac | solve_ex ANO tac
      | solve_ex BEG tac | solve_ex BIK tac| solve_ex BMO tac | solve_ex BHJ tac | solve_ex BNL tac | solve_ex BDF tac
      | solve_ex CHK tac | solve_ex CLO tac | solve_ex CDG tac | solve_ex CMN tac | solve_ex CEF tac | solve_ex CIJ tac
      | solve_ex DKO tac | solve_ex DIM tac | solve_ex DJN tac | solve_ex DHL tac
      | solve_ex EJO tac | solve_ex EIL tac | solve_ex EKN tac | solve_ex EHM tac
      | solve_ex FIO tac | solve_ex FHN tac | solve_ex FJL tac | solve_ex FKM tac
      | solve_ex GHO tac | solve_ex GIN tac | solve_ex GJM tac | solve_ex GKL tac
].

Definition dist_3 (S:Type) (A B C  : S) : Prop := A <> B /\ A <> C /\ B <> C.

Definition dist_4 (S:Type) (A B C D :S) : Prop := 
  A <> B /\ A <> C /\ A <> D /\ B <> C /\ B <> D /\ C <> D.

Definition Incid p l := Incid_bool p l= true.

Lemma incid_dec (P:Point) (l:Line): {Incid P l} + {~Incid P l}.
Proof.
  idtac "-> proving incid_dec".
  Time (unfold Incid; destruct l; destruct P; simpl; solve [left;reflexivity | right; discriminate]).
Time Qed.
Check incid_dec.

(** A1 : existence and unicity of line generated from 2 points **)

Lemma a1_exists : forall A B : Point, {l : Line | Incid A l /\ Incid B l}.
Proof.
  idtac "-> proving a1_exists".
  Time (intros P Q; unfold Incid; destruct P; destruct Q; simpl; solve_ex_l tac1).
Time Defined.
Check a1_exists.

Lemma a1_unique:forall (A B :Point)(l1 l2:Line),
~A=B -> Incid A l1 -> Incid B l1  -> Incid A l2 -> Incid B l2 -> l1=l2.
Proof.
  idtac "-> proving a1_unique".
  Time (unfold Incid; intros X Y l1 l2 HXY H1 H2 H3 H4;
    destruct X;destruct Y; try clean;
      destruct l1; simpl in H1,H2; try clean; clear H1 H2;
        destruct l2; simpl in H3,H4; try clean; reflexivity).
Time Qed.
Check a1_unique.

Lemma a2_unique : forall(l1 l2 :Line)(A B :Point),
  ~l1=l2 -> Incid A l1 -> Incid A l2 -> Incid B l1 -> Incid B l2 -> A=B.
Proof.
  Time (unfold Incid; intros X Y l1 l2 HXY H1 H2 H3 H4;
    destruct X;destruct Y; try clean;
      destruct l1; simpl in H1,H2; try clean; clear H1 H2;
        destruct l2; simpl in H3,H4; try clean; reflexivity).
Time Qed.
Check a2_unique.

Lemma uniqueness : forall (A B :Point)(l1 l2:Line),
  Incid A l1 -> Incid B l1  -> Incid A l2 -> Incid B l2 -> A = B \/ l1 = l2.
Proof.
  idtac "-> proving uniqueness".
  Time (unfold Incid; intros P Q l1 l2 ha1 hb1 ha2 hb2;
    destruct P; destruct Q; try first [left; reflexivity | right; reflexivity];
      abstract (destruct l1;simpl in *;try clean; clear ha1 hb1; destruct l2; simpl in *; try clean; clear ha2 hb2;
        solve [left;reflexivity | right;reflexivity])).
Time Qed.
Check uniqueness.

(** A3 : dimension-related axioms *)

  (** A3_1 *)

Ltac rsplit := apply conj; [apply conj ; [idtac | apply conj ] | apply conj ; [idtac | apply conj]].

Ltac many_ex_p := match goal with
    | |- {_:Point& _} => exists A; many_ex_p
    | |- {_:Point& _} => exists B; many_ex_p
    | |- {_:Point& _} => exists C; many_ex_p 
    | |- {_:Point& _} => exists D; many_ex_p 
    | |- {_:Point& _} => exists E; many_ex_p 
    | |- {_:Point& _} => exists F; many_ex_p 
    | |- {_:Point& _} => exists G; many_ex_p 
    | |- {_:Point& _} => exists H; many_ex_p 
    | |- {_:Point& _} => exists I; many_ex_p 
    | |- {_:Point& _} => exists J; many_ex_p 
    | |- {_:Point& _} => exists K; many_ex_p 
    | |- {_:Point& _} => exists L; many_ex_p 
    | |- {_:Point& _} => exists M; many_ex_p 
    | |- {_:Point& _} => exists N; many_ex_p 
    | |- {_:Point& _} => exists O; many_ex_p
    | |- {_:Point| _} => exists A; many_ex_p
    | |- {_:Point| _} => exists B; many_ex_p
    | |- {_:Point| _} => exists C; many_ex_p 
    | |- {_:Point| _} => exists D; many_ex_p 
    | |- {_:Point| _} => exists E; many_ex_p 
    | |- {_:Point| _} => exists F; many_ex_p 
    | |- {_:Point| _} => exists G; many_ex_p 
    | |- {_:Point| _} => exists H; many_ex_p 
    | |- {_:Point| _} => exists I; many_ex_p 
    | |- {_:Point| _} => exists J; many_ex_p 
    | |- {_:Point| _} => exists K; many_ex_p 
    | |- {_:Point| _} => exists L; many_ex_p 
    | |- {_:Point| _} => exists M; many_ex_p 
    | |- {_:Point| _} => exists N; many_ex_p 
    | |- {_:Point| _} => exists O; many_ex_p
    | _ => abstract (solve [unfold Incid, dist_3; simpl; rsplit; solve [discriminate | reflexivity]])
end.

Lemma a3_1 :
  forall l:Line,{A:Point &{B:Point &{ C:Point|
  dist_3 _ A B C/\Incid A l /\Incid B l /\ Incid C l}}}.
Proof.
  idtac "-> proving a3_1".
  Time intros l; destruct l; many_ex_p.
Time Defined.
Check a3_1.

  (** A2_2 : there exists 2 lines which do not intersect *)

Ltac many_ex_l := match goal with
    | |- exists _:Line, _ => exists ABC; many_ex_l
    | |- exists _:Line, _ => exists ADE; many_ex_l
    | |- exists _:Line, _ => exists AFG; many_ex_l
    | |- exists _:Line, _ => exists AHI; many_ex_l
    | |- exists _:Line, _ => exists AKJ; many_ex_l
    | |- exists _:Line, _ => exists ALM; many_ex_l
    | |- exists _:Line, _ => exists ANO; many_ex_l

    | |- exists _:Line, _ => exists BEG; many_ex_l
    | |- exists _:Line, _ => exists BIK; many_ex_l
    | |- exists _:Line, _ => exists BMO; many_ex_l
    | |- exists _:Line, _ => exists BHJ; many_ex_l
    | |- exists _:Line, _ => exists BNL; many_ex_l
    | |- exists _:Line, _ => exists BDF; many_ex_l

    | |- exists _:Line, _ => exists CHK; many_ex_l
    | |- exists _:Line, _ => exists CLO; many_ex_l
    | |- exists _:Line, _ => exists CDG; many_ex_l
    | |- exists _:Line, _ => exists CMN; many_ex_l
    | |- exists _:Line, _ => exists CEF; many_ex_l
    | |- exists _:Line, _ => exists CIJ; many_ex_l

    | |- exists _:Line, _ => exists DKO; many_ex_l
    | |- exists _:Line, _ => exists DIM; many_ex_l
    | |- exists _:Line, _ => exists DJN; many_ex_l
    | |- exists _:Line, _ => exists DHL; many_ex_l

    | |- exists _:Line, _ => exists EJO; many_ex_l
    | |- exists _:Line, _ => exists EIL; many_ex_l
    | |- exists _:Line, _ => exists EKN; many_ex_l
    | |- exists _:Line, _ => exists EHM; many_ex_l

    | |- exists _:Line, _ => exists FIO; many_ex_l
    | |- exists _:Line, _ => exists FHN; many_ex_l
    | |- exists _:Line, _ => exists FJL; many_ex_l
    | |- exists _:Line, _ => exists FKM; many_ex_l

    | |- exists _:Line, _ => exists GHO; many_ex_l
    | |- exists _:Line, _ => exists GIN; many_ex_l
    | |- exists _:Line, _ => exists GJM; many_ex_l
    | |- exists _:Line, _ => exists GKL; many_ex_l

    | _ => solve [unfold Incid; let p:= fresh in intros p; destruct p; simpl; let h:=fresh in intro h; destruct h; discriminate]
end.

Lemma a3_2 (* dim >= 3 *) : exists l1:Line, exists l2:Line, forall p:Point, ~(Incid p l1/\Incid p l2). 
Proof.
  idtac "-> proving a3_2".
  Time many_ex_l. (* we could have chosen GKL and EHM for instance *)
Time Qed.
Check a3_2.

  (** A3_3 *)

Lemma pt_dec : forall T U:Point, {T=U}+{~T=U}.
Proof.
  intros T U; destruct T; destruct U; solve [left; reflexivity | right; discriminate].
Defined.

  (** points_from_l is actually a3_1 *)

Definition points_from_l (l:Line) := let t:= (a3_1 l) in (projT1 t, projT1 (projT2 t), proj1_sig (projT2 (projT2  t))).

Definition inter (l1 l2:Line) : option Point :=
  match (points_from_l l1) with (X,Y,Z) =>
    match (points_from_l l2) with (X',Y',Z') =>
                                  if (pt_dec X X')then Some (X) else
                                    if (pt_dec X Y') then Some (X) else
                                      if (pt_dec X Z') then Some (X) else
                                        if (pt_dec Y X') then Some (Y) else
                                          if (pt_dec Y Y') then Some (Y) else
                                            if (pt_dec Y Z') then (Some Y) else
                                              if (pt_dec Z X') then (Some Z) else
                                                if (pt_dec Z Y') then (Some Z) else
                                                  if (pt_dec Z Z') then (Some Z) else None end end.

Definition Intersect_In (l1 l2 :Line) (P:Point) := Incid P l1 /\ Incid P l2.

Ltac solve_l l l1 l2 l3 :=
  let sP1 := eval compute in (inter l l1) in
  let sP2 := eval compute in (inter l l2) in
  let sP3 := eval compute in (inter l l3) in 
  match sP1 with
    | None => fail
    | Some ?P1 => match sP2 with
           | None => fail 
           | Some ?P2 => match sP3 with
                  | None => fail
                  | Some ?P3 => solve [exists l; exists P1; exists P2; exists P3;
                                       unfold Intersect_In, Incid; split; [split ; reflexivity | split ; split; reflexivity]] end end end.

Ltac solve_ex_ll :=
  match goal with |- exists (l4 : Line) (J1 J2 J3 : Point),
      Intersect_In ?l1 l4 J1 /\
      Intersect_In ?l2 l4 J2 /\ Intersect_In ?l3 l4 J3 =>
                  first [
                      solve_l ABC l1 l2 l3| solve_l ADE l1 l2 l3 | solve_l AFG l1 l2 l3 | solve_l AHI l1 l2 l3
                      | solve_l AKJ l1 l2 l3 | solve_l ALM l1 l2 l3 | solve_l ANO l1 l2 l3 
                      | solve_l BEG l1 l2 l3 | solve_l BIK l1 l2 l3 | solve_l BMO l1 l2 l3 | solve_l BHJ l1 l2 l3
                      | solve_l BNL l1 l2 l3 | solve_l BDF l1 l2 l3
                      | solve_l CHK l1 l2 l3 | solve_l CLO l1 l2 l3 | solve_l CDG l1 l2 l3 | solve_l CMN l1 l2 l3
                      | solve_l CEF l1 l2 l3 | solve_l CIJ l1 l2 l3
                      | solve_l DKO l1 l2 l3 | solve_l DIM l1 l2 l3 | solve_l DJN l1 l2 l3 | solve_l DHL l1 l2 l3
                      | solve_l EJO l1 l2 l3 | solve_l EIL l1 l2 l3 | solve_l EKN l1 l2 l3 | solve_l EHM l1 l2 l3
                      | solve_l FIO l1 l2 l3 | solve_l FHN l1 l2 l3 | solve_l FJL l1 l2 l3 | solve_l FKM l1 l2 l3
                      | solve_l GHO l1 l2 l3 | solve_l GIN l1 l2 l3 | solve_l GJM l1 l2 l3 | solve_l GKL l1 l2 l3
  ] end.

Lemma a3_3 : forall l1 l2 l3:Line,
  dist_3 Line l1 l2 l3 -> exists l4 :Line,  exists J1:Point, exists J2:Point, exists J3:Point,
  (Intersect_In l1 l4 J1) /\ (Intersect_In l2 l4 J2) /\ (Intersect_In l3 l4 J3).
Proof.
  idtac "-> proving a3_3".
  Time (unfold dist_3; intros l1 l2 l3 (hd1,(hd2,hd3)); destruct l1; destruct l2; try clean; clear hd1; 
  abstract (destruct l3; try clean; clear hd2 hd3; solve_ex_ll)).
Time Qed.
Check a3_3.

  (** A2 : Pasch's axiom *)

  (** l_from_points is actually a1_exists *)

Definition l_from_points (Z : Point * Point) := proj1_sig (a1_exists (fst Z) (snd Z)).

Definition proj t := match t with Some t' => t' | None => A end.

Ltac findp := match goal with
  |- exists J0 : Point,
  Incid_bool J0 ?m = true /\
  Incid_bool J0 ?p = true => exists (proj (inter m p));simpl; split; reflexivity end.

Lemma points_line : forall T Z, forall x,  Incid_bool T x = true -> Incid_bool Z x =true -> T<>Z -> x=(l_from_points(T,Z)).
Proof.
  Time (intros T Z x HTx HZx HTZ;
  destruct T; destruct Z; try clean; destruct x; simpl in HTx,HZx;first [reflexivity | discriminate ]).
Time Qed.

Ltac handle x :=
  match goal with Ht: Incid_bool ?T x = _, Hz:Incid_bool ?Z x =_ |- _ =>
  let HH:= fresh in (assert (HH:x= (l_from_points(T,Z))) by (apply (points_line T Z x Ht Hz); assumption)); simpl in HH; subst x end.

Lemma a2 : forall A B C D:Point, forall lAB lCD lAC lBD :Line, 
	dist_4 _ A B C D -> 
	Incid A lAB/\Incid B lAB ->  
	Incid C lCD/\Incid D lCD -> 
	Incid A lAC/\Incid C lAC -> 
	Incid B lBD/\Incid D lBD -> 
	(exists I:Point, (Incid I lAB /\ Incid I lCD)) -> exists J:Point, (Incid J lAC /\Incid J lBD). 
Proof.
  idtac "-> proving a2".
  unfold dist_4, Incid;
  intros P Q R S l1 l2 l3 l4 (hd1,(hd2,(hd3,(hd4,(hd5,hd6))))) (hp1,hq1) (hr2,hs2) (hp3,hr3) (hq4,hs4) Ht.
  Time (destruct P; destruct Q; try clean;
          abstract (
              handle l1;
                abstract (
                    destruct R; try clean; handle l3;
                      abstract (
                          destruct S; try clean; handle l2; handle l4;
                            destruct Ht as [t (Ht1,Ht2)]; destruct t; simpl in Ht1, Ht2; try discriminate; clear Ht1 Ht2;findp)))).
Time Qed.
Check a2.

End s_fanoSpaceModelPG32.
