Require Import ords all_ssreflect pg3x_spec pg32_ind pg32_spec.

Module PS : ProjectiveSpace.

  Definition Point := Point. (*[eqType of Point].*)
  Definition Line := Line. (*[eqType of Line].*)

  Definition incid_lp (x:Point) (l:Line) : bool := incid_lp x l.
  
  Definition eqP (x y:Point) := x==y.
  Definition eqL (l m :Line) := l==m.

  (** a1_exists : existence of a line generated from 2 points *)

  Lemma symAB : forall A B:Point,
      {l : Line |  incid_lp A l && incid_lp B l} ->
      {l : Line |  incid_lp B l && incid_lp A l}.
  Proof.
    intros A B X.
    exists (projT1 X).
    abstract (destruct X; rewrite Bool.andb_comm; assumption).
  Defined.

  Lemma wrapAB : forall A B:Point,forall P:Point-> Point-> Type,
        (forall x y:Point, x <= y -> P x y) -> (forall x y:Point,  y<=x -> P x y) -> P A B.
  Proof.
    intros A B;
      destruct (Bool.orb_true_elim _ _ (leq_total A B)) as [i | i];
    [intros P X1 X2; exact (X1 _ _ i) | intros P X1 X2; exact (X2 _ _ i)].
  Defined.

  Lemma wraplm : forall A B:Line,forall P:Line -> Line -> Type,
        (forall x y:Line, x<=y -> P x y) -> (forall x y:Line,  y<=x -> P x y) -> P A B.
  Proof.
     intros A B;
       destruct (Bool.orb_true_elim _ _ (leq_total A B)) as [i | i]; 
     [intros P X1 X2; exact (X1 _ _ i) | intros P X1 X2; exact (X2 _ _ i)].
  Defined.

  Ltac wrap_it_completely tac :=
    let A:= fresh "A" in
    let B:= fresh "B" in
    let Xsym := fresh "Xsym" in
    let Xle := fresh "Xle" in
    intros A B;
    pattern A,B; 
    match goal with A:?ty |- (?P A B) =>
                    cbv beta;
                    revert A B;
                    assert (Xle:forall A B:ty, A<=B -> P A B) ; [tac |
                    assert (Xsym:forall x y:ty, P x y -> P y x);
                    [idtac |
                     intros A B; apply (wrapAB A B) || apply (wraplm A B);
                     [ (exact Xle)
                     | repeat (intro; try solve [ apply Xsym; apply Xle; assumption])
                     ]
                    ]]
    end.
  
  Ltac prove_a1_exists :=
    let P:=fresh in
    let Q:=fresh in
    intros P Q; elim P using Point_rect; elim Q using Point_rect;intros hypp hypq;
    try_all_l ltac:(fun L => (solve [apply (exist _ L); exact (@erefl bool true)])).
  
  Lemma a1_exists : forall A B : Point,
      {l : Line | incid_lp A l && incid_lp B l}.
  Proof.
    idtac "-> proving a1_exists".
    Time (prove_a1_exists). 
    Time Defined.
  Check a1_exists.
  
  (** a3_1 : every line has at least three distinct points *)
  
  Ltac final_a3_1 := abstract (exact (@erefl bool true)).

  Ltac prove_a3_1 :=
    let l:= fresh in
    intros l; elim l using Line_rect; intros hi;
    try_all_p ltac:(fun A => apply (existT _ A);
    try_all_p ltac:(fun B => apply (existT _ B);
    try_all_p ltac:(fun C => apply (exist _ C); final_a3_1))).

  Definition dist_3p  (A B C :Point) : bool :=
    (negb (eqP A B)) && (negb (eqP A C)) && (negb (eqP B C)).

  Lemma a3_1 : 
    forall l:Line,{A:Point &{B:Point &{ C:Point| 
        dist_3p A B C && (incid_lp A l && incid_lp B l && incid_lp C l)}}}.
  Proof.
    idtac "-> proving a3_1".
    Time (prove_a3_1).
    Time Defined.

  (** a1_unique : unicity of the line generated from 2 points *)

  (** l_from_points is actually a1_exists *)
  
  Definition l_from_points (Z : Point * Point) := proj1_sig (a1_exists (fst Z) (snd Z)).

  Lemma points_line : forall T Z:Point, forall x:Line,
        incid_lp T x -> incid_lp Z x -> T!=Z -> x = (l_from_points(T,Z)).
  Proof.
    idtac "-> proving points_line".
    Time (intros T Z x;
            elim x using Line_rect; intros hypx;
              elim T using Point_rect; intros hypt HTx;
                solve [ remove_cases | 
                        elim Z using Point_rect; intros hypz HZx HTZ;
                          solve [ remove_cases
                                | apply val_inj; exact (@erefl nat _)]]).
    Time Qed.
  Check points_line.
        
  Ltac handle x :=
    match goal with Ht  : is_true (incid_lp ?T x),
                    Hz  : is_true (incid_lp ?Z x),
                    Htz: is_true (?T!=?Z) |- _ => 
                    pose proof (points_line T Z x Ht Hz Htz); clear Ht Hz; subst end.

  Ltac prove_a1_unique' :=
    let A:=fresh in
    let B:= fresh in
    let HAB' := fresh in 
    let l1:=fresh in
    let l2:=fresh in
    let HAB:=fresh in
    let HAl1:=fresh in
    let HBl1:= fresh in
    let HAl2 := fresh in
    let HBl2 := fresh in
    intros A B HAB' l1 l2 HAB HAl1 HBl1 HAl2 HBl2;
    revert A B HAB' HAB l1 HAl1 HBl1 l2 HAl2 HBl2;
    intros  X; elim X using Point_rect;
    intros hypx Y;elim Y using Point_rect; intros hypy HAB' HAB;
    solve [remove_cases | 
           intros l1 HAl1 HBl1; handle l1; 
           intros l2 HAl2 HBl2; handle l2;
           exact (@erefl Line _)].
  
  Lemma a1_unique:forall (A B :Point)(l1 l2:Line),
      A!=B -> incid_lp A l1 -> incid_lp B l1  -> incid_lp A l2 -> incid_lp B l2 -> l1=l2.
  Proof.
    idtac "-> proving a1_unique".
    Time (
        wrap_it_completely prove_a1_unique';
    intros; apply H; try assumption; rewrite eq_sym; assumption).
    Time Qed.
  Check a1_unique.
  
  Lemma Point_dec : forall T U:Point, {T=U}+{T!=U}.
  Proof.
    intros T U; elim T using Point_rect; intros hypT; elim U using Point_rect;
      intros hypU; solve [left; apply:val_inj; exact (@erefl _ _) | 
                          right;apply/negP; intro H; inversion H].
  Defined.
  
  Ltac prove_uniqueness :=
    let P:= fresh in
    let hypP := fresh in
    let HPQdiff := fresh in 
    let Q:= fresh in
    let hypQ := fresh in
    let HPQ := fresh in 
    let l := fresh in
    let m := fresh in 
    intros P Q;
    destruct (Point_dec P Q) as [HPQdiff | HPQdiff];
    [left; subst P; exact (@erefl Point _) | idtac];
    revert P Q HPQdiff;
    intros P; elim P using Point_rect;
    intros hypP Q; elim Q using Point_rect; intros hypQ HPQdiff HPQ;
    solve [remove_cases |  
    intros l m Hl Hl'; revert m; handle l; 
    intros m Hm Hm'; handle m;  right; exact (@erefl Line _)].

  Lemma uniqueness : forall (A B :Point)(l1 l2:Line),
      incid_lp A l1 -> incid_lp B l1  -> incid_lp A l2 -> incid_lp B l2 -> A = B \/ l1 = l2.
  Proof.
    idtac "-> proving uniqueness".
    Time(wrap_it_completely (prove_uniqueness);
    intros; assert (foo:x=y\/l1=l2->y=x\/l1=l2) by (intros; solve [intuition]);
      apply foo; apply H; assumption).
    Time Qed.
  Check uniqueness.
  
  (** a3_2 : there exists 2 lines which do not intersect, i.e. dim >= 3  *)

  Ltac solve_a3_2 := let p:= fresh in
                     intros p; elim p using Point_rect;
                     let hypp:=fresh in let t := fresh in intros hypp t; discriminate.

  Ltac prove_a3_2 := try_all_l ltac:(fun l1 => exists l1; try_all_l ltac:(fun l2 => exists l2; solve_a3_2)).
  
  Lemma a3_2 : exists l1:Line, exists l2:Line, forall p:Point, ~(incid_lp p l1 && incid_lp p l2). 
  Proof.
    idtac "-> proving a3_2".
    time (prove_a3_2). (* we could have chosen (o 35 0) and (o 35 34). *)
    Time Qed.
  Check a3_2.

  (* a3_3 : given 3 lines, there exists a line which intersects these 3 lines *)

  (** points_from_l is actually a3_1 *)
  
  Definition points_from_l (l:Line) :=
    let t:= (a3_1 l) in (projT1 t, projT1 (projT2 t), proj1_sig (projT2 (projT2  t))).

  Definition inter (l1 l2:Line) : option Point :=
    match (points_from_l l1) with (X,Y,Z) =>
      match (points_from_l l2) with (X',Y',Z') =>
              if (Point_dec X X') then Some (X) else
                if (Point_dec X Y') then Some (X) else
                  if (Point_dec X Z') then Some (X) else
                    if (Point_dec Y X') then Some (Y) else
                      if (Point_dec Y Y') then Some (Y) else
                        if (Point_dec Y Z') then (Some Y) else
                          if (Point_dec Z X') then (Some Z) else
                            if (Point_dec Z Y') then (Some Z) else
                              if (Point_dec Z Z') then (Some Z) else None end end.

  Definition Intersect_In (l1 l2 :Line) (P:Point) := incid_lp P l1 && incid_lp P l2.

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
                  | Some ?P3 => solve [apply (ex_intro _ l); apply (ex_intro _ P1);
                                       apply (ex_intro _ P2); apply (ex_intro _ P3);
                                       exact (@erefl bool true)]
                                              end end end.

  Ltac solve_ex_ll :=
    match goal with |- exists (l4 : _) (J1 J2 J3 : _),
        is_true (Intersect_In ?l1 l4 J1 &&
        Intersect_In ?l2 l4 J2 && Intersect_In ?l3 l4 J3) => try_all_l ltac:(fun L => solve_l L l1 l2 l3) end.

  Lemma wrapABC : forall (A B C: Point) (P : Point -> Point -> Point -> Type),
      (forall x y z : Point, x <= y <= z -> P x y z) ->
      (forall x y z : Point, x <= z <= y -> P x y z) ->
      (forall x y z : Point, y <= x <= z -> P x y z) ->
      (forall x y z : Point, y <= z <= x -> P x y z) ->
      (forall x y z : Point, z <= x <= y -> P x y z) ->
      (forall x y z : Point, z <= y <= x -> P x y z) ->
      P A B C.
  Proof.
    intros A B C;
      destruct (Bool.orb_true_elim _ _ (leq_total A B)) as [i | i];
      destruct (Bool.orb_true_elim _ _ (leq_total A C)) as [j | j];
      destruct (Bool.orb_true_elim _ _ (leq_total B C)) as [k | k];
      [ intros P X1 X2 X3 X4 X5 X6;apply X1; apply andb_true_intro; split; assumption
      | intros P X1 X2 X3 X4 X5 X6;apply X2; apply andb_true_intro; split; assumption
      | intros P X1 X2 X3 X4 X5 X6;apply X4; apply andb_true_intro; split; assumption
      | intros P X1 X2 X3 X4 X5 X6;apply X5; apply andb_true_intro; split; assumption
      | intros P X1 X2 X3 X4 X5 X6;apply X3; apply andb_true_intro; split; assumption
      | intros P X1 X2 X3 X4 X5 X6;apply X6; apply andb_true_intro; split; assumption
      | intros P X1 X2 X3 X4 X5 X6;apply X4; apply andb_true_intro; split; assumption
      | intros P X1 X2 X3 X4 X5 X6;apply X6; apply andb_true_intro; split; assumption].
  Qed.
  
  Lemma wraplmp : forall (A B C: Line) (P : Line -> Line -> Line -> Type),
      (forall x y z : Line, x <= y <= z -> P x y z) ->
      (forall x y z : Line, x <= z <= y -> P x y z) ->
      (forall x y z : Line, y <= x <= z -> P x y z) ->
      (forall x y z : Line, y <= z <= x -> P x y z) ->
      (forall x y z : Line, z <= x <= y -> P x y z) ->
      (forall x y z : Line, z <= y <= x -> P x y z) ->
      P A B C.
  Proof.
    intros A B C;
      destruct (Bool.orb_true_elim _ _ (leq_total A B)) as [i | i];
      destruct (Bool.orb_true_elim _ _ (leq_total A C)) as [j | j];
      destruct (Bool.orb_true_elim _ _ (leq_total B C)) as [k | k];
      [ intros P X1 X2 X3 X4 X5 X6;apply X1; apply andb_true_intro; split; assumption
      | intros P X1 X2 X3 X4 X5 X6;apply X2; apply andb_true_intro; split; assumption
      | intros P X1 X2 X3 X4 X5 X6;apply X4; apply andb_true_intro; split; assumption
      | intros P X1 X2 X3 X4 X5 X6;apply X5; apply andb_true_intro; split; assumption
      | intros P X1 X2 X3 X4 X5 X6;apply X3; apply andb_true_intro; split; assumption
      | intros P X1 X2 X3 X4 X5 X6;apply X6; apply andb_true_intro; split; assumption
      | intros P X1 X2 X3 X4 X5 X6;apply X4; apply andb_true_intro; split; assumption
      | intros P X1 X2 X3 X4 X5 X6;apply X6; apply andb_true_intro; split; assumption].
  Qed.
  
  Ltac wrap_it_completely3 tac :=
    let A:= fresh "A" in
    let B:= fresh "B" in
    let C:= fresh "C" in
    let Xsym := fresh "Xsym" in
    let Xsym1 := fresh "Xsym1" in
    let Xsym2 := fresh "Xsym2" in
    let Xle := fresh "Xle" in
    intros A B C;
    pattern A,B,C; 
    match goal with A:?ty |- (?P A B C) =>
                    cbv beta;
                    revert A B C;
                    assert (Xle:forall A B C:ty, A<=B<=C -> P A B C) ;
                    [ tac
                    | intros A B C; apply (wrapABC A B C) || apply (wraplmp A B C);idtac]
    end.

  Definition dist_3l (A B C :Line) : bool :=
    (negb (eqL A B)) && (negb (eqL A C)) && (negb (eqL B C)).

   Ltac prove_a3_3' :=
    let v1 := fresh in
    let v2 := fresh in
    let v3 := fresh in
    let Hv1v2v3 := fresh in
    let hd:= fresh in 
    let hd12:=fresh in 
    let hd1 :=fresh in
    let hd2 :=fresh in
    let hd3 :=fresh in
    let hypv1 := fresh in
    let hypv2 := fresh in 
    let Hv1v2diff := fresh in
    let hypv3 := fresh in 
    let Hv1v3 := fresh in
    let Hv2v3 := fresh in 
    unfold dist_3l; intros v1 v2 v3 Hv1v2v3 hd;
    destruct (ab_bool_lr _ _ hd) as [hd12 hd3];
    destruct (ab_bool_lr _ _ hd12) as [hd1 hd2];
    revert Hv1v2v3 hd1 hd2 hd3;
    elim v1 using Line_rect; intros hypv1; 
    abstract (elim v2 using Line_rect; intros hypv2 Hv1v2v3 Hv1v2diff;
              solve [remove_cases |
                     clear Hv1v2v3 Hv1v2diff; 
                     (elim v3 using Line_rect; intros hypv3 Hv1v3 Hv2v3;
              solve [remove_cases | clear Hv1v3 Hv2v3; solve_ex_ll])]).

   Lemma a3_3 : forall v1 v2 v3:Line,
       (dist_3l v1 v2 v3) -> exists v4 :Line,  exists T1:Point, exists T2:Point, exists T3:Point,
             (Intersect_In v1 v4 T1) && (Intersect_In v2 v4 T2) && (Intersect_In v3 v4 T3).
   Proof.
    idtac "-> proving a3_3".
    wrap_it_completely3 idtac.
    time(prove_a3_3').
    
    exact Xle.
    
    intros.
    assert (Hd: dist_3l x z y).
    unfold dist_3l, eqL in * ; rewrite (eq_sym z y); apply comm12L; assumption.
    generalize (Xle x z y H Hd).
    intros Hex; destruct Hex as [v4 [t1 [t2 [t3 Hv4t1t2t3]]]].
    exists v4; exists t1; exists t3; exists t2.
    apply comm12L; apply circ3; assumption.
    
    intros.
    assert (Hd: dist_3l y x z).
    unfold dist_3l, eqL in * ; rewrite (eq_sym y x).
    apply circ3; apply comm12L; apply circ3; apply circ3; assumption.
    generalize (Xle y x z H Hd).
    intros Hex; destruct Hex as [v4 [t1 [t2 [t3 Hv4t1t2t3]]]].
    exists v4; exists t2; exists t1; exists t3.
    apply comm12L; assumption. 

    intros.
    assert (Hd: dist_3l y z x).
    unfold dist_3l,eqL in *.
    rewrite (eq_sym z x); rewrite (eq_sym y x); apply circ3; assumption.
    generalize (Xle y z x H Hd).
    intros Hex; destruct Hex as [v4 [t1 [t2 [t3 Hv4t1t2t3]]]].
    exists v4; exists t3; exists t1; exists t2.
    apply comm12L; apply circ3; apply comm12L; apply circ3; apply circ3; assumption.
    
    intros.
    assert (Hd: dist_3l z x y).
    unfold dist_3l,eqL in *; rewrite (eq_sym z x); rewrite (eq_sym z y);
      apply circ3; apply circ3; assumption.
    generalize (Xle z x y H Hd).
    intros Hex; destruct Hex as [v4 [t1 [t2 [t3 Hv4t1t2t3]]]].
    exists v4; exists t2; exists t3; exists t1.
    apply circ3; apply comm12L; apply circ3; apply circ3; apply comm12L; assumption.
    
    intros.
    assert (Hd: dist_3l z y x).
    unfold dist_3l,eqL in *; rewrite (eq_sym z y); rewrite (eq_sym z x); rewrite (eq_sym y x).
    apply comm12L; apply circ3; apply circ3; assumption.
    generalize (Xle z y x H Hd).
    intros Hex; destruct Hex as [v4 [t1 [t2 [t3 Hv4t1t2t3]]]].
    exists v4; exists t3; exists t2; exists t1.
    apply circ3; apply comm12L; assumption.

    (*Optimize Heap. Optimize Proof.*)
    Time Qed.
  Check a3_3.

  (** a2 : Pasch's axiom *)

  Definition proj t := match t with Some t' => t' | None => (o 15 0) end.
  
  Ltac findp := match goal with
                  |-  (@ex Point (fun J:Point => 
                                       is_true (andb (incid_lp J ?m) 
                                                     (incid_lp J ?p))))
                         => exists (proj (inter m p)); exact (@erefl bool true) end.

  Definition dist_4p  (A B C D:Point) : bool :=
    (negb (eqP A B)) && (negb (eqP A C)) && (negb (eqP A D))
                     && (negb (eqP B C)) && (negb (eqP B D)) && (negb (eqP C D)).

  Lemma points_line' : forall T Z:Point, forall x:Line,
        incid_lp T x -> incid_lp Z x -> ~~ eqP T Z -> x = l_from_points(T,Z).
  Proof.
    idtac "-> proving points_line'".
    time (intros T Z x;
            elim x using Line_rect; intros hypx;
            elim T using Point_rect; intros hypt HTx;
            solve [remove_cases |
                   elim Z using Point_rect; intros hypz HZx HTZ;
                   solve [ remove_cases | apply val_inj; exact (@erefl nat _)]]).
    Time Qed.

  Ltac handle' x :=
    match goal with Ht: is_true (incid_lp ?T x),
                    Hz: is_true (incid_lp ?Z x),
                    Htz : is_true (negb (eqP ?T ?Z)) |- _ =>
                    let HP := fresh in pose proof (points_line' T Z x Ht Hz Htz) as HP;
                                       clear Ht Hz; rewrite HP(*; subst*)  end.

  Lemma a2 : forall A B C D:Point, forall lAB lCD lAC lBD :Line, 
        dist_4p A B C D -> 
        incid_lp A lAB && incid_lp B lAB ->  
        incid_lp C lCD && incid_lp D lCD -> 
        incid_lp A lAC && incid_lp C lAC -> 
        incid_lp B lBD && incid_lp D lBD -> 
        (exists I:Point, incid_lp I lAB && incid_lp I lCD) ->
        exists J:Point, (incid_lp J lAC && incid_lp J lBD). 
  Proof.
    idtac "-> proving a2".
    wrap_it_completely idtac.

    time(unfold dist_4p;
            intros P Q HPQle R S l1 l2 l3 l4 hd hp1q1 hr2s2 hp3r3 hq4s4 Ht;

    destruct (ab_bool_lr _ _ hd) as [hd12345 hd6];
    destruct (ab_bool_lr _ _ hd12345) as [hd1234 hd5];
    destruct (ab_bool_lr _ _ hd1234) as [hd123 hd4];
    destruct (ab_bool_lr _ _ hd123) as [hd12 hd3];
    destruct (ab_bool_lr _ _ hd12) as [hd1 hd2]; clear hd hd12345 hd1234 hd123 hd12;    
    destruct (ab_bool_lr _ _ hp1q1) as [hp1 hq1]; 
    destruct (ab_bool_lr _ _ hr2s2) as [hr2 hs2]; 
    destruct (ab_bool_lr _ _ hp3r3) as [hp3 hr3]; 
    destruct (ab_bool_lr _ _ hq4s4) as [hq4 hs4]; clear hp1q1 hr2s2 hp3r3 hq4s4;

    revert HPQle hd1 hp1 hq1 hd2 hd4 hp3 hr3 hd3 hd5 hd6 hr2 hs2 hq4 hs4 Ht;
    elim P using Point_rect; intros hypP;

    abstract (
        elim Q using Point_rect;
        intros hypQ hd1 HPQdiff;
        solve [ remove_cases | 
        intros hp1 hq1; handle' l1; clear hd1;
        abstract (
            elim R using Point_rect;
            intros hypR hd2 hd4;
            solve [remove_cases |
                   intros hp3 hr3; handle' l3; clear hd2 hd4;
                   abstract (elim S using Point_rect; intros hypS hd3 hd5 hd6;
                             solve [ remove_cases |
                                     intros  hr2 hs2;
                                     handle' l2;
                                     intros  hq4 hs4;
                                     handle' l4;
                                     clear hd5 hd6;
                                     abstract (intros Ht; destruct Ht as [t Ht]; revert Ht;
                                               elim t using Point_rect; intros hypt Ht;
                                               solve [remove_cases |  findp ])])])])).
(* 377s *)
      clear Xle; intros.
      assert (dist: dist_4p x y D C).
      
      unfold dist_4p,eqP in H0; unfold dist_4p,eqP;
        rewrite (eq_sym x y); rewrite (eq_sym D C); apply bool6; assumption.
      assert (exists J : Point, (incid_lp J) lBD && (incid_lp J) lAC).
      apply (H D C lAB lCD lBD lAC dist);
      [ apply circ2; assumption | apply circ2; assumption | assumption | assumption | assumption].
      destruct H6 as [J HJ]; exists J; apply circ2; assumption.
      Time Qed.

End PS.

(* Local Variables: *)
(* coq-prog-name: "/Users/magaud/.opam/4.06.0/bin/coqtop" *)
(* coq-load-path: (("/Users/magaud/math-comp/mathcomp" "mathcomp") ("." "Top") ) *)
(* suffixes: .v *)
(* End: *)

