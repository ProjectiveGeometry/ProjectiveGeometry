Require Import ords ssreflect ssrfun ssrbool pg3x_spec pg33_ind.
Require Import wlog.

Module PS : ProjectiveSpace.

  Definition Point := Point.
  Definition Line := Line.

  Definition incid_lp := incid_lp. 
  Definition eqP := eqP.
  Definition eqL := eqL.

  (** a1_exists : existence of a line generated from 2 points *)

  Check l_from_points.
  
  Ltac prove_a1_exists :=
    let A:=fresh in
    let B:=fresh in
    intros A B;  pose (l:=(l_from_points A B));
                   revert l;case A; case B; intros l; exists l; exact (erefl true).

  Lemma a1_exists : forall A B : Point,
      {l : Line | incid_lp A l && incid_lp B l}.
  Proof.
    idtac "-> proving a1_exists".
    time (prove_a1_exists).
    Time Qed.
  Check a1_exists.

  (** a3_1 : every line has at least three distinct points *)
  
  Ltac exists_p3 t u v :=
    exact (existT _ t 
                  (existT _  u 
                          (exist _   v (erefl true)))).
  
  Ltac prove_a3_1 := let l := fresh "l" in
                     let x := fresh "x" in
                     intros l; pose (x:= points_from_line l); revert x;
                     case l; intros x;
                     exists_p3 (fst (fst (fst x))) (snd (fst (fst x))) (snd (fst x)).

  Definition dist_3p  (A B C :Point) : bool := (negb (eqP A B)) && (negb (eqP A C)) && (negb (eqP B C)).

  Lemma a3_1 : 
    forall l:Line,{A:Point &{B:Point &{ C:Point| 
            dist_3p A B C && (incid_lp A l && incid_lp B l && incid_lp C l)}}}.
    Proof.
    idtac "-> proving a3_1".
    time (prove_a3_1).
    Time Qed. 

    Check a3_1.

  (** a1_unique : unicity of the line generated from 2 points *)
  (** l_from_points is actually a1_exists *)
  Check l_from_points.
  Check a1_exists.

  Lemma points_line : forall T Z:Point, forall x:Line,
        incid_lp T x -> incid_lp Z x -> (T<>Z) -> x = (l_from_points T Z).
  Proof.
    idtac "-> proving points_line".
    time (intros T Z x;
          case x; case T; intros HTx;
          first [ discriminate | 
                 case Z; intros HZx HTZ;
                 solve  [ discriminate |  exact (@erefl Line _) | apply False_rect; auto ] ]).
    Time Qed.

  Check points_line.
  
  Ltac handle x :=
    match goal with Ht  : is_true (incid_lp ?T x),
                    Hz  : is_true (incid_lp ?Z x),
                    Htz : (not (@eq Point ?T ?Z))  |- _ =>
                    let HP := fresh in pose proof (points_line T Z x Ht Hz Htz) as HP;
                                       clear Ht Hz; rewrite HP(*; subst*)  end.

  Ltac prove_a1_unique :=
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
    intros A B l1 l2 HAB HAl1 HBl1 HAl2 HBl2;
    revert A B HAB l1 HAl1 HBl1 l2 HAl2 HBl2;
    intros  X; case X;
    intros Y;case Y; intros HAB;
    solve [apply False_rect; auto
          | discriminate
          | intros l1 HAl1 HBl1; handle l1; intros l2 HAl2 HBl2; handle l2; exact (@erefl Line _)].
  
  Lemma a1_unique:forall (A B :Point)(l1 l2:Line),
      ~A=B -> incid_lp A l1 -> incid_lp B l1  -> incid_lp A l2 -> incid_lp B l2 -> l1=l2.
  Proof.
    idtac "-> proving a1_unique".
    time(prove_a1_unique).
    Time Qed.
  
  Check a1_unique.

  Lemma Point_dec : forall T U:Point, {T=U}+{~T=U}.
  Proof.
    intros T U; case T; case U;
      solve [left; exact (@erefl Point _) | right; discriminate].
  Qed. 

  Ltac prove_uniqueness :=
    let P:= fresh in
    let Q:= fresh in
    let hypP := fresh in
    let HPQdiff := fresh in 
    let hypQ := fresh in
    let HPQ := fresh in 
    let l := fresh in
    let m := fresh in
    let Hl := fresh in
    let Hl' := fresh in
    let Hm := fresh in
    let Hm' := fresh in
    intros P Q l m Hl Hl' Hm Hm';
    revert l Hl Hl' m Hm Hm';
    destruct (Point_dec P Q) as [HPQdiff | HPQdiff];
    [left; rewrite HPQdiff; exact (@erefl Point _) | idtac]; revert HPQdiff;
    case P; case Q; intros HPQdiff;
    solve [discriminate |  
      intros  l Hl Hl';handle l; intros m Hm Hm'; handle m; right; exact (@erefl Line _)].

  Lemma uniqueness : forall (A B :Point)(l1 l2:Line),
      incid_lp A l1 -> incid_lp B l1  -> incid_lp A l2 -> incid_lp B l2 -> A = B \/ l1 = l2.
  Proof.
    idtac "-> proving uniqueness".
    time(prove_uniqueness).
    Time Qed.
  Check uniqueness.
  
  (** a3_2 : there exists 2 lines which do not intersect, i.e. dim >= 3  *)

  Ltac solve_a3_2 := let p:= fresh in
                     intros p; case p;
                     let hypp:=fresh in let t := fresh in intros hypp t; discriminate.

  (*Ltac prove_a3_2 := try_all_l ltac:(fun l1 => exists l1; try_all_l ltac:(fun l2 => exists l2; solve_a3_2)).*)
  
  Lemma a3_2 : exists l1:Line, exists l2:Line, forall p:Point, ~(incid_lp p l1 && incid_lp p l2). 
  Proof.
    idtac "-> proving a3_2".
    exists L0; exists L34;intros p; case p; 
      let hypp:=fresh in let t := fresh in intros t; discriminate.
    (*Time (prove_a3_2).*) (* we could have chosen GKL and EHM for instance:  exists (o 35 0); exists (o 35 34)).*)
    Time Qed.
  Check a3_2.

(* a3_3 : given 3 lines, there exists a line which intersects these 3 lines *)

  Definition Intersect_In (l1 l2 :Line) (P:Point) := incid_lp P l1 && incid_lp P l2.
 
  (** points_from_l is actually a3_1 *)
  
  Definition points_from_l (l:Line) := points_from_line l.

  Ltac exists_lppp l t u v :=
    exact (ex_intro _  l 
                 (ex_intro _  t
                  (ex_intro _ u 
                          (ex_intro _  v  (erefl true))))).

  Definition dist_3l (A B C :Line) : bool :=
    (negb (eqL A B)) && (negb (eqL A C)) && (negb (eqL B C)).

  Lemma a3_3_simple :
    forall v1 v2 v3:Line,
      leL v1 v2-> leL v2 v3 ->
      dist_3l v1 v2 v3 ->
      exists v4 :Line, exists T1:Point, exists T2:Point, exists T3:Point,
              (Intersect_In v1 v4 T1) && (Intersect_In v2 v4 T2) && (Intersect_In v3 v4 T3).
   Proof.
     idtac "-> proving a3_3_simple".
     unfold dist_3l; intros v1 v2 v3 Hv1v2 Hv2v3 Hd;
       pose (t:=f_a3_3 v1 v2 v3) ;
pose(l:=fst t); pose (x:= fst (fst (snd t))); pose (y:= snd (fst (snd t))); pose (z:=snd (snd t));
       revert Hv1v2 Hv2v3 Hd t l x y z.

     case v1.

(*case v2;
                  intros hp1p2;try exact (degen_bool _ hp1p2) .

case v3;intros hp1p3 hdist l x y z.*)

    par: abstract
           (time (case v2;
                  intros hp1p2;
                  first [exact (degen_bool _ hp1p2) | 
                         (case v3;
                          intros hp1p3 hdist t l x y z;
                          solve [ (exact (degen_bool _ hp1p3))
                                | (exact (degen_bool _ hdist))
                                | exists_lppp l x y z ])])).

      Time Qed.
(*233s*)
   Lemma eqL_sym : forall x y:Line, eqL x y = eqL y x.
    Proof.
      idtac "proving eqL_sym".
      time (intros; apply PeanoNat.Nat.eqb_sym). 
    Time Qed.
    Check eqL_sym.
    
    Lemma eqP_sym : forall x y:Point, eqP x y = eqP y x.
    Proof. 
      idtac "proving eqP_sym".
      time (intros;apply PeanoNat.Nat.eqb_sym).
    Time Qed.
    Check eqP_sym.
    
    Lemma exchL: forall x y B C, ~~eqL y x && B &&C-> ~~eqL x y && B && C.
    Proof.
      intros x y b c H.
      apply ab_bool in H.      
      destruct H as [Hx Hy].
      apply ab_bool in Hx.
      destruct Hx.
      apply ab_bool; split.
      apply ab_bool; split.
      rewrite eqL_sym.
      assumption.
      assumption.
      assumption.
    Qed.
    
    Lemma exchP: forall x y B C D E F,
        ~~eqP y x && B &&C &&D &&E &&F-> ~~eqP x y && B && C && D && E &&F.
    Proof.
      intros x y b c d e f H.
      apply ab_bool in H.
      destruct H as [Ha Hf]; apply ab_bool in Ha;
        destruct Ha as [Ha He]; apply ab_bool in Ha;
          destruct Ha as [Ha Hd]; apply ab_bool in Ha;
            destruct Ha as [Ha Hc]; apply ab_bool in Ha;
              destruct Ha as [Ha Hb].
      apply ab_bool; split.
      apply ab_bool; split.
      apply ab_bool; split.
      apply ab_bool; split.
      apply ab_bool; split.
      rewrite eqP_sym.
      assumption.
      assumption.
      assumption.
      assumption.
      assumption.
      assumption.
    Qed.

   Lemma a3_3 : forall v1 v2 v3:Line,
      dist_3l v1 v2 v3 -> exists v4 :Line,  exists T1:Point, exists T2:Point, exists T3:Point,
             (Intersect_In v1 v4 T1) && (Intersect_In v2 v4 T2) && (Intersect_In v3 v4 T3).
  Proof.
    idtac "-> proving a3_3".
    intros v1 v2 v3.
    wlog3 v1 v2 v3 leL leL_total idtac idtac.

    intros; apply a3_3_simple.
    destruct (ab_bool_lr _ _  H) as [Ha1 Ha2]; exact Ha1.
    destruct (ab_bool_lr _ _  H) as [Ha1 Ha2]; exact Ha2.
    assumption.

    intros.
    assert (Hd: dist_3l x z y).
    unfold dist_3l in *;
      apply circ3;apply circ3;apply exchL;apply circ3; apply comm12L; assumption.
    destruct (H Hd) as [v4 [t1 [t2 [t3 Hv4t1t2t3]]]].
    exists v4; exists t1; exists t3; exists t2.
    apply circ3; apply circ3; apply comm12L; assumption.
    
    intros.
    assert (Hd: dist_3l y x z).
    unfold dist_3l in *; apply exchL; apply circ3; apply circ3; apply comm12L; assumption.
    destruct (H Hd) as [v4 [t1 [t2 [t3 Hv4t1t2t3]]]].
    exists v4; exists t2; exists t1; exists t3.
    apply comm12L; assumption.
    
    intros.
    assert (Hd: dist_3l y z x).
    unfold dist_3l in *.
    apply circ3; apply exchL; apply circ3; apply exchL; apply circ3; apply circ3; assumption.
    destruct (H Hd) as [v4 [t1 [t2 [t3 Hv4t1t2t3]]]].
    exists v4; exists t3; exists t1; exists t2.
    apply circ3; assumption.
    
    intros.
    assert (Hd: dist_3l z x y).
    unfold dist_3l in *.
    apply exchL; apply circ3; apply exchL; apply circ3; assumption.
    destruct (H Hd) as [v4 [t1 [t2 [t3 Hv4t1t2t3]]]].
    exists v4; exists t2; exists t3; exists t1.
    apply circ3; apply circ3; assumption.
    
    intros.
    assert (Hd: dist_3l z y x).
    unfold dist_3l in *.
    apply exchL; apply circ3; apply exchL; apply circ3; apply exchL;
      apply circ3; apply circ3; apply comm12L; assumption.
    destruct  (H Hd) as [v4 [t1 [t2 [t3 Hv4t1t2t3]]]].
    exists v4; exists t3; exists t2; exists t1.
    apply comm12L; apply circ3;apply circ3; assumption. 
    Time Qed.
  
  (** a2 : Pasch's axiom *)

  Definition dist_4p  (A B C D:Point) : bool :=
    (negb (eqP A B)) && (negb (eqP A C)) && (negb (eqP A D))
                     && (negb (eqP B C)) && (negb (eqP B D)) && (negb (eqP C D)).

  Ltac findp' := match goal with
                  |-  (@ex Point (fun J:Point => 
                                       is_true (andb (incid_lp J ?m) 
                                                     (incid_lp J ?p))))
                  /\ (@ex Point (fun K:Point => 
                                       is_true (andb (incid_lp K ?q) 
                                                     (incid_lp K ?r))))=> 
                  exact (conj (ex_intro _  ((*pg33_ind.*)f_a2 m p) (erefl true))
                              (ex_intro _  ((*pg33_ind.*)f_a2 q r) (erefl true)))
                 end.
  
  Lemma a2_conj_specific :
    forall A B C D:Point, leP A B -> leP C D ->
        let lAB := l_from_points A B in
        let lCD := l_from_points C D in
        let lAC := l_from_points A C in
        let lBD := l_from_points B D in
        let lAD := l_from_points A D in
        let lBC := l_from_points B C in 
        
        dist_4p A B C D -> 
        incid_lp A lAB && incid_lp B lAB ->  
        incid_lp C lCD && incid_lp D lCD -> 
        incid_lp A lAC && incid_lp C lAC -> 
        incid_lp B lBD && incid_lp D lBD ->
        incid_lp A lAD && incid_lp D lAD ->
        incid_lp B lBC && incid_lp C lBC ->
        
        (exists I:Point, incid_lp I lAB && incid_lp I lCD) ->
        (exists J:Point, (incid_lp J lAC && incid_lp J lBD)) /\
        (exists K:Point, (incid_lp K lAD && incid_lp K lBC)).
  Proof.
  idtac "-> proving a2_conj_specific".
     intros A B C D HleAB HleCD lAB lCD lAC lBD lAD lBC Hdist HlAB HlCD HlAC HlBD HlAD HlBC Hex;
       destruct (ab_bool_lr _ _ Hdist) as [Hdist1 HCD]; clear Hdist;
         destruct (ab_bool_lr _ _ Hdist1) as [Hdist2 HBD]; clear Hdist1;
           destruct (ab_bool_lr _ _ Hdist2) as [Hdist3 HBC]; clear Hdist2;
             destruct (ab_bool_lr _ _ Hdist3) as [Hdist4 HAD]; clear Hdist3;
               destruct (ab_bool_lr _ _ Hdist4) as [HAB HAC]; clear Hdist4;
        revert A B HleAB HAB lAB HlAB C HBC HAC lBC HlBC lAC HlAC D HleCD HAD HBD HCD lAD HlAD lBD HlBD lCD HlCD Hex.

     time (intros A B; case A; case B; intros HlePAB HAB lAB HlAB). 
     par: abstract (time (first [exact (degen_bool _ HlePAB) |exact (degen_bool _ HAB) | exact (degen_bool _ HlAB)| 



      (intros C; case C; intros HBC HAC lBC HlBC lAC HlAC; 
           first [  exact (degen_bool _ HBC) | exact (degen_bool _ HAC)
                        |
           
                        (intros D; case D; intros HleCD HAD HBD HCD lAD HlAD lBD HlBD lCD HlCD Hex;

                         first [ exact (degen_bool _ HleCD) | exact (degen_bool _ HAD)
                                 | exact (degen_bool _ HBD) | exact (degen_bool _ HCD)
                                 
                                 | case Hex; intros t; case t; intros Ht;
                                 first [exact (degen_bool _ Ht) | findp'] ])])])).
  Qed.
  Check a2_conj_specific.
  
  Lemma l_from_points_sym : forall x y:Point, l_from_points x y = l_from_points y x.
  Proof.
    intros x y; case x; case y; reflexivity.
  Qed.

Lemma a2_conj :
    forall A B C D:Point, dist_4p A B C D -> 
         let lAB := l_from_points A B in
         let lCD := l_from_points C D in
         let lAC := l_from_points A C in
         let lBD := l_from_points B D in
         let lAD := l_from_points A D in
         let lBC := l_from_points B C in 
         
         incid_lp A lAB && incid_lp B lAB ->  
         incid_lp C lCD && incid_lp D lCD -> 
         incid_lp A lAC && incid_lp C lAC -> 
         incid_lp B lBD && incid_lp D lBD ->
         incid_lp A lAD && incid_lp D lAD ->
         incid_lp B lBC && incid_lp C lBC ->
         
         (exists I:Point, incid_lp I lAB && incid_lp I lCD) ->
         (exists J:Point, (incid_lp J lAC && incid_lp J lBD)) /\
         (exists J:Point, (incid_lp J lAD && incid_lp J lBC)).
  Proof.
    intros A B.
    wlog2 A B leP leP_total idtac idtac.
    intros A B HleAB.
    intros C D.
    wlog2 C D leP leP_total idtac ltac:(intros; apply a2_conj_specific; assumption || exact I).
    (* other cases *)

    intros C D Hr.

    intros lAB lCD lAC lBD lAD lBC Hdist HlAB HlCD HlAC HlBD HlAD HlBC Hex.
    assert (Hd' : dist_4p A B D C).
    unfold dist_4p in *.
    apply circ6; apply comm12P; apply circ6; apply circ6 ; apply comm12P; apply circ6;
    apply circ6; apply exchP; apply circ6; assumption.

    assert (HlDC:(incid_lp D (l_from_points D C) && incid_lp C (l_from_points D C))).
    apply circ2; rewrite l_from_points_sym; assumption. 
    assert (Hex': (exists I : Point, incid_lp I (l_from_points A B) && incid_lp I (l_from_points D C))).
    rewrite (l_from_points_sym D C); assumption.
    generalize (Hr Hd' HlAB HlDC HlAD HlBC HlAC HlBD Hex').
    solve [intuition].

    intros A B Hr C D.
    intros Hd lAB lCD lAC lBD lAD lBC HlAB HlCD HlAC HlBD HlAD HlBC Hex.
    assert (Hd':  dist_4p B A C D).
    unfold dist_4p in *.
    apply exchP; apply circ6; apply circ6; apply comm12P; apply circ6; apply comm12P;
      apply circ6; apply circ6; apply circ6; apply circ6; apply comm12P; apply circ6;
        apply comm12P; apply circ6; apply circ6; apply circ6; apply circ6; assumption.

    assert (HlBA:incid_lp B (l_from_points B A) && incid_lp A (l_from_points B A)).
    apply circ2; rewrite l_from_points_sym; assumption.
    assert (HlDB:(incid_lp D (l_from_points D B) && incid_lp B (l_from_points D B))).
    apply circ2; rewrite l_from_points_sym; assumption.
    assert (Hex':(exists I : Point, incid_lp I (l_from_points B A) && incid_lp I (l_from_points C D))).
    rewrite (l_from_points_sym B A); assumption.

    generalize (Hr C D Hd' HlBA HlCD HlBC HlAD HlBD HlAC Hex').
    intros (He1,He2).
    split.
    destruct He2 as [e2 He2]; apply circ2 in He2; exists e2; assumption.
    destruct He1 as [e1 He1]; apply circ2 in He1; exists e1; assumption.
  Qed.

  Check a2_conj.

  
  Lemma points_line' : forall T Z:Point, forall x:Line,
        incid_lp T x -> incid_lp Z x -> ~~ eqP T Z -> x = (l_from_points T Z).
  Proof.
    idtac "-> proving points_line".
    time (intros T Z x;
           case x ; 
           case T; intros  HTx;
           first [ discriminate | 
                   case Z; intros  HZx HTZ;
                   solve [discriminate | apply False_rect; auto | exact (@erefl Line _)]]).
    Time Qed.

  Ltac handle' x :=
    match goal with Ht  : is_true (incid_lp ?T x),
                          Hz  : is_true (incid_lp ?Z x),
                                Htz : is_true (negb (eqP ?T ?Z)) |- _ =>
                    let HP := fresh in pose proof (points_line' T Z x Ht Hz Htz) as HP;
                                       clear Ht Hz; rewrite HP(*; subst*)  end.

  
  Ltac handle_eff l P Q HlAB:= assert (l=l_from_points P Q);[
                                 assert (incid_lp P l) by ( solve [intuition]);
                                 assert (incid_lp Q l) by ( solve [intuition]);
                                 handle' l; reflexivity | idtac].

  Lemma incid_lp_l_from_point1 : forall x y, incid_lp x (l_from_points x y).
  Proof.
    intros x y; case x; case y; trivial.
  Qed.

  Lemma incid_lp_l_from_point2 : forall x y, incid_lp y (l_from_points x y).
  Proof.
    intros x y; case x; case y; trivial.
  Qed.

  Lemma a2 : forall A B C D:Point, forall lAB lCD lAC lBD :Line,
        dist_4p A B C D -> 
        incid_lp A lAB && incid_lp B lAB ->
        incid_lp C lCD && incid_lp D lCD ->
        incid_lp A lAC && incid_lp C lAC ->
        incid_lp B lBD && incid_lp D lBD ->
        (exists I:Point, incid_lp I lAB && incid_lp I lCD) ->
        exists J:Point, incid_lp J lAC && incid_lp J lBD.
  Proof.
    intros A B C D lAB lCD lAC lBD Hdist HlAB HlCD HlAC HlBD Hex.
    destruct (ab_bool_lr _ _ HlAB) as [HlAB1 HlAB2]; 
      destruct (ab_bool_lr _ _ HlCD) as [HlCD1 HlCD2]; 
      destruct (ab_bool_lr _ _ HlAC) as [HlAC1 HlAC2]; 
      destruct (ab_bool_lr _ _ HlBD) as [HlBD1 HlBD2]; 
      destruct (ab_bool_lr _ _ Hdist) as [Hdist1 HCD]; 
      destruct (ab_bool_lr _ _ Hdist1) as [Hdist2 HBD]; 
      destruct (ab_bool_lr _ _ Hdist2) as [Hdist3 HBC]; 
      destruct (ab_bool_lr _ _ Hdist3) as [Hdist4 HAD]; 
      destruct (ab_bool_lr _ _ Hdist4) as [HAB HAC].
    
    handle_eff lAB A B HlAB.
    handle_eff lCD C D HlCD.
    handle_eff lAC A C HlAC.
    handle_eff lBD B D HlBD.
    rewrite H in HlAB.
    rewrite H0 in HlCD.
    rewrite H1 in HlAC.
    rewrite H2 in HlBD.
    rewrite H in Hex.
    rewrite H0 in Hex.
    assert (HlAD:(incid_lp A (l_from_points A D) && incid_lp D (l_from_points A D))).
    apply Bool.andb_true_iff; split;
      [apply incid_lp_l_from_point1 | apply incid_lp_l_from_point2].
    
    assert (HlBC: (incid_lp B (l_from_points B C) && incid_lp C (l_from_points B C))).
    apply Bool.andb_true_iff; split;
      [apply incid_lp_l_from_point1 | apply incid_lp_l_from_point2].
    
    rewrite H1.
    rewrite H2.
    elim (a2_conj A B C D Hdist HlAB HlCD HlAC HlBD HlAD HlBC Hex).
    intros; assumption.
  Qed.
  Check a2.
  
End PS.

(* Local Variables: *)
(* coq-prog-name: "/Users/magaud/.opam/4.07.0/bin/coqtop" *)
(* coq-load-path: (("." "Top") ) *)
(* suffixes: .v *)
(* End: *)
