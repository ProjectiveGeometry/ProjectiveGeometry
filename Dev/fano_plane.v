Require Export ProjectiveGeometry.Dev.general_tactics.

(*****************************************************************************)
(** Fano plane **)

Module Type fano_plane.

Parameter Point:Set.
Parameter A B C D E F G : Point.

Parameter Line: Set.
Parameter ABF BCD CAE ADG  BEG  CFG  DEF : Line.

Parameter Incid : Point -> Line -> Prop.

Axiom is_only_7_pts : forall P:Point, {P=A}+{P=B}+{P=C}+{P=D}+{P=E}+{P=F}+{P=G}.

Axiom is_only_7_lines : forall P:Line, {P=ABF}+{P=BCD}+{P=CAE}+{P=ADG}+{P=BEG}+{P=CFG}+{P=DEF}.

Definition is_fano_plane A B C D E F G ABF BCD CAE ADG BEG CFG DEF :=
(~A=B /\ ~A=C /\ ~A=D /\ ~A=E /\ ~A=F /\ ~A=G /\
~B=C /\ ~B=D /\ ~B=E /\ ~B=F /\ ~B=G /\
~C=D /\ ~C=E /\ ~C=F /\ ~C=G /\
~D=E /\ ~D=F /\ ~D=G /\
~E=F /\ ~E=G /\
~F=G) /\
(ABF<>BCD /\ ABF <>CAE /\ ABF <>ADG /\ ABF<>BEG /\ ABF<>CFG /\ ABF<>DEF /\ 
BCD<>CAE /\ BCD<>ADG /\ BCD<>BEG /\ BCD<>CFG /\ BCD<>DEF /\
CAE<>ADG /\ CAE<>BEG /\ CAE<>CFG /\ CAE<>DEF /\
ADG<>BEG /\ ADG<>CFG /\ADG<>DEF /\
BEG<>CFG /\ BEG<>DEF /\
CFG<>DEF )/\ 

( Incid A ABF /\ Incid B ABF /\ ~ Incid C ABF /\ ~ Incid D ABF /\ ~ Incid E ABF /\ Incid F ABF /\ ~ Incid G  ABF /\
 ~ Incid A BCD /\ Incid B BCD /\ Incid C BCD /\ Incid D BCD /\ ~ Incid E BCD /\ ~ Incid F BCD /\ ~ Incid G  BCD /\
 Incid A CAE /\ ~ Incid B CAE /\ Incid C CAE /\ ~ Incid D CAE /\ Incid E CAE /\ ~ Incid F CAE /\ ~ Incid G  CAE /\
 Incid A ADG /\ ~ Incid B ADG /\ ~ Incid C ADG /\ Incid D ADG /\ ~ Incid E ADG /\ ~ Incid F ADG /\ Incid G  ADG /\
 ~ Incid A BEG /\ Incid B BEG /\ ~ Incid C BEG /\ ~ Incid D BEG /\  Incid E BEG /\ ~ Incid F BEG /\ Incid G  BEG /\
 ~ Incid A CFG /\ ~ Incid B CFG /\ Incid C CFG /\ ~ Incid D CFG /\ ~ Incid E CFG /\ Incid F CFG /\ Incid G  CFG /\
 ~ Incid A DEF /\ ~ Incid B DEF /\ ~ Incid C DEF /\ Incid D DEF /\ Incid E DEF /\ Incid F DEF /\ ~ Incid G  DEF).

Axiom is_fano_plane_inst :  is_fano_plane A B C D E F G ABF BCD CAE ADG BEG CFG DEF.

End fano_plane.

(*****************************************************************************)
(** Fano plane swap **)

Module swapf3 (M:fano_plane) : fano_plane
with Definition Point:=M.Point

with Definition A:= M.B 
with Definition B:=M.E
with Definition C:=M.D
with Definition D:=M.F
with Definition E:=M.C
with Definition F:=M.G
with Definition G:=M.A

with Definition Line:=M.Line

with Definition ABF:=M.BEG
with Definition BCD:=M.DEF
with Definition CAE:=M.BCD
with Definition ADG:=M.ABF
with Definition BEG:=M.CAE
with Definition CFG:=M.ADG
with Definition DEF:=M.CFG

with Definition Incid :=M.Incid

with Definition is_fano_plane := M.is_fano_plane.

Definition Point:=M.Point.

Definition A:=M.B.
Definition B:=M.E.
Definition C:=M.D.
Definition D:=M.F.
Definition E:=M.C.
Definition F:=M.G.
Definition G:=M.A.

Definition Line:=M.Line.

Definition ABF:=M.BEG.
Definition BCD:=M.DEF.
Definition CAE:=M.BCD.
Definition ADG:=M.ABF.
Definition BEG:=M.CAE.
Definition CFG:=M.ADG.
Definition DEF:=M.CFG.

Definition Incid :=M.Incid.

Definition is_fano_plane := M.is_fano_plane.

Lemma is_only_7_pts : forall P:Point, {P=A}+{P=B}+{P=C}+{P=D}+{P=E}+{P=F}+{P=G}.
Proof.
generalize (M.is_only_7_pts).
unfold A, B,C, D, E, F, G.
intros H P; elim (H P).
intuition.
intuition.
Qed.

Lemma is_only_7_lines : forall P:Line, {P=ABF}+{P=BCD}+{P=CAE}+{P=ADG}+{P=BEG}+{P=CFG}+{P=DEF}.
Proof.
generalize (M.is_only_7_lines).
unfold ABF, BCD, CAE, ADG, BEG, CFG, DEF .
intros H P;
generalize (H P); intuition.
Qed.

Lemma is_fano_plane_inst : is_fano_plane A B C D E F G ABF BCD CAE ADG BEG CFG DEF.
Proof.
generalize (M.is_fano_plane_inst).
unfold is_fano_plane, M.is_fano_plane.
intros H; decompose [and] H; clear H.
unfold A, B, C, D, E, F, G, ABF, BCD, CAE, ADG, BEG, CFG, DEF .
repeat split;try  assumption;try auto.
Qed.

End swapf3.


Module Desargues_from_A (M:fano_plane).

Import M.

Definition on_line := fun A B C l => M.Incid A l /\ Incid B l /\ Incid C l.
Definition collinear A B C :=  exists l, Incid A l /\ Incid B l /\ Incid C l.

Ltac use H := decompose [and ex] H; clear H.

Ltac solve_ex L := solve [exists L;auto].

(** A tactic which tries all possible lines **)

Ltac solve_ex_l := first [solve_ex ABF
     |  solve_ex BCD
     |  solve_ex CAE
     |  solve_ex ADG
     |  solve_ex BEG
     |  solve_ex CFG
     |  solve_ex DEF
 ].

Ltac solve_ex_p := first [
        solve_ex A
     |  solve_ex B
     |  solve_ex C
     |  solve_ex D
     |  solve_ex E
     |  solve_ex F
     |  solve_ex G
 ].

Ltac new_case P := 
match (type of P) with 
| Point => generalize (is_only_7_pts P) ; let Q := fresh in (intros Q; decompose [sumor sumbool] Q; clear Q; subst)
| Line => generalize (is_only_7_lines P) ; let Q := fresh in (intros Q; decompose [sumor sumbool] Q; clear Q; subst)
end.

Lemma col_degen_1 : forall P R, ~ collinear P P R -> False.
Proof.
intros.
apply H.
unfold collinear in *.
generalize (is_fano_plane_inst); unfold is_fano_plane in *;
intro Hw ;use Hw;new_case P; new_case R;solve_ex_l.
Qed.

Lemma col_degen_2 : forall P R, 
~ collinear P R P -> False.
Proof.
intros.
apply H.
unfold collinear.
generalize (is_fano_plane_inst); unfold is_fano_plane in *; intro Hw ;use Hw; 
new_case P;new_case R;solve_ex_l.
Qed.

Lemma col_degen_3 : forall P R, 
~ collinear R P P -> False.
Proof.
intros.
apply H.
unfold collinear.
generalize (is_fano_plane_inst); unfold is_fano_plane in *; intro Hw ;use Hw; 
new_case P;new_case R;solve_ex_l.
Qed.

Lemma not_all_equal : forall P Q R : Point, ~(~P=P \/ ~Q=Q \/ ~R=R).
Proof.
intros P Q R H; intuition.
Qed.

Ltac degens := 
match goal with
| H: ~?A=?A \/ ~?B=?B \/ ~?C=?C |- _ => elim (not_all_equal A B C H)
| H:~collinear ?P ?P ?R |- _ => elim (col_degen_1 P R H)
| H:~collinear ?P ?R ?P |- _ => elim (col_degen_2 P R H)
| H:~collinear ?R ?P ?P |- _ => elim (col_degen_3 P R H)
| H:Incid ?P ?l, H2: ~ Incid ?P ?l |- _ => cut False; [let hf := fresh in (intro hf;elim hf)| apply (H2 H)]
end.

Ltac case_eq_s  O := new_case O.

Ltac case_clear P := case_eq_s P; try solve [degens].

Ltac fano_ctx := generalize (is_fano_plane_inst); unfold is_fano_plane in *; let Hw := fresh in (intro Hw ;use Hw).

Lemma collinearPPQ : forall P Q: Point, collinear P P Q.
Proof.
intros P; generalize (is_fano_plane_inst); unfold is_fano_plane in *; intro Hw ;use Hw; new_case P; intros Q; new_case Q; unfold collinear in *; 
solve_ex_l.
Qed.

Lemma collinearPQQ : forall P Q: Point, collinear P Q Q.
Proof.
intros P; generalize (is_fano_plane_inst); unfold is_fano_plane in *; intro Hw ;use Hw; new_case P; intros Q; new_case Q; unfold collinear in *; 
solve_ex_l.
Qed.

Lemma collinearPQP : forall P Q: Point, collinear P Q P.
Proof.
intros P; generalize (is_fano_plane_inst); unfold is_fano_plane in *; intro Hw ;use Hw;new_case P; intros Q; new_case Q; unfold collinear in *; 
solve_ex_l.
Qed.

Ltac cols :=  apply collinearPPQ || 
                    apply  collinearPQQ || 
                    apply collinearPQP ||
                    (unfold collinear;solve_ex_l).

Ltac collinear_line :=
match goal with 
H : ~collinear ?P ?Q ?R |- _ => 
  solve[assert (collinear P Q R) by (solve_ex_l); 
cut False; [intros Hf; elim Hf | auto]] 
end.

Ltac collinear_line_gen ABF BCD CAE ADG  BEG CFG DEF :=
match goal with 
H : ~collinear ?P ?Q ?R |- _ => 
  solve [assert (collinear P Q R) by (solve_ex_l); 
cut False; [intros Hf; elim Hf | auto]] 
end.

Lemma Desargues_from_A_spec :  forall P Q R P' Q' R' alpha beta gamma lPQ lPR lQR lP'Q' lP'R' lQ'R',
((on_line P Q gamma lPQ) /\ (on_line P' Q' gamma lP'Q')) /\
((on_line P R beta lPR) /\ (on_line P' R' beta lP'R')) /\
((on_line Q R alpha lQR) /\ (on_line Q' R' alpha lQ'R')) /\
((on_line A P P' ADG) /\ (on_line A Q Q' CAE) /\(on_line A R R' ABF)) /\ 
~collinear A P Q /\  ~collinear A P R /\ ~collinear A Q R /\ 
~collinear P Q R /\ ~collinear P' Q' R' /\ ((~P=P')\/(~Q=Q')\/(~R=R')) ->
collinear alpha beta gamma.
Proof.

intros P Q R P' Q' R' alpha beta gamma lPQ lPR lQR lP'Q' lP'R' lQ'R'.
intros.
unfold on_line in  *;use H.
generalize (is_fano_plane_inst); unfold is_fano_plane in *; intro Hw ;use Hw.

case_clear P;
case_clear Q;
case_clear R;

try collinear_line;
case_clear P';
case_clear Q';
case_clear R';
try collinear_line;
case_clear lPQ;
case_clear lP'Q';
case_clear lPR;
case_clear lP'R';
case_clear lQR;
case_clear lQ'R';
case_clear alpha;
case_clear beta;
try cols;
case_clear gamma;
try cols.
Qed.

Lemma col_1 : forall A B C,
 collinear A B C -> collinear B A C.
Proof.
intros.
unfold collinear in *.
decompose [ex and] H; clear H.
exists x.
intuition.
Qed.

Lemma col_2 : forall A B C,
 collinear A B C -> collinear A C B.
Proof.
intros.
unfold collinear in *.
decompose [ex and] H; clear H.
exists x.
intuition.
Qed.

Lemma col_3 : forall A B C,
 collinear A B C -> collinear B C A.
Proof.
intros.
unfold collinear in *.
decompose [ex and] H; clear H.
exists x.
intuition.
Qed.

Lemma col_4 : forall A B C,
 collinear A B C -> collinear C A B.
Proof.
intros.
unfold collinear in *.
decompose [ex and] H; clear H.
exists x.
intuition.
Qed.

Lemma col_5 : forall A B C,
 collinear A B C -> collinear C B A.
Proof.
intros.
unfold collinear in *.
decompose [ex and] H; clear H.
exists x.
intuition.
Qed.

Hint Resolve col_1 col_2 col_3 col_4 col_5 : Geom.

Lemma Desargues_from_A :  forall P Q R P' Q' R' alpha beta gamma lP lQ lR lPQ lPR lQR lP'Q' lP'R' lQ'R',
((on_line P Q gamma lPQ) /\ (on_line P' Q' gamma lP'Q')) /\
((on_line P R beta lPR) /\ (on_line P' R' beta lP'R')) /\
((on_line Q R alpha lQR) /\ (on_line Q' R' alpha lQ'R')) /\
((on_line A P P' lP) /\ (on_line A Q Q' lQ) /\(on_line A R R' lR)) /\ 
~collinear A P Q /\  ~collinear A P R /\ ~collinear A Q R /\ 
~collinear P Q R /\ ~collinear P' Q' R' /\ ((~P=P')\/(~Q=Q')\/(~R=R')) ->
collinear alpha beta gamma.
Proof.
intros P Q R P' Q' R' alpha beta gamma lP lQ lR lPQ lPR lQR lP'Q' lP'R' lQ'R'.
intros.
unfold on_line in  *;use H.
generalize (is_fano_plane_inst); unfold is_fano_plane in *; intro Hw ;use Hw. 
case_clear lP;
case_clear lQ;
case_clear lR;
try collinear_line.

cut (collinear gamma beta alpha).
auto with Geom.
apply (Desargues_from_A_spec R Q P R' Q' P' gamma beta alpha
  lQR lPR lPQ lQ'R' lP'R' lP'Q').
repeat split; auto with Geom;
decompose [or] H33;auto.

cut (collinear beta gamma alpha).
auto with Geom.
eapply (Desargues_from_A_spec Q R P Q' R' P' beta gamma alpha 
lQR lPQ lPR lQ'R' lP'Q' lP'R').
repeat split; auto with Geom;
decompose [or] H33;auto.

cut (collinear gamma alpha beta).
auto with Geom.
eapply (Desargues_from_A_spec R P Q R' P' Q' gamma alpha beta 
 lPR lQR lPQ lP'R' lQ'R' lP'Q');
repeat split; auto with Geom;
decompose [or] H33;auto.

cut (collinear beta alpha gamma).
auto with Geom.
eapply (Desargues_from_A_spec Q P R Q' P' R' beta alpha gamma 
 lPQ lQR lPR lP'Q' lQ'R' lP'R');
repeat split; auto with Geom;
decompose [or] H33;auto.

cut (collinear alpha gamma beta).
auto with Geom.
eapply (Desargues_from_A_spec P R Q P' R' Q' alpha gamma beta 
lPR lPQ lQR lP'R' lP'Q' lQ'R');
repeat split; auto with Geom;
decompose [or] H33;auto.

apply (Desargues_from_A_spec P Q R P' Q' R' alpha beta gamma lPQ lPR lQR lP'Q' lP'R' lQ'R').
repeat split; auto with Geom.
Qed.

End Desargues_from_A.


Module Desargues (M:fano_plane).

Import M.

Module Import M2:= Desargues_from_A M.

Module swaped_B := swapf3 M.
Module swaped_B' := Desargues_from_A swaped_B.
Module swaped_E := swapf3 swaped_B.
Module swaped_E' := Desargues_from_A swaped_E.
Module swaped_C := swapf3 swaped_E.
Module swaped_C' := Desargues_from_A swaped_C.
Module swaped_D := swapf3 swaped_C.
Module swaped_D' := Desargues_from_A swaped_D.
Module swaped_F := swapf3 swaped_D.
Module swaped_F' := Desargues_from_A swaped_F.
Module swaped_G := swapf3 swaped_F.
Module swaped_G' := Desargues_from_A swaped_G.

Theorem Desargues : 
 forall O P Q R P' Q' R' alpha beta gamma lP lQ lR lPQ lPR lQR lP'Q' lP'R' lQ'R',
((on_line P Q gamma lPQ) /\ (on_line P' Q' gamma lP'Q')) /\
((on_line P R beta lPR) /\ (on_line P' R' beta lP'R')) /\
((on_line Q R alpha lQR) /\ (on_line Q' R' alpha lQ'R')) /\
((on_line O P P' lP) /\ (on_line O Q Q' lQ) /\(on_line O R R' lR)) /\ 
~collinear O P Q /\  ~collinear O P R /\ ~collinear O Q R /\ 
~collinear P Q R /\ ~collinear P' Q' R' /\ ((~P=P')\/(~Q=Q')\/(~R=R')) ->
collinear alpha beta gamma.
Proof.
intros.
unfold on_line in *.
use H.
new_case O.

apply (Desargues_from_A  P Q R P' Q' R' alpha beta gamma lP lQ lR lPQ lPR lQR lP'Q' lP'R' lQ'R');repeat split;eauto.

assert (T:=swaped_B'.Desargues_from_A).
unfold swaped_B'.on_line, swaped_B'.collinear,  swaped_B.A, swaped_B.Incid, swaped_B.Line, swaped_B.Point in *.
eapply (T P Q R P' Q' R' alpha beta gamma lP lQ lR lPQ lPR lQR lP'Q' lP'R' lQ'R').
repeat split;auto.

assert (T:=swaped_C'.Desargues_from_A).
unfold swaped_C'.on_line, swaped_C'.collinear,  swaped_C.A, swaped_C.Incid, swaped_C.Line, swaped_C.Point in *.
unfold swaped_E.A, swaped_E.Incid, swaped_E.Line, swaped_E.Point in *.
unfold  swaped_B.A, swaped_B.Incid, swaped_B.Line, swaped_B.Point in *.
eapply (T P Q R P' Q' R' alpha beta gamma lP lQ lR lPQ lPR lQR lP'Q' lP'R' lQ'R').
repeat split;auto.

assert (T:=swaped_D'.Desargues_from_A).
unfold swaped_D'.on_line, swaped_D'.collinear,  swaped_D.A, swaped_D.Incid, swaped_D.Line, swaped_D.Point in *.
unfold swaped_C.A, swaped_C.Incid, swaped_C.Line, swaped_C.Point in *.
unfold swaped_E.A, swaped_E.Incid, swaped_E.Line, swaped_E.Point in *.
unfold  swaped_B.A, swaped_B.Incid, swaped_B.Line, swaped_B.Point in *.
eapply (T P Q R P' Q' R' alpha beta gamma lP lQ lR lPQ lPR lQR lP'Q' lP'R' lQ'R').
repeat split;auto.

assert (T:=swaped_E'.Desargues_from_A).
unfold swaped_E'.on_line, swaped_E'.collinear,  swaped_E.A, swaped_E.Incid, swaped_E.Line, swaped_E.Point in *.
unfold   swaped_B.B, swaped_B.Incid, swaped_B.Line, swaped_B.Point in *.
eapply (T P Q R P' Q' R' alpha beta gamma lP lQ lR lPQ lPR lQR lP'Q' lP'R' lQ'R').
repeat split;auto.

assert (T:=swaped_F'.Desargues_from_A).
unfold swaped_F'.on_line, swaped_F'.collinear,  swaped_F.A, swaped_F.Incid, swaped_F.Line, swaped_F.Point in *.
unfold swaped_D.A, swaped_D.Incid, swaped_D.Line, swaped_D.Point in *.
unfold swaped_C.A, swaped_C.Incid, swaped_C.Line, swaped_C.Point in *.
unfold swaped_E.A, swaped_E.Incid, swaped_E.Line, swaped_E.Point in *.
unfold  swaped_B.A, swaped_B.Incid, swaped_B.Line, swaped_B.Point in *.
eapply (T P Q R P' Q' R' alpha beta gamma lP lQ lR lPQ lPR lQR lP'Q' lP'R' lQ'R').
repeat split;auto.

assert (T:=swaped_G'.Desargues_from_A).
unfold swaped_G'.on_line, swaped_G'.collinear in *.
unfold  swaped_G.A, swaped_G.Incid, swaped_G.Line, swaped_G.Point in *.
unfold swaped_F'.on_line, swaped_F'.collinear,  swaped_F.A, swaped_F.Incid, swaped_F.Line, swaped_F.Point in *.
unfold swaped_D.A, swaped_D.Incid, swaped_D.Line, swaped_D.Point in *.
unfold swaped_C.A, swaped_C.Incid, swaped_C.Line, swaped_C.Point in *.
unfold swaped_E.A, swaped_E.Incid, swaped_E.Line, swaped_E.Point in *.
unfold  swaped_B.A, swaped_B.Incid, swaped_B.Line, swaped_B.Point in *.
eapply (T P Q R P' Q' R' alpha beta gamma lP lQ lR lPQ lPR lQR lP'Q' lP'R' lQ'R').
repeat split;auto.
Qed.

End Desargues.