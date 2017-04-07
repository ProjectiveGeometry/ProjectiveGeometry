Require Export general_tactics.

(*****************************************************************************)
(** Fano plane PG23 **)

Module Type fano_plane_pg23.

Parameter Point:Set.
Parameter A B C D E F G H I J K L M: Point.

Parameter Line: Set.
Parameter ABCD AEFG AIJM AHKL BEHI BGJL BFKM CELM CFHJ CGIK DEJK DGHM DFIL : Line.

Parameter Incid : Point -> Line -> Prop.

Axiom is_only_13_pts : forall P:Point, {P=A}+{P=B}+{P=C}+{P=D}+{P=E}+{P=F}+{P=G}+{P=H}+{P=I}+{P=J}+{P=K}+{P=L}+{P=M}.

Axiom is_only_13_lines : forall P:Line, {P=ABCD}+{P=AEFG}+{P=AIJM}+{P=AHKL}+{P=BEHI}+{P=BGJL}+{P=BFKM}+{P=CELM}+{P=CFHJ}+{P=CGIK}+{P=DEJK}+{P=DGHM}+{P=DFIL}.

Definition is_fano_plane A B C D E F G H I J K L M ABCD AEFG AIJM AHKL BEHI BGJL BFKM CELM CFHJ CGIK DEJK DGHM DFIL :=
(~A=B /\ ~A=C /\ ~A=D /\ ~A=E /\ ~A=F /\ ~A=G /\ ~A=H /\ ~A=I /\ ~A=J /\ ~A=K /\ ~A=L /\ ~A=M /\
~B=C /\ ~B=D /\ ~B=E /\ ~B=F /\ ~B=G /\ ~B=H /\ ~B=I /\ ~B=J /\ ~B=K /\ ~B=L /\ ~B=M /\
~C=D /\ ~C=E /\ ~C=F /\ ~C=G /\ ~C=H /\ ~C=I /\ ~C=J /\ ~C=K /\ ~C=L /\ ~C=M /\
~D=E /\ ~D=F /\ ~D=G /\ ~D=H /\ ~D=I /\ ~D=J /\ ~D=K /\ ~D=L /\ ~D=M /\
~E=F /\ ~E=G /\ ~E=H /\ ~E=I /\ ~E=J /\ ~E=K /\ ~E=L /\ ~E=M /\
~F=G /\ ~F=H /\ ~F=I /\ ~F=J /\ ~F=K /\ ~F=L /\ ~F=M /\
~G=H /\ ~G=I /\ ~G=J /\ ~G=K /\ ~G=L /\ ~G=M /\
~H=I /\ ~H=J /\ ~H=K /\ ~H=L /\ ~H=M /\
~I=J /\ ~I=K /\ ~I=L /\ ~I=M /\
~J=K /\ ~J=L /\ ~J=M /\
~K=L /\ ~K=M /\
~L=M) /\
(ABCD<>AEFG /\ ABCD<>AIJM /\ ABCD<>AHKL /\ ABCD<>BEHI /\ ABCD<>BGJL /\ ABCD<>BFKM /\ ABCD<>CELM /\ ABCD<>CFHJ /\ ABCD<>CGIK /\ ABCD<>DEJK /\ ABCD<>DGHM /\ ABCD<>DFIL /\
AEFG<>AIJM /\ AEFG<>AHKL /\ AEFG<>BEHI /\ AEFG<>BGJL /\ AEFG<>BFKM /\ AEFG<>CELM /\ AEFG<>CFHJ /\ AEFG<>CGIK /\ AEFG<>DEJK /\ AEFG<>DGHM /\ AEFG<>DFIL /\
AIJM<>AHKL /\ AIJM<>BEHI /\ AIJM<>BGJL /\ AIJM<>BFKM /\ AIJM<>CELM /\ AIJM<>CFHJ /\ AIJM<>CGIK /\ AIJM<>DEJK /\ AIJM<>DGHM /\ AIJM<>DFIL /\
AHKL<>BEHI /\ AHKL<>BGJL /\ AHKL<>BFKM /\ AHKL<>CELM /\ AHKL<>CFHJ /\ AHKL<>CGIK /\ AHKL<>DEJK /\ AHKL<>DGHM /\ AHKL<>DFIL /\
BEHI<>BGJL /\ BEHI<>BFKM /\ BEHI<>CELM /\ BEHI<>CFHJ /\ BEHI<>CGIK /\ BEHI<>DEJK /\ BEHI<>DGHM /\ BEHI<>DFIL /\
BGJL<>BFKM /\ BGJL<>CELM /\ BGJL<>CFHJ /\ BGJL<>CGIK /\ BGJL<>DEJK /\ BGJL<>DGHM /\ BGJL<>DFIL /\
BFKM<>CELM /\ BFKM<>CFHJ /\ BFKM<>CGIK /\ BFKM<>DEJK /\ BFKM<>DGHM /\ BFKM<>DFIL /\
CELM<>CFHJ /\ CELM<>CGIK /\ CELM<>DEJK /\ CELM<>DGHM /\ CELM<>DFIL /\
CFHJ<>CGIK /\ CFHJ<>DEJK /\ CFHJ<>DGHM /\ CFHJ<>DFIL /\
CGIK<>DEJK /\ CGIK<>DGHM /\ CGIK<>DFIL /\
DEJK<>DGHM /\ DEJK<>DFIL /\
DGHM<>DFIL) /\
( Incid A ABCD /\ Incid A AEFG /\ Incid A AIJM /\ Incid A AHKL /\ ~Incid A BEHI /\ ~Incid A BGJL /\ ~Incid A BFKM /\ ~Incid A CELM /\ ~Incid A CFHJ /\ ~Incid A CGIK /\ ~Incid A DEJK /\ ~Incid A DGHM /\ ~Incid A DFIL /\
Incid B ABCD /\ ~Incid B AEFG /\ ~Incid B AIJM /\ ~Incid B AHKL /\ Incid B BEHI /\ Incid B BGJL /\ Incid B BFKM /\ ~Incid B CELM /\ ~Incid B CFHJ /\ ~Incid B CGIK /\ ~Incid B DEJK /\ ~Incid B DGHM /\ ~Incid B DFIL /\
Incid C ABCD /\ ~Incid C AEFG /\ ~Incid C AIJM /\ ~Incid C AHKL /\ ~Incid C BEHI /\ ~Incid C BGJL /\ ~Incid C BFKM /\ Incid C CELM /\ Incid C CFHJ /\ Incid C CGIK /\ ~Incid C DEJK /\ ~Incid C DGHM /\ ~Incid C DFIL /\
Incid D ABCD /\ ~Incid D AEFG /\ ~Incid D AIJM /\ ~Incid D AHKL /\ ~Incid D BEHI /\ ~Incid D BGJL /\ ~Incid D BFKM /\ ~Incid D CELM /\ ~Incid D CFHJ /\ ~Incid D CGIK /\ Incid D DEJK /\ Incid D DGHM /\ Incid D DFIL /\
~Incid E ABCD /\ Incid E AEFG /\ ~Incid E AIJM /\ ~Incid E AHKL /\ Incid E BEHI /\ ~Incid E BGJL /\ ~Incid E BFKM /\ Incid E CELM /\ ~Incid E CFHJ /\ ~Incid E CGIK /\ Incid E DEJK /\ ~Incid E DGHM /\ ~Incid E DFIL /\
~Incid F ABCD /\ Incid F AEFG /\ ~Incid F AIJM /\ ~Incid F AHKL /\ ~Incid F BEHI /\ ~Incid F BGJL /\ Incid F BFKM /\ ~Incid F CELM /\ Incid F CFHJ /\ ~Incid F CGIK /\ ~Incid F DEJK /\ ~Incid F DGHM /\ Incid F DFIL /\
~Incid G ABCD /\ Incid G AEFG /\ ~Incid G AIJM /\ ~Incid G AHKL /\ ~Incid G BEHI /\ Incid G BGJL /\ ~Incid G BFKM /\ ~Incid G CELM /\ ~Incid G CFHJ /\ Incid G CGIK /\ ~Incid G DEJK /\ Incid G DGHM /\ ~Incid G DFIL /\
~Incid H ABCD /\ ~Incid H AEFG /\ ~Incid H AIJM /\ Incid H AHKL /\ Incid H BEHI /\ ~Incid H BGJL /\ ~Incid H BFKM /\ ~Incid H CELM /\ Incid H CFHJ /\ ~Incid H CGIK /\ ~Incid H DEJK /\ Incid H DGHM /\ ~Incid H DFIL /\
~Incid I ABCD /\ ~Incid I AEFG /\ Incid I AIJM /\ ~Incid I AHKL /\ Incid I BEHI /\ ~Incid I BGJL /\ ~Incid I BFKM /\ ~Incid I CELM /\ ~Incid I CFHJ /\ Incid I CGIK /\ ~Incid I DEJK /\ ~Incid I DGHM /\ Incid I DFIL /\
~Incid J ABCD /\ ~Incid J AEFG /\ Incid J AIJM /\ ~Incid J AHKL /\ ~Incid J BEHI /\ Incid J BGJL /\ ~Incid J BFKM /\ ~Incid J CELM /\ Incid J CFHJ /\ ~Incid J CGIK /\ Incid J DEJK /\ ~Incid J DGHM /\ ~Incid J DFIL /\
~Incid K ABCD /\ ~Incid K AEFG /\ ~Incid K AIJM /\ Incid K AHKL /\ ~Incid K BEHI /\ ~Incid K BGJL /\ Incid K BFKM /\ ~Incid K CELM /\ ~Incid K CFHJ /\ Incid K CGIK /\ Incid K DEJK /\ ~Incid K DGHM /\ ~Incid K DFIL /\
~Incid L ABCD /\ ~Incid L AEFG /\ ~Incid L AIJM /\ Incid L AHKL /\ ~Incid L BEHI /\ Incid L BGJL /\ ~Incid L BFKM /\ Incid L CELM /\ ~Incid L CFHJ /\ ~Incid L CGIK /\ ~Incid L DEJK /\ ~Incid L DGHM /\ Incid L DFIL /\
~Incid M ABCD /\ ~Incid M AEFG /\ Incid M AIJM /\ ~Incid M AHKL /\ ~Incid M BEHI /\ ~Incid M BGJL /\ Incid M BFKM /\ Incid M CELM /\ ~Incid M CFHJ /\ ~Incid M CGIK /\ ~Incid M DEJK /\ Incid M DGHM /\ ~Incid M DFIL).

Axiom is_fano_plane_inst :  is_fano_plane A B C D E F G H I J K L M ABCD AEFG AIJM AHKL BEHI BGJL BFKM CELM CFHJ CGIK DEJK DGHM DFIL.

End fano_plane_pg23.

(*****************************************************************************)
(** Fano plane pg23 swap **)

Module swapf3 (M:fano_plane_pg23) : fano_plane_pg23
with Definition Point:=M.Point

with Definition A:=M.B
with Definition B:=M.E
with Definition C:=M.I
with Definition D:=M.H
with Definition E:=M.L
with Definition F:=M.G
with Definition G:=M.J
with Definition H:=M.C
with Definition I:=M.M
with Definition J:=M.K
with Definition K:=M.A
with Definition L:=M.D
with Definition M:=M.F

with Definition Line:=M.Line

with Definition ABCD:=M.BEHI
with Definition AEFG:=M.BGJL
with Definition AIJM:=M.BFKM
with Definition AHKL:=M.ABCD
with Definition BEHI:=M.CELM
with Definition BGJL:=M.DEJK
with Definition BFKM:=M.AEFG
with Definition CELM:=M.DFIL
with Definition CFHJ:=M.CGIK
with Definition CGIK:=M.AIJM
with Definition DEJK:=M.AHKL
with Definition DGHM:=M.CFHJ
with Definition DFIL:=M.DGHM

with Definition Incid :=M.Incid

with Definition is_fano_plane := M.is_fano_plane.

Definition Point:=M.Point.

Definition A:=M.B.
Definition B:=M.E.
Definition C:=M.I.
Definition D:=M.H.
Definition E:=M.L.
Definition F:=M.G.
Definition G:=M.J.
Definition H:=M.C.
Definition I:=M.M.
Definition J:=M.K.
Definition K:=M.A.
Definition L:=M.D.
Definition M:=M.F.

Definition Line:=M.Line.

Definition ABCD:=M.BEHI.
Definition AEFG:=M.BGJL.
Definition AIJM:=M.BFKM.
Definition AHKL:=M.ABCD.
Definition BEHI:=M.CELM.
Definition BGJL:=M.DEJK.
Definition BFKM:=M.AEFG.
Definition CELM:=M.DFIL.
Definition CFHJ:=M.CGIK.
Definition CGIK:=M.AIJM.
Definition DEJK:=M.AHKL.
Definition DGHM:=M.CFHJ.
Definition DFIL:=M.DGHM.

Definition Incid :=M.Incid.

Definition is_fano_plane := M.is_fano_plane.

Lemma is_only_13_pts : forall P:Point, {P=A}+{P=B}+{P=C}+{P=D}+{P=E}+{P=F}+{P=G}+{P=H}+{P=I}+{P=J}+{P=K}+{P=L}+{P=M}.
Proof.
generalize (M.is_only_13_pts).
unfold A, B,C, D, E, F, G, H, I, J, K, L, M.
intros H P; elim (H P).
intuition.
intuition.
Qed.

Lemma is_only_13_lines : forall P:Line, {P=ABCD}+{P=AEFG}+{P=AIJM}+{P=AHKL}+{P=BEHI}+{P=BGJL}+{P=BFKM}+{P=CELM}+{P=CFHJ}+{P=CGIK}+{P=DEJK}+{P=DGHM}+{P=DFIL}.
Proof.
generalize (M.is_only_13_lines).
unfold ABCD, AEFG, AIJM, AHKL, BEHI, BGJL, BFKM, CELM, CFHJ, CGIK, DEJK, DGHM, DFIL.
intros H P;
generalize (H P); intuition.
Qed.

Lemma is_fano_plane_inst : is_fano_plane A B C D E F G H I J K L M ABCD AEFG AIJM AHKL BEHI BGJL BFKM CELM CFHJ CGIK DEJK DGHM DFIL.
Proof.
generalize (M.is_fano_plane_inst).
unfold is_fano_plane, M.is_fano_plane.
intros H; decompose [and] H; clear H.
unfold A, B,C, D, E, F, G, H, I, J, K, L, M, ABCD, AEFG, AIJM, AHKL, BEHI, BGJL, BFKM, CELM, CFHJ, CGIK, DEJK, DGHM, DFIL.
repeat split;try assumption;try auto.
Qed.

End swapf3.


Module Desargues_from_A (M:fano_plane_pg23).

Import M.

Definition on_line := fun A B C l => M.Incid A l /\ Incid B l /\ Incid C l.
Definition collinear A B C :=  exists l, Incid A l /\ Incid B l /\ Incid C l.

Ltac use H := decompose [and ex] H; clear H.

Ltac solve_ex L := solve [exists L;auto].

(** A tactic which tries all possible lines **)

Ltac solve_ex_l := first [solve_ex ABCD
     |  solve_ex AEFG
     |  solve_ex AIJM
     |  solve_ex AHKL
     |  solve_ex BEHI
     |  solve_ex BGJL
     |  solve_ex BFKM
     |  solve_ex CELM
     |  solve_ex CFHJ
     |  solve_ex CGIK
     |  solve_ex DEJK
     |  solve_ex DGHM
     |  solve_ex DFIL
 ].

Ltac solve_ex_p := first [
        solve_ex A
     |  solve_ex B
     |  solve_ex C
     |  solve_ex D
     |  solve_ex E
     |  solve_ex F
     |  solve_ex G
     |  solve_ex H
     |  solve_ex I
     |  solve_ex J
     |  solve_ex K
     |  solve_ex L
     |  solve_ex M
 ].

Ltac new_case P := 
match (type of P) with 
| Point => generalize (is_only_13_pts P) ; let Q := fresh in (intros Q; decompose [sumor sumbool] Q; clear Q; subst)
| Line => generalize (is_only_13_lines P) ; let Q := fresh in (intros Q; decompose [sumor sumbool] Q; clear Q; subst)
end.

Lemma col_degen_1 : forall P R, ~ collinear P P R -> False.
Proof.
intros.
apply H0.
unfold collinear in *.
generalize (is_fano_plane_inst); unfold is_fano_plane in *;
intro Hw ;use Hw;new_case P; new_case R;solve_ex_l.
Qed.

Lemma col_degen_2 : forall P R, 
~ collinear P R P -> False.
Proof.
intros.
apply H0.
unfold collinear.
generalize (is_fano_plane_inst); unfold is_fano_plane in *; intro Hw ;use Hw; 
new_case P;new_case R;solve_ex_l.
Qed.

Lemma col_degen_3 : forall P R, 
~ collinear R P P -> False.
Proof.
intros.
apply H0.
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

Ltac case_clear P := case_eq_s P;try solve [degens].

Ltac fano_ctx := generalize (is_fano_plane_inst); unfold is_fano_plane in *; let Hw := fresh in (intro Hw ;use Hw).

Lemma collinearPPQ : forall P Q: Point, collinear P P Q.
Proof.
intros P; generalize (is_fano_plane_inst); unfold is_fano_plane in *; intro Hw ;use Hw; new_case P; intros Q; new_case Q;unfold collinear; 
solve_ex_l.
Qed.

Lemma collinearPQQ : forall P Q: Point, collinear P Q Q.
Proof.
intros P; generalize (is_fano_plane_inst); unfold is_fano_plane in *; intro Hw ;use Hw; new_case P; intros Q; new_case Q; unfold collinear; 
solve_ex_l.
Qed.

Lemma collinearPQP : forall P Q: Point, collinear P Q P.
Proof.
intros P; generalize (is_fano_plane_inst); unfold is_fano_plane in *; intro Hw ;use Hw;new_case P; intros Q; new_case Q; unfold collinear; 
solve_ex_l.
Qed.

Ltac cols :=  apply collinearPPQ ||
              apply collinearPQQ ||
              apply collinearPQP ||
              (unfold collinear;solve_ex_l).

Ltac collinear_line :=
match goal with 
H : ~collinear ?P ?Q ?R |- _ => 
  solve[assert (collinear P Q R) by (solve_ex_l); 
cut False; [intros Hf; elim Hf | auto]] 
end.

Ltac collinear_line_gen ABCD AEFG AIJM AHKL BEHI BGJL BFKM CELM CFHJ CGIK DEJK DGHM DFIL :=
match goal with 
H : ~collinear ?P ?Q ?R |- _ => 
  solve [assert (collinear P Q R) by (solve_ex_l); 
cut False; [intros Hf; elim Hf | auto]] 
end.

End Desargues_from_A.

(** Combinatorial explosion by proving Desargues ! **)

(*

Lemma Desargues_from_A_spec :  forall P Q R P' Q' R' alpha beta gamma lPQ lPR lQR lP'Q' lP'R' lQ'R',
((on_line P Q gamma lPQ) /\ (on_line P' Q' gamma lP'Q')) /\
((on_line P R beta lPR) /\ (on_line P' R' beta lP'R')) /\
((on_line Q R alpha lQR) /\ (on_line Q' R' alpha lQ'R')) /\
((on_line A P P' ABCD) /\ (on_line A Q Q' AEFG) /\(on_line A R R' AIJM)) /\ 
~collinear A P Q /\  ~collinear A P R /\ ~collinear A Q R /\ 
~collinear P Q R /\ ~collinear P' Q' R' /\ ((~P=P')\/(~Q=Q')\/(~R=R')) ->
collinear alpha beta gamma.
Proof.
intros P Q R P' Q' R' alpha beta gamma lPQ lPR lQR lP'Q' lP'R' lQ'R'.
intros.
unfold on_line in  *;use H0.
generalize (is_fano_plane_inst); unfold is_fano_plane in *; intro Hw ;use Hw.

time(case_clear P;
case_clear Q;
case_clear R;
try collinear_line;
case_clear P';
case_clear Q';
case_clear R';
try collinear_line).
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
try cols).
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

*)