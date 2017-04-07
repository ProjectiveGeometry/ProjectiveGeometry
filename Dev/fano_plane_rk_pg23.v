Require Export ProjectiveGeometry.Dev.fano_rk_tactics.

(*****************************************************************************)
(** Fano plane rank **)

Module Type fano_plane_rank.

Parameter A B C D E F G H I J K L M : Point.

Parameter is_only_13_pts : forall P, {P=A}+{P=B}+{P=C}+{P=D}+{P=E}+{P=F}+{P=G}+{P=H}+{P=I}+{P=J}+{P=K}+{P=L}+{P=M}.

Parameter rk_points : rk(A :: nil) = 1 /\ rk(B :: nil) = 1 /\ rk(C :: nil) = 1 /\ rk(D :: nil) = 1 /\
rk(E :: nil) = 1 /\ rk(F :: nil) = 1 /\ rk(G :: nil) = 1 /\ rk(H :: nil) = 1 /\ rk(I :: nil) = 1 /\ 
rk(J :: nil) = 1 /\ rk(K :: nil) = 1 /\ rk(L :: nil) = 1 /\ rk(M :: nil) = 1.

Parameter rk_distinct_points : 
rk(A :: B :: nil) = 2 /\ rk(A :: C :: nil) = 2 /\ rk(A :: D :: nil) = 2 /\ rk(A :: E :: nil) = 2 /\ rk(A :: F :: nil) = 2 /\ rk(A :: G :: nil) = 2 /\
rk(A :: H :: nil) = 2 /\ rk(A :: I :: nil) = 2 /\ rk(A :: J :: nil) = 2 /\ rk(A :: K :: nil) = 2 /\ rk(A :: L :: nil) = 2 /\ rk(A :: M :: nil) = 2 /\
rk(B :: C :: nil) = 2 /\ rk(B :: D :: nil) = 2 /\ rk(B :: E :: nil) = 2 /\ rk(B :: F :: nil) = 2 /\ rk(B :: G :: nil) = 2 /\
rk(B :: H :: nil) = 2 /\ rk(B :: I :: nil) = 2 /\ rk(B :: J :: nil) = 2 /\ rk(B :: K :: nil) = 2 /\ rk(B :: L :: nil) = 2 /\ rk(B :: M :: nil) = 2 /\
rk(C :: D :: nil) = 2 /\ rk(C :: E :: nil) = 2 /\ rk(C :: F :: nil) = 2 /\ rk(C :: G :: nil) = 2 /\
rk(C :: H :: nil) = 2 /\ rk(C :: I :: nil) = 2 /\ rk(C :: J :: nil) = 2 /\ rk(C :: K :: nil) = 2 /\ rk(C :: L :: nil) = 2 /\ rk(C :: M :: nil) = 2 /\
rk(D :: E :: nil) = 2 /\ rk(D :: F :: nil) = 2 /\ rk(D :: G :: nil) = 2 /\
rk(D :: H :: nil) = 2 /\ rk(D :: I :: nil) = 2 /\ rk(D :: J :: nil) = 2 /\ rk(D :: K :: nil) = 2 /\ rk(D :: L :: nil) = 2 /\ rk(D :: M :: nil) = 2 /\
rk(E :: F :: nil) = 2 /\ rk(E :: G :: nil) = 2 /\
rk(E :: H :: nil) = 2 /\ rk(E :: I :: nil) = 2 /\ rk(E :: J :: nil) = 2 /\ rk(E :: K :: nil) = 2 /\ rk(E :: L :: nil) = 2 /\ rk(E :: M :: nil) = 2 /\
rk(F :: G :: nil) = 2 /\
rk(F :: H :: nil) = 2 /\ rk(F :: I :: nil) = 2 /\ rk(F :: J :: nil) = 2 /\ rk(F :: K :: nil) = 2 /\ rk(F :: L :: nil) = 2 /\ rk(F :: M :: nil) = 2 /\
rk(G :: H :: nil) = 2 /\ rk(G :: I :: nil) = 2 /\ rk(G :: J :: nil) = 2 /\ rk(G :: K :: nil) = 2 /\ rk(G :: L :: nil) = 2 /\ rk(G :: M :: nil) = 2 /\
rk(H :: I :: nil) = 2 /\ rk(H :: J :: nil) = 2 /\ rk(H :: K :: nil) = 2 /\ rk(H :: L :: nil) = 2 /\ rk(H :: M :: nil) = 2 /\
rk(I :: J :: nil) = 2 /\ rk(I :: K :: nil) = 2 /\ rk(I :: L :: nil) = 2 /\ rk(I :: M :: nil) = 2 /\
rk(J :: K :: nil) = 2 /\ rk(J :: L :: nil) = 2 /\ rk(J :: M :: nil) = 2 /\
rk(K :: L :: nil) = 2 /\ rk(K :: M :: nil) = 2 /\
rk(L :: M :: nil) = 2.

Parameter rk_lines :
rk (A :: B :: C :: D :: nil) = 2 /\ rk (A :: E :: F :: G :: nil) = 2 /\
rk (A :: I :: J :: M :: nil) = 2 /\ rk (A :: H :: K :: L :: nil) = 2 /\
rk (B :: E :: H :: I :: nil) = 2 /\ rk (B :: G :: J :: L :: nil) = 2 /\
rk (B :: F :: K :: M :: nil) = 2 /\ rk (D :: E :: J :: K :: nil) = 2 /\
rk (C :: E :: L :: M :: nil) = 2 /\ rk (C :: F :: H :: J :: nil) = 2 /\
rk (D :: G :: H :: M :: nil) = 2 /\ rk (D :: F :: I :: L :: nil) = 2 /\
rk (C :: G :: I :: K :: nil) = 2.

Parameter rk_planes :
rk (A :: B :: E :: nil) = 3 /\ rk (A :: B :: F :: nil) = 3 /\ rk (A :: B :: G :: nil) = 3 /\
rk (A :: B :: H :: nil) = 3 /\ rk (A :: B :: I :: nil) = 3 /\ rk (A :: B :: J :: nil) = 3 /\
rk (A :: B :: K :: nil) = 3 /\ rk (A :: B :: L :: nil) = 3 /\ rk (A :: B :: M :: nil) = 3 /\
rk (A :: C :: E :: nil) = 3 /\ rk (A :: C :: F :: nil) = 3 /\ rk (A :: C :: G :: nil) = 3 /\
rk (A :: C :: H :: nil) = 3 /\ rk (A :: C :: I :: nil) = 3 /\ rk (A :: C :: J :: nil) = 3 /\
rk (A :: C :: K :: nil) = 3 /\ rk (A :: C :: L :: nil) = 3 /\ rk (A :: C :: M :: nil) = 3 /\
rk (A :: D :: E :: nil) = 3 /\ rk (A :: D :: F :: nil) = 3 /\ rk (A :: D :: G :: nil) = 3 /\
rk (A :: D :: H :: nil) = 3 /\ rk (A :: D :: I :: nil) = 3 /\ rk (A :: D :: J :: nil) = 3 /\
rk (A :: D :: K :: nil) = 3 /\ rk (A :: D :: L :: nil) = 3 /\ rk (A :: D :: M :: nil) = 3 /\
rk (A :: E :: H :: nil) = 3 /\ rk (A :: E :: I :: nil) = 3 /\ rk (A :: E :: J :: nil) = 3 /\
rk (A :: E :: K :: nil) = 3 /\ rk (A :: E :: L :: nil) = 3 /\ rk (A :: E :: M :: nil) = 3 /\
rk (A :: F :: H :: nil) = 3 /\ rk (A :: F :: I :: nil) = 3 /\ rk (A :: F :: J :: nil) = 3 /\
rk (A :: F :: K :: nil) = 3 /\ rk (A :: F :: L :: nil) = 3 /\ rk (A :: F :: M :: nil) = 3 /\
rk (A :: G :: H :: nil) = 3 /\ rk (A :: G :: I :: nil) = 3 /\ rk (A :: G :: J :: nil) = 3 /\
rk (A :: G :: K :: nil) = 3 /\ rk (A :: G :: L :: nil) = 3 /\ rk (A :: G :: M :: nil) = 3 /\
rk (A :: H :: I :: nil) = 3 /\ rk (A :: H :: J :: nil) = 3 /\ rk (A :: H :: M :: nil) = 3 /\
rk (A :: I :: K :: nil) = 3 /\ rk (A :: I :: L :: nil) = 3 /\
rk (A :: J :: K :: nil) = 3 /\ rk (A :: J :: L :: nil) = 3 /\
rk (A :: K :: M :: nil) = 3 /\
rk (A :: L :: M :: nil) = 3 /\
rk (B :: C :: E :: nil) = 3 /\ rk (B :: C :: F :: nil) = 3 /\ rk (B :: C :: G :: nil) = 3 /\
rk (B :: C :: H :: nil) = 3 /\ rk (B :: C :: I :: nil) = 3 /\ rk (B :: C :: J :: nil) = 3 /\
rk (B :: C :: K :: nil) = 3 /\ rk (B :: C :: L :: nil) = 3 /\ rk (B :: C :: M :: nil) = 3 /\
rk (B :: D :: E :: nil) = 3 /\ rk (B :: D :: F :: nil) = 3 /\ rk (B :: D :: G :: nil) = 3 /\
rk (B :: D :: H :: nil) = 3 /\ rk (B :: D :: I :: nil) = 3 /\ rk (B :: D :: J :: nil) = 3 /\
rk (B :: D :: K :: nil) = 3 /\ rk (B :: D :: L :: nil) = 3 /\ rk (B :: D :: M :: nil) = 3 /\
rk (B :: E :: F :: nil) = 3 /\ rk (B :: E :: G :: nil) = 3 /\ rk (B :: E :: J :: nil) = 3 /\
rk (B :: E :: K :: nil) = 3 /\ rk (B :: E :: L :: nil) = 3 /\ rk (B :: E :: M :: nil) = 3 /\
rk (B :: F :: G :: nil) = 3 /\ rk (B :: F :: H :: nil) = 3 /\ rk (B :: F :: I :: nil) = 3 /\
rk (B :: F :: J :: nil) = 3 /\ rk (B :: F :: L :: nil) = 3 /\
rk (B :: G :: H :: nil) = 3 /\ rk (B :: G :: I :: nil) = 3 /\ rk (B :: G :: K :: nil) = 3 /\
rk (B :: G :: M :: nil) = 3 /\
rk (B :: H :: J :: nil) = 3 /\ rk (B :: H :: K :: nil) = 3 /\ rk (B :: H :: L :: nil) = 3 /\
rk (B :: H :: M :: nil) = 3 /\
rk (B :: I :: J :: nil) = 3 /\ rk (B :: I :: K :: nil) = 3 /\ rk (B :: I :: L :: nil) = 3 /\
rk (B :: I :: M :: nil) = 3 /\
rk (B :: J :: K :: nil) = 3 /\ rk (B :: J :: M :: nil) = 3 /\
rk (B :: K :: L :: nil) = 3 /\
rk (B :: L :: M :: nil) = 3 /\
rk (C :: D :: E :: nil) = 3 /\ rk (C :: D :: F :: nil) = 3 /\ rk (C :: D :: G :: nil) = 3 /\
rk (C :: D :: H :: nil) = 3 /\ rk (C :: D :: I :: nil) = 3 /\ rk (C :: D :: J :: nil) = 3 /\
rk (C :: D :: K :: nil) = 3 /\ rk (C :: D :: L :: nil) = 3 /\ rk (C :: D :: M :: nil) = 3 /\
rk (C :: E :: F :: nil) = 3 /\ rk (C :: E :: G :: nil) = 3 /\ rk (C :: E :: H :: nil) = 3 /\
rk (C :: E :: I :: nil) = 3 /\ rk (C :: E :: J :: nil) = 3 /\ rk (C :: E :: K :: nil) = 3 /\
rk (C :: F :: G :: nil) = 3 /\ rk (C :: F :: I :: nil) = 3 /\ rk (C :: F :: K :: nil) = 3 /\
rk (C :: F :: L :: nil) = 3 /\ rk (C :: F :: M :: nil) = 3 /\
rk (C :: G :: H :: nil) = 3 /\ rk (C :: G :: J :: nil) = 3 /\ rk (C :: G :: L :: nil) = 3 /\
rk (C :: G :: M :: nil) = 3 /\
rk (C :: H :: I :: nil) = 3 /\ rk (C :: H :: K :: nil) = 3 /\ rk (C :: H :: L :: nil) = 3 /\
rk (C :: H :: M :: nil) = 3 /\
rk (C :: I :: J :: nil) = 3 /\ rk (C :: I :: L :: nil) = 3 /\ rk (C :: I :: M :: nil) = 3 /\
rk (C :: J :: K :: nil) = 3 /\ rk (C :: J :: L :: nil) = 3 /\ rk (C :: J :: M :: nil) = 3 /\
rk (C :: K :: L :: nil) = 3 /\ rk (C :: K :: M :: nil) = 3 /\ rk (C :: K :: L :: nil) = 3 /\
rk (D :: E :: F :: nil) = 3 /\ rk (D :: E :: G :: nil) = 3 /\ rk (D :: E :: H :: nil) = 3 /\
rk (D :: E :: I :: nil) = 3 /\ rk (D :: E :: L :: nil) = 3 /\ rk (D :: E :: M :: nil) = 3 /\
rk (D :: F :: G :: nil) = 3 /\ rk (D :: F :: H :: nil) = 3 /\ rk (D :: F :: J :: nil) = 3 /\
rk (D :: F :: K :: nil) = 3 /\ rk (D :: F :: M :: nil) = 3 /\ 
rk (D :: G :: I :: nil) = 3 /\ rk (D :: G :: J :: nil) = 3 /\ rk (D :: G :: K :: nil) = 3 /\
rk (D :: G :: L :: nil) = 3 /\
rk (D :: H :: I :: nil) = 3 /\ rk (D :: H :: J :: nil) = 3 /\ rk (D :: H :: K :: nil) = 3 /\
rk (D :: H :: L :: nil) = 3 /\ 
rk (D :: I :: J :: nil) = 3 /\ rk (D :: I :: K :: nil) = 3 /\ rk (D :: I :: M :: nil) = 3 /\ 
rk (D :: J :: L :: nil) = 3 /\ rk (D :: J :: M :: nil) = 3 /\
rk (D :: K :: L :: nil) = 3 /\ rk (D :: K :: M :: nil) = 3 /\ 
rk (D :: L :: M :: nil) = 3 /\
rk (E :: F :: H :: nil) = 3 /\ rk (E :: F :: I :: nil) = 3 /\ rk (E :: F :: J :: nil) = 3 /\
rk (E :: F :: K :: nil) = 3 /\ rk (E :: F :: L :: nil) = 3 /\ rk (E :: F :: M :: nil) = 3 /\
rk (E :: G :: H :: nil) = 3 /\ rk (E :: G :: I :: nil) = 3 /\ rk (E :: G :: J :: nil) = 3 /\
rk (E :: G :: K :: nil) = 3 /\ rk (E :: G :: L :: nil) = 3 /\ rk (E :: G :: M :: nil) = 3 /\
rk (E :: H :: J :: nil) = 3 /\ rk (E :: H :: K :: nil) = 3 /\ rk (E :: H :: L :: nil) = 3 /\
rk (E :: H :: M :: nil) = 3 /\ 
rk (E :: I :: J :: nil) = 3 /\ rk (E :: I :: K :: nil) = 3 /\ rk (E :: I :: L :: nil) = 3 /\
rk (E :: I :: M :: nil) = 3 /\ 
rk (E :: J :: L :: nil) = 3 /\ rk (E :: J :: M :: nil) = 3 /\ 
rk (E :: K :: L :: nil) = 3 /\ rk (E :: K :: M :: nil) = 3 /\
rk (F :: G :: H :: nil) = 3 /\ rk (F :: G :: I :: nil) = 3 /\ rk (F :: G :: J :: nil) = 3 /\
rk (F :: G :: K :: nil) = 3 /\ rk (F :: G :: L :: nil) = 3 /\ rk (F :: G :: M :: nil) = 3 /\
rk (F :: H :: I :: nil) = 3 /\ rk (F :: H :: K :: nil) = 3 /\ rk (F :: H :: L :: nil) = 3 /\
rk (F :: H :: M :: nil) = 3 /\
rk (F :: I :: J :: nil) = 3 /\ rk (F :: I :: K :: nil) = 3 /\ rk (F :: I :: M :: nil) = 3 /\
rk (F :: J :: K :: nil) = 3 /\ rk (F :: J :: L :: nil) = 3 /\ rk (F :: J :: M :: nil) = 3 /\
rk (F :: K :: L :: nil) = 3 /\
rk (F :: L :: M :: nil) = 3 /\
rk (G :: H :: I :: nil) = 3 /\ rk (G :: H :: J :: nil) = 3 /\ rk (G :: H :: K :: nil) = 3 /\
rk (G :: H :: L :: nil) = 3 /\
rk (G :: I :: J :: nil) = 3 /\ rk (G :: I :: L :: nil) = 3 /\ rk (G :: I :: M :: nil) = 3 /\
rk (G :: J :: K :: nil) = 3 /\ rk (G :: J :: M :: nil) = 3 /\
rk (G :: K :: L :: nil) = 3 /\ rk (G :: K :: M :: nil) = 3 /\
rk (G :: L :: M :: nil) = 3 /\
rk (H :: I :: J :: nil) = 3 /\ rk (H :: I :: K :: nil) = 3 /\ rk (H :: I :: L :: nil) = 3 /\
rk (H :: I :: M :: nil) = 3 /\
rk (H :: J :: K :: nil) = 3 /\ rk (H :: J :: L :: nil) = 3 /\ rk (H :: J :: M :: nil) = 3 /\
rk (H :: K :: M :: nil) = 3 /\
rk (H :: L :: M :: nil) = 3 /\
rk (I :: J :: K :: nil) = 3 /\ rk (I :: J :: L :: nil) = 3 /\
rk (I :: K :: L :: nil) = 3 /\ rk (I :: K :: M :: nil) = 3 /\
rk (I :: L :: M :: nil) = 3 /\
rk (J :: K :: L :: nil) = 3 /\ rk (J :: K :: M :: nil) = 3 /\
rk (J :: L :: M :: nil) = 3 /\
rk (K :: L :: M :: nil) = 3.

End fano_plane_rank.


(*****************************************************************************)




(*****************************************************************************)


Module swapfr3 (M:fano_plane_rank) : fano_plane_rank
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
with Definition M:=M.F.

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

Lemma is_only_13_pts : forall P:Point, {P=A}+{P=B}+{P=C}+{P=D}+{P=E}+{P=F}+{P=G}+{P=H}+{P=I}+{P=J}+{P=K}+{P=L}+{P=M}.
Proof.
generalize (M.is_only_13_pts).
unfold A, B,C, D, E, F, G, H, I, J, K, L, M.
intros H P; elim (H P).
intuition.
intuition.
Qed.

Lemma rk_points : rk(A :: nil) = 1 /\ rk(B :: nil) = 1 /\ rk(C :: nil) = 1 /\ rk(D :: nil) = 1 /\
rk(E :: nil) = 1 /\ rk(F :: nil) = 1 /\ rk(G :: nil) = 1 /\ rk(H :: nil) = 1 /\ rk(I :: nil) = 1 /\ 
rk(J :: nil) = 1 /\ rk(K :: nil) = 1 /\ rk(L :: nil) = 1 /\ rk(M :: nil) = 1.
Proof.
generalize (M.rk_points).
unfold A, B,C, D, E, F, G, H, I, J, K, L, M.
intros;intuition.
Qed.

Lemma rk_distinct_points : 
rk(A :: B :: nil) = 2 /\ rk(A :: C :: nil) = 2 /\ rk(A :: D :: nil) = 2 /\ rk(A :: E :: nil) = 2 /\ rk(A :: F :: nil) = 2 /\ rk(A :: G :: nil) = 2 /\
rk(A :: H :: nil) = 2 /\ rk(A :: I :: nil) = 2 /\ rk(A :: J :: nil) = 2 /\ rk(A :: K :: nil) = 2 /\ rk(A :: L :: nil) = 2 /\ rk(A :: M :: nil) = 2 /\
rk(B :: C :: nil) = 2 /\ rk(B :: D :: nil) = 2 /\ rk(B :: E :: nil) = 2 /\ rk(B :: F :: nil) = 2 /\ rk(B :: G :: nil) = 2 /\
rk(B :: H :: nil) = 2 /\ rk(B :: I :: nil) = 2 /\ rk(B :: J :: nil) = 2 /\ rk(B :: K :: nil) = 2 /\ rk(B :: L :: nil) = 2 /\ rk(B :: M :: nil) = 2 /\
rk(C :: D :: nil) = 2 /\ rk(C :: E :: nil) = 2 /\ rk(C :: F :: nil) = 2 /\ rk(C :: G :: nil) = 2 /\
rk(C :: H :: nil) = 2 /\ rk(C :: I :: nil) = 2 /\ rk(C :: J :: nil) = 2 /\ rk(C :: K :: nil) = 2 /\ rk(C :: L :: nil) = 2 /\ rk(C :: M :: nil) = 2 /\
rk(D :: E :: nil) = 2 /\ rk(D :: F :: nil) = 2 /\ rk(D :: G :: nil) = 2 /\
rk(D :: H :: nil) = 2 /\ rk(D :: I :: nil) = 2 /\ rk(D :: J :: nil) = 2 /\ rk(D :: K :: nil) = 2 /\ rk(D :: L :: nil) = 2 /\ rk(D :: M :: nil) = 2 /\
rk(E :: F :: nil) = 2 /\ rk(E :: G :: nil) = 2 /\
rk(E :: H :: nil) = 2 /\ rk(E :: I :: nil) = 2 /\ rk(E :: J :: nil) = 2 /\ rk(E :: K :: nil) = 2 /\ rk(E :: L :: nil) = 2 /\ rk(E :: M :: nil) = 2 /\
rk(F :: G :: nil) = 2 /\
rk(F :: H :: nil) = 2 /\ rk(F :: I :: nil) = 2 /\ rk(F :: J :: nil) = 2 /\ rk(F :: K :: nil) = 2 /\ rk(F :: L :: nil) = 2 /\ rk(F :: M :: nil) = 2 /\
rk(G :: H :: nil) = 2 /\ rk(G :: I :: nil) = 2 /\ rk(G :: J :: nil) = 2 /\ rk(G :: K :: nil) = 2 /\ rk(G :: L :: nil) = 2 /\ rk(G :: M :: nil) = 2 /\
rk(H :: I :: nil) = 2 /\ rk(H :: J :: nil) = 2 /\ rk(H :: K :: nil) = 2 /\ rk(H :: L :: nil) = 2 /\ rk(H :: M :: nil) = 2 /\
rk(I :: J :: nil) = 2 /\ rk(I :: K :: nil) = 2 /\ rk(I :: L :: nil) = 2 /\ rk(I :: M :: nil) = 2 /\
rk(J :: K :: nil) = 2 /\ rk(J :: L :: nil) = 2 /\ rk(J :: M :: nil) = 2 /\
rk(K :: L :: nil) = 2 /\ rk(K :: M :: nil) = 2 /\
rk(L :: M :: nil) = 2.
Proof.
generalize (M.rk_distinct_points).
unfold A, B,C, D, E, F, G, H, I, J, K, L, M.
intros;intuition;solve[rk_couple_bis_bis].
Qed.

Lemma rk_lines :
rk (A :: B :: C :: D :: nil) = 2 /\ rk (A :: E :: F :: G :: nil) = 2 /\
rk (A :: I :: J :: M :: nil) = 2 /\ rk (A :: H :: K :: L :: nil) = 2 /\
rk (B :: E :: H :: I :: nil) = 2 /\ rk (B :: G :: J :: L :: nil) = 2 /\
rk (B :: F :: K :: M :: nil) = 2 /\ rk (D :: E :: J :: K :: nil) = 2 /\
rk (C :: E :: L :: M :: nil) = 2 /\ rk (C :: F :: H :: J :: nil) = 2 /\
rk (D :: G :: H :: M :: nil) = 2 /\ rk (D :: F :: I :: L :: nil) = 2 /\
rk (C :: G :: I :: K :: nil) = 2.
Proof.
generalize (M.rk_lines).
unfold A, B,C, D, E, F, G, H, I, J, K, L, M.
intros.
my_split.
repeat split;solve[rk_quadruple_bis_bis].
Qed.

Lemma rk_planes :
rk (A :: B :: E :: nil) = 3 /\ rk (A :: B :: F :: nil) = 3 /\ rk (A :: B :: G :: nil) = 3 /\
rk (A :: B :: H :: nil) = 3 /\ rk (A :: B :: I :: nil) = 3 /\ rk (A :: B :: J :: nil) = 3 /\
rk (A :: B :: K :: nil) = 3 /\ rk (A :: B :: L :: nil) = 3 /\ rk (A :: B :: M :: nil) = 3 /\
rk (A :: C :: E :: nil) = 3 /\ rk (A :: C :: F :: nil) = 3 /\ rk (A :: C :: G :: nil) = 3 /\
rk (A :: C :: H :: nil) = 3 /\ rk (A :: C :: I :: nil) = 3 /\ rk (A :: C :: J :: nil) = 3 /\
rk (A :: C :: K :: nil) = 3 /\ rk (A :: C :: L :: nil) = 3 /\ rk (A :: C :: M :: nil) = 3 /\
rk (A :: D :: E :: nil) = 3 /\ rk (A :: D :: F :: nil) = 3 /\ rk (A :: D :: G :: nil) = 3 /\
rk (A :: D :: H :: nil) = 3 /\ rk (A :: D :: I :: nil) = 3 /\ rk (A :: D :: J :: nil) = 3 /\
rk (A :: D :: K :: nil) = 3 /\ rk (A :: D :: L :: nil) = 3 /\ rk (A :: D :: M :: nil) = 3 /\
rk (A :: E :: H :: nil) = 3 /\ rk (A :: E :: I :: nil) = 3 /\ rk (A :: E :: J :: nil) = 3 /\
rk (A :: E :: K :: nil) = 3 /\ rk (A :: E :: L :: nil) = 3 /\ rk (A :: E :: M :: nil) = 3 /\
rk (A :: F :: H :: nil) = 3 /\ rk (A :: F :: I :: nil) = 3 /\ rk (A :: F :: J :: nil) = 3 /\
rk (A :: F :: K :: nil) = 3 /\ rk (A :: F :: L :: nil) = 3 /\ rk (A :: F :: M :: nil) = 3 /\
rk (A :: G :: H :: nil) = 3 /\ rk (A :: G :: I :: nil) = 3 /\ rk (A :: G :: J :: nil) = 3 /\
rk (A :: G :: K :: nil) = 3 /\ rk (A :: G :: L :: nil) = 3 /\ rk (A :: G :: M :: nil) = 3 /\
rk (A :: H :: I :: nil) = 3 /\ rk (A :: H :: J :: nil) = 3 /\ rk (A :: H :: M :: nil) = 3 /\
rk (A :: I :: K :: nil) = 3 /\ rk (A :: I :: L :: nil) = 3 /\
rk (A :: J :: K :: nil) = 3 /\ rk (A :: J :: L :: nil) = 3 /\
rk (A :: K :: M :: nil) = 3 /\
rk (A :: L :: M :: nil) = 3 /\
rk (B :: C :: E :: nil) = 3 /\ rk (B :: C :: F :: nil) = 3 /\ rk (B :: C :: G :: nil) = 3 /\
rk (B :: C :: H :: nil) = 3 /\ rk (B :: C :: I :: nil) = 3 /\ rk (B :: C :: J :: nil) = 3 /\
rk (B :: C :: K :: nil) = 3 /\ rk (B :: C :: L :: nil) = 3 /\ rk (B :: C :: M :: nil) = 3 /\
rk (B :: D :: E :: nil) = 3 /\ rk (B :: D :: F :: nil) = 3 /\ rk (B :: D :: G :: nil) = 3 /\
rk (B :: D :: H :: nil) = 3 /\ rk (B :: D :: I :: nil) = 3 /\ rk (B :: D :: J :: nil) = 3 /\
rk (B :: D :: K :: nil) = 3 /\ rk (B :: D :: L :: nil) = 3 /\ rk (B :: D :: M :: nil) = 3 /\
rk (B :: E :: F :: nil) = 3 /\ rk (B :: E :: G :: nil) = 3 /\ rk (B :: E :: J :: nil) = 3 /\
rk (B :: E :: K :: nil) = 3 /\ rk (B :: E :: L :: nil) = 3 /\ rk (B :: E :: M :: nil) = 3 /\
rk (B :: F :: G :: nil) = 3 /\ rk (B :: F :: H :: nil) = 3 /\ rk (B :: F :: I :: nil) = 3 /\
rk (B :: F :: J :: nil) = 3 /\ rk (B :: F :: L :: nil) = 3 /\
rk (B :: G :: H :: nil) = 3 /\ rk (B :: G :: I :: nil) = 3 /\ rk (B :: G :: K :: nil) = 3 /\
rk (B :: G :: M :: nil) = 3 /\
rk (B :: H :: J :: nil) = 3 /\ rk (B :: H :: K :: nil) = 3 /\ rk (B :: H :: L :: nil) = 3 /\
rk (B :: H :: M :: nil) = 3 /\
rk (B :: I :: J :: nil) = 3 /\ rk (B :: I :: K :: nil) = 3 /\ rk (B :: I :: L :: nil) = 3 /\
rk (B :: I :: M :: nil) = 3 /\
rk (B :: J :: K :: nil) = 3 /\ rk (B :: J :: M :: nil) = 3 /\
rk (B :: K :: L :: nil) = 3 /\
rk (B :: L :: M :: nil) = 3 /\
rk (C :: D :: E :: nil) = 3 /\ rk (C :: D :: F :: nil) = 3 /\ rk (C :: D :: G :: nil) = 3 /\
rk (C :: D :: H :: nil) = 3 /\ rk (C :: D :: I :: nil) = 3 /\ rk (C :: D :: J :: nil) = 3 /\
rk (C :: D :: K :: nil) = 3 /\ rk (C :: D :: L :: nil) = 3 /\ rk (C :: D :: M :: nil) = 3 /\
rk (C :: E :: F :: nil) = 3 /\ rk (C :: E :: G :: nil) = 3 /\ rk (C :: E :: H :: nil) = 3 /\
rk (C :: E :: I :: nil) = 3 /\ rk (C :: E :: J :: nil) = 3 /\ rk (C :: E :: K :: nil) = 3 /\
rk (C :: F :: G :: nil) = 3 /\ rk (C :: F :: I :: nil) = 3 /\ rk (C :: F :: K :: nil) = 3 /\
rk (C :: F :: L :: nil) = 3 /\ rk (C :: F :: M :: nil) = 3 /\
rk (C :: G :: H :: nil) = 3 /\ rk (C :: G :: J :: nil) = 3 /\ rk (C :: G :: L :: nil) = 3 /\
rk (C :: G :: M :: nil) = 3 /\
rk (C :: H :: I :: nil) = 3 /\ rk (C :: H :: K :: nil) = 3 /\ rk (C :: H :: L :: nil) = 3 /\
rk (C :: H :: M :: nil) = 3 /\
rk (C :: I :: J :: nil) = 3 /\ rk (C :: I :: L :: nil) = 3 /\ rk (C :: I :: M :: nil) = 3 /\
rk (C :: J :: K :: nil) = 3 /\ rk (C :: J :: L :: nil) = 3 /\ rk (C :: J :: M :: nil) = 3 /\
rk (C :: K :: L :: nil) = 3 /\ rk (C :: K :: M :: nil) = 3 /\ rk (C :: K :: L :: nil) = 3 /\
rk (D :: E :: F :: nil) = 3 /\ rk (D :: E :: G :: nil) = 3 /\ rk (D :: E :: H :: nil) = 3 /\
rk (D :: E :: I :: nil) = 3 /\ rk (D :: E :: L :: nil) = 3 /\ rk (D :: E :: M :: nil) = 3 /\
rk (D :: F :: G :: nil) = 3 /\ rk (D :: F :: H :: nil) = 3 /\ rk (D :: F :: J :: nil) = 3 /\
rk (D :: F :: K :: nil) = 3 /\ rk (D :: F :: M :: nil) = 3 /\ 
rk (D :: G :: I :: nil) = 3 /\ rk (D :: G :: J :: nil) = 3 /\ rk (D :: G :: K :: nil) = 3 /\
rk (D :: G :: L :: nil) = 3 /\
rk (D :: H :: I :: nil) = 3 /\ rk (D :: H :: J :: nil) = 3 /\ rk (D :: H :: K :: nil) = 3 /\
rk (D :: H :: L :: nil) = 3 /\ 
rk (D :: I :: J :: nil) = 3 /\ rk (D :: I :: K :: nil) = 3 /\ rk (D :: I :: M :: nil) = 3 /\ 
rk (D :: J :: L :: nil) = 3 /\ rk (D :: J :: M :: nil) = 3 /\
rk (D :: K :: L :: nil) = 3 /\ rk (D :: K :: M :: nil) = 3 /\ 
rk (D :: L :: M :: nil) = 3 /\
rk (E :: F :: H :: nil) = 3 /\ rk (E :: F :: I :: nil) = 3 /\ rk (E :: F :: J :: nil) = 3 /\
rk (E :: F :: K :: nil) = 3 /\ rk (E :: F :: L :: nil) = 3 /\ rk (E :: F :: M :: nil) = 3 /\
rk (E :: G :: H :: nil) = 3 /\ rk (E :: G :: I :: nil) = 3 /\ rk (E :: G :: J :: nil) = 3 /\
rk (E :: G :: K :: nil) = 3 /\ rk (E :: G :: L :: nil) = 3 /\ rk (E :: G :: M :: nil) = 3 /\
rk (E :: H :: J :: nil) = 3 /\ rk (E :: H :: K :: nil) = 3 /\ rk (E :: H :: L :: nil) = 3 /\
rk (E :: H :: M :: nil) = 3 /\ 
rk (E :: I :: J :: nil) = 3 /\ rk (E :: I :: K :: nil) = 3 /\ rk (E :: I :: L :: nil) = 3 /\
rk (E :: I :: M :: nil) = 3 /\ 
rk (E :: J :: L :: nil) = 3 /\ rk (E :: J :: M :: nil) = 3 /\ 
rk (E :: K :: L :: nil) = 3 /\ rk (E :: K :: M :: nil) = 3 /\
rk (F :: G :: H :: nil) = 3 /\ rk (F :: G :: I :: nil) = 3 /\ rk (F :: G :: J :: nil) = 3 /\
rk (F :: G :: K :: nil) = 3 /\ rk (F :: G :: L :: nil) = 3 /\ rk (F :: G :: M :: nil) = 3 /\
rk (F :: H :: I :: nil) = 3 /\ rk (F :: H :: K :: nil) = 3 /\ rk (F :: H :: L :: nil) = 3 /\
rk (F :: H :: M :: nil) = 3 /\
rk (F :: I :: J :: nil) = 3 /\ rk (F :: I :: K :: nil) = 3 /\ rk (F :: I :: M :: nil) = 3 /\
rk (F :: J :: K :: nil) = 3 /\ rk (F :: J :: L :: nil) = 3 /\ rk (F :: J :: M :: nil) = 3 /\
rk (F :: K :: L :: nil) = 3 /\
rk (F :: L :: M :: nil) = 3 /\
rk (G :: H :: I :: nil) = 3 /\ rk (G :: H :: J :: nil) = 3 /\ rk (G :: H :: K :: nil) = 3 /\
rk (G :: H :: L :: nil) = 3 /\
rk (G :: I :: J :: nil) = 3 /\ rk (G :: I :: L :: nil) = 3 /\ rk (G :: I :: M :: nil) = 3 /\
rk (G :: J :: K :: nil) = 3 /\ rk (G :: J :: M :: nil) = 3 /\
rk (G :: K :: L :: nil) = 3 /\ rk (G :: K :: M :: nil) = 3 /\
rk (G :: L :: M :: nil) = 3 /\
rk (H :: I :: J :: nil) = 3 /\ rk (H :: I :: K :: nil) = 3 /\ rk (H :: I :: L :: nil) = 3 /\
rk (H :: I :: M :: nil) = 3 /\
rk (H :: J :: K :: nil) = 3 /\ rk (H :: J :: L :: nil) = 3 /\ rk (H :: J :: M :: nil) = 3 /\
rk (H :: K :: M :: nil) = 3 /\
rk (H :: L :: M :: nil) = 3 /\
rk (I :: J :: K :: nil) = 3 /\ rk (I :: J :: L :: nil) = 3 /\
rk (I :: K :: L :: nil) = 3 /\ rk (I :: K :: M :: nil) = 3 /\
rk (I :: L :: M :: nil) = 3 /\
rk (J :: K :: L :: nil) = 3 /\ rk (J :: K :: M :: nil) = 3 /\
rk (J :: L :: M :: nil) = 3 /\
rk (K :: L :: M :: nil) = 3.
Proof.
generalize (M.rk_planes).
unfold A, B,C, D, E, F, G, H, I, J, K, L, M.
intros.
my_split.
repeat split;solve[rk_triple_bis_bis].
Qed.

End swapfr3.

(*****************************************************************************)


Module Desargues_from_A (M:fano_plane_rank).

Import M.

Ltac new_case P := 
match (type of P) with 
| Point => generalize (is_only_13_pts P) ; let Q := fresh in (intros Q; decompose [sumor sumbool] Q; clear Q)
end.

Ltac case_eq_s O := new_case O.

Ltac case_clear_1 P := case_eq_s P.

(*** Autres lemmes matroid ***)

Lemma rk_distinct : 
rk(A :: B :: nil) = 2 /\ rk(A :: C :: nil) = 2 /\ rk(A :: D :: nil) = 2 /\ rk(A :: E :: nil) = 2 /\ rk(A :: F :: nil) = 2 /\ rk(A :: G :: nil) = 2 /\
rk(A :: H :: nil) = 2 /\ rk(A :: I :: nil) = 2 /\ rk(A :: J :: nil) = 2 /\ rk(A :: K :: nil) = 2 /\ rk(A :: L :: nil) = 2 /\ rk(A :: M :: nil) = 2 /\
rk(B :: C :: nil) = 2 /\ rk(B :: D :: nil) = 2 /\ rk(B :: E :: nil) = 2 /\ rk(B :: F :: nil) = 2 /\ rk(B :: G :: nil) = 2 /\
rk(B :: H :: nil) = 2 /\ rk(B :: I :: nil) = 2 /\ rk(B :: J :: nil) = 2 /\ rk(B :: K :: nil) = 2 /\ rk(B :: L :: nil) = 2 /\ rk(B :: M :: nil) = 2 /\
rk(C :: D :: nil) = 2 /\ rk(C :: E :: nil) = 2 /\ rk(C :: F :: nil) = 2 /\ rk(C :: G :: nil) = 2 /\
rk(C :: H :: nil) = 2 /\ rk(C :: I :: nil) = 2 /\ rk(C :: J :: nil) = 2 /\ rk(C :: K :: nil) = 2 /\ rk(C :: L :: nil) = 2 /\ rk(C :: M :: nil) = 2 /\
rk(D :: E :: nil) = 2 /\ rk(D :: F :: nil) = 2 /\ rk(D :: G :: nil) = 2 /\
rk(D :: H :: nil) = 2 /\ rk(D :: I :: nil) = 2 /\ rk(D :: J :: nil) = 2 /\ rk(D :: K :: nil) = 2 /\ rk(D :: L :: nil) = 2 /\ rk(D :: M :: nil) = 2 /\
rk(E :: F :: nil) = 2 /\ rk(E :: G :: nil) = 2 /\
rk(E :: H :: nil) = 2 /\ rk(E :: I :: nil) = 2 /\ rk(E :: J :: nil) = 2 /\ rk(E :: K :: nil) = 2 /\ rk(E :: L :: nil) = 2 /\ rk(E :: M :: nil) = 2 /\
rk(F :: G :: nil) = 2 /\
rk(F :: H :: nil) = 2 /\ rk(F :: I :: nil) = 2 /\ rk(F :: J :: nil) = 2 /\ rk(F :: K :: nil) = 2 /\ rk(F :: L :: nil) = 2 /\ rk(F :: M :: nil) = 2 /\
rk(G :: H :: nil) = 2 /\ rk(G :: I :: nil) = 2 /\ rk(G :: J :: nil) = 2 /\ rk(G :: K :: nil) = 2 /\ rk(G :: L :: nil) = 2 /\ rk(G :: M :: nil) = 2 /\
rk(H :: I :: nil) = 2 /\ rk(H :: J :: nil) = 2 /\ rk(H :: K :: nil) = 2 /\ rk(H :: L :: nil) = 2 /\ rk(H :: M :: nil) = 2 /\
rk(I :: J :: nil) = 2 /\ rk(I :: K :: nil) = 2 /\ rk(I :: L :: nil) = 2 /\ rk(I :: M :: nil) = 2 /\
rk(J :: K :: nil) = 2 /\ rk(J :: L :: nil) = 2 /\ rk(J :: M :: nil) = 2 /\
rk(K :: L :: nil) = 2 /\ rk(K :: M :: nil) = 2 /\
rk(L :: M :: nil) = 2 ->
~A = B /\ ~A = C /\ ~A = D /\ ~A = E /\ ~A = F /\ ~A = G /\ ~A = H /\ ~A = I /\ ~A = J /\ ~A = K /\ ~A = L /\ ~A = M /\
~B = C /\ ~B = D /\ ~B = E /\ ~B = F /\ ~B = G /\ ~B = H /\ ~B = I /\ ~B = J /\ ~B = K /\ ~B = L /\ ~B = M /\
~C = D /\ ~C = E /\ ~C = F /\ ~C = G /\ ~C = H /\ ~C = I /\ ~C = J /\ ~C = K /\ ~C = L /\ ~C = M /\
~D = E /\ ~D = F /\ ~D = G /\ ~D = H /\ ~D = I /\ ~D = J /\ ~D = K /\ ~D = L /\ ~D = M /\
~E = F /\ ~E = G /\ ~E = H /\ ~E = I /\ ~E = J /\ ~E = K /\ ~E = L /\ ~E = M /\
~F = G /\ ~F = H /\ ~F = I /\ ~F = J /\ ~F = K /\ ~F = L /\ ~F = M /\
~G = H /\ ~G = I /\ ~G = J /\ ~G = K /\ ~G = L /\ ~G = M /\
~H = I /\ ~H = J /\ ~H = K /\ ~H = L /\ ~H = M /\
~I = J /\ ~I = K /\ ~I = L /\ ~I = M /\
~J = K /\ ~J = L /\ ~J = M /\
~K = L /\ ~K = M /\
~L = M.
Proof.
intros.
my_split;repeat split;apply couple_rk1;assumption.
Qed.

Lemma quadruple_rk2rk3 : forall P Q R S : Point,
~ P = Q -> ~ P = R -> ~ P = S -> ~ Q = R -> ~ Q = S -> ~ R = S -> 
rk(P :: Q :: R :: S :: nil) = 2 \/ rk(P :: Q :: R :: S :: nil) = 3.
Proof.
intros.
assert(HH0 := rk_couple_ge P Q H0).
assert(HH1 := rk_quadruple_max_3 P Q R S).
apply le_lt_or_eq in HH1.
destruct HH1.
assert(HH2 : incl (P :: Q :: nil) (P :: Q :: R :: S :: nil));[my_inA|].
assert(HH3 := matroid2 (P :: Q :: nil) (P :: Q :: R :: S :: nil) HH2).
omega.
omega.
Qed.

Lemma quadruple_rk2_to_triple_rk2 : forall P Q R S : Point,
~ P = Q -> rk(P :: Q :: R :: S :: nil) = 2 -> rk(P :: Q :: R :: nil) = 2.
Proof.
intros.
assert(HH0 := rk_couple_ge P Q H0).
assert(HH2 : incl (P :: Q :: nil) (P :: Q :: R :: nil));[my_inA|].
assert(HH3 := matroid2 (P :: Q :: nil) (P :: Q :: R :: nil) HH2).
assert(HH4 : incl (P :: Q :: R :: nil) (P :: Q :: R :: S :: nil));[my_inA|].
assert(HH5 := matroid2 (P :: Q :: R :: nil) (P :: Q :: R :: S :: nil) HH4).
omega.
Qed.

Lemma quadruple_distinct_rk3 : forall P Q R S T : Point, 
~ P = Q -> ~ P = R -> ~ P = S -> ~ P = T ->
~ Q = R -> ~ Q = S -> ~ Q = T -> ~ R = S ->
~ R = T -> ~ S = T ->
rk(P :: Q :: R :: S :: nil) = 2 ->
rk(P :: Q :: R :: T :: nil) = 3.
Proof.
intros.
assert(HH0 := quadruple_rk2_to_triple_rk2 P Q R S H0 H10).
generalize rk_planes;intro HH;use HH.
time(case_clear_1 P;subst;
case_clear_1 Q;subst;
try equal_degens;
case_clear_1 R;subst;
try equal_degens;
try solve[rk_triple_2_3_bis_bis];
case_clear_1 S;subst;
try equal_degens;
try solve[rk_quadruple_2_3_bis_bis];
case_clear_1 T;subst;
try equal_degens;
try solve[rk_quadruple_to_triple_bis_bis]).
Qed.

Lemma quintuple_distinct_rk3 : forall P Q R S T : Point, 
~ P = Q -> ~ P = R -> ~ P = S -> ~ P = T -> 
~ Q = R -> ~ Q = S -> ~ Q = T -> ~ R = S -> 
~ R = T -> ~S = T -> rk(P :: Q :: R :: S :: T :: nil) = 3.
Proof.
intros.
assert(HH0 := quadruple_rk2rk3 P Q R S H0 H1 H2 H4 H5 H7).
destruct HH0.
assert(HH1 := quadruple_distinct_rk3 P Q R S T H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10).
assert(HH2 := rk_quintuple_max_3 P Q R S T).
assert(HH3 : incl (P :: Q :: R :: T :: nil) (P :: Q :: R :: S :: T :: nil));[my_inA|].
assert(HH4 := matroid2 (P :: Q :: R :: T :: nil) (P :: Q :: R :: S :: T :: nil) HH3).
omega.
assert(HH0 := rk_quintuple_max_3 P Q R S T).
assert(HH1 : incl (P :: Q :: R :: S :: nil) (P :: Q :: R :: S :: T :: nil));[my_inA|].
assert(HH2 := matroid2 (P :: Q :: R :: S :: nil) (P :: Q :: R :: S :: T :: nil) HH1).
omega.
Qed.

Lemma not_all_rk_equal : forall P Q R : Point, ~(rk(P :: P :: nil) = 2  \/ rk(Q :: Q :: nil) = 2 \/ rk(R :: R :: nil) = 2).
Proof.
intros P Q R H0; intuition.
assert(HH := couple_rk1 P P H1);my_inA.
assert(HH := couple_rk1 Q Q H0);my_inA.
assert(HH := couple_rk1 R R H0);my_inA.
Qed.

(*
Lemma not_at_least_two_rk_equal_from_P : forall P Q R P' : Point, 
~(rk(P :: P' :: nil) = 2 /\ rk(Q :: Q :: nil) = 2 \/ 
rk(P :: P' :: nil) = 2 /\ rk(R :: R :: nil) = 2 \/ 
rk(Q :: Q :: nil) = 2 /\ rk(R :: R :: nil) = 2).
Proof.
intros P Q R R' H0; intuition.
assert(HH := couple_rk1 Q Q H2);my_inA.
assert(HH := couple_rk1 R R H2);my_inA.
assert(HH := couple_rk1 Q Q H1);my_inA.
Qed.

Lemma not_at_least_two_rk_equal_from_Q : forall P Q R Q' : Point, 
~(rk(P :: P :: nil) = 2 /\ rk(Q :: Q' :: nil) = 2 \/ 
rk(P :: P :: nil) = 2 /\ rk(R :: R :: nil) = 2 \/ 
rk(Q :: Q' :: nil) = 2 /\ rk(R :: R :: nil) = 2).
Proof.
intros P Q R R' H0; intuition.
assert(HH := couple_rk1 P P H0);my_inA.
assert(HH := couple_rk1 R R H2);my_inA.
assert(HH := couple_rk1 R R H2);my_inA.
Qed.

Lemma not_at_least_two_rk_equal_from_R : forall P Q R R' : Point, 
~(rk(P :: P :: nil) = 2 /\ rk(Q :: Q :: nil) = 2 \/ 
rk(P :: P :: nil) = 2 /\ rk(R :: R' :: nil) = 2 \/ 
rk(Q :: Q :: nil) = 2 /\ rk(R :: R' :: nil) = 2).
Proof.
intros P Q R R' H0; intuition.
assert(HH := couple_rk1 P P H0);my_inA.
assert(HH := couple_rk1 P P H1);my_inA.
assert(HH := couple_rk1 Q Q H1);my_inA.
Qed.
*)

Ltac degens_rk2 := 
try solve[apply triple_rk2_1;assumption];
try solve[apply triple_rk2_2;assumption];
try solve[apply triple_rk2_3;assumption].

Ltac degens_rk3 := 
match goal with
| H: rk(?P :: ?P :: nil) = 2  \/ rk(?Q :: ?Q :: nil) = 2 \/ rk(?R :: ?R :: nil) = 2 |- _ => elim (not_all_rk_equal P Q R H)
| H: rk(?P :: ?P :: ?R :: nil) = 3 |- _ => elim (col_degen_1 P R H)
| H: rk(?P :: ?R :: ?P :: nil) = 3 |- _ => elim (col_degen_2 P R H)
| H: rk(?R :: ?P :: ?P :: nil) = 3 |- _ => elim (col_degen_3 P R H)
end.

(*
Ltac degens_rk3_alt := 
match goal with
| H: rk(?P :: ?P' :: nil) = 2 /\ rk(?Q :: ?Q :: nil) = 2 \/ rk(?P :: ?P' :: nil) = 2 /\ rk(?R :: ?R :: nil) = 2 \/ rk(?Q :: ?Q :: nil) = 2 /\ rk(?R :: ?R :: nil) = 2 |- _ => elim (not_at_least_two_rk_equal_from_P P Q R P' H)
| H: rk(?P :: ?P :: nil) = 2 /\ rk(?Q :: ?Q' :: nil) = 2 \/ rk(?P :: ?P :: nil) = 2 /\ rk(?R :: ?R :: nil) = 2 \/ rk(?Q :: ?Q' :: nil) = 2 /\ rk(?R :: ?R :: nil) = 2 |- _ => elim (not_at_least_two_rk_equal_from_Q P Q R Q' H)
| H: rk(?P :: ?P :: nil) = 2 /\ rk(?Q :: ?Q :: nil) = 2 \/ rk(?P :: ?P :: nil) = 2 /\ rk(?R :: ?R' :: nil) = 2 \/ rk(?Q :: ?Q :: nil) = 2 /\ rk(?R :: ?R' :: nil) = 2 |- _ => elim (not_at_least_two_rk_equal_from_R P Q R R' H)
| H: rk(?P :: ?P :: ?R :: nil) = 3 |- _ => elim (col_degen_1 P R H)
| H: rk(?P :: ?R :: ?P :: nil) = 3 |- _ => elim (col_degen_2 P R H)
| H: rk(?R :: ?P :: ?P :: nil) = 3 |- _ => elim (col_degen_3 P R H)
end.
*)

Ltac rk_quintuple_simplification P:=
repeat match goal with
| H : rk(P :: ?X :: ?Y :: ?Z :: ?W :: nil) = 2 |- _ => let HH := fresh in assert(HH : rk (P :: X :: Y :: Z :: W :: nil) = 3) by (apply (quintuple_distinct_rk3 P X Y Z W);assumption);
rewrite HH in H;inversion H
end.

Ltac case_clear_2 P :=
  case_clear_1 P;
  match goal with
| H : P = ?X |- _ => subst;try solve [degens_rk3];try solve[rk_quintuple_simplification X]
end.

Ltac clear_rk2 :=
repeat match goal with
| H : rk _ = 2 |- _ => clear H
end.

Ltac clear_rk3 :=
repeat match goal with
| H : rk _ = 3 |- _ => clear H
end.

Ltac clear_rk :=
  match goal with
| H : rk _ = _ |- _ => clear H
end.

Ltac clear_neq :=
   match goal with
| H : _ <> _ |- _ => clear H
end.

Ltac case_clear_P1 P Q R :=
case_clear_2 P;
case_clear_2 Q;
case_clear_2 R;
try solve[rk_quadruple_2_3_bis_bis].

Ltac case_clear_P2 P Q R :=
case_clear_2 P;
case_clear_2 Q;
case_clear_2 R;
try solve[rk_quadruple_2_3_bis_bis].

Ltac case_clear_P3 P Q R := 
case_clear_1 P;subst;try solve[rk_triple_2_3_bis_bis];
case_clear_1 Q;subst;try solve[rk_triple_2_3_bis_bis];
case_clear_1 R;subst;try solve[rk_triple_2_3_bis_bis];
degens_rk2;try rk_triple_to_quadruple_bis_bis.

Ltac case_clear_P2_P3 P Q R P' Q' R' :=
case_clear_P2 P Q R;
case_clear_P3 P' Q' R'.

Lemma Desargues_from_A_spec_1 :  forall P Q R P' Q' R' alpha beta gamma,
rk(P :: Q :: gamma :: nil) = 2 -> rk(P' :: Q' :: gamma :: nil) = 2 ->
rk(P :: R :: beta :: nil) = 2 -> rk(P' :: R' :: beta :: nil) = 2 ->
rk(Q :: R :: alpha :: nil) = 2 -> rk(Q' :: R' :: alpha :: nil) = 2 ->
rk(A :: P :: P' :: nil) = 2 -> rk(A :: Q :: Q' :: nil) = 2 -> rk(A :: R :: R' :: nil) = 2 ->
rk(P :: A :: B :: C :: D :: nil) = 2 -> rk(P':: A :: B :: C :: D :: nil) = 2 ->
rk(Q :: A :: E :: F :: G :: nil) = 2 -> rk(Q' :: A :: E :: F :: G :: nil) = 2 ->
rk(R :: A :: I :: J :: M :: nil) = 2 -> rk(R' :: A :: I :: J :: M :: nil) = 2 ->
rk(A :: P :: Q :: nil) = 3 -> rk(A :: P :: R :: nil) = 3 -> rk(A :: Q :: R :: nil) = 3 ->
rk(P :: Q :: R :: nil) = 3 -> rk(P' :: Q' :: R' :: nil) = 3 -> 
(rk(P :: P' :: nil) = 2 \/ rk(Q :: Q' :: nil) = 2 \/ rk(R :: R' :: nil) = 2) ->
rk(alpha :: beta :: gamma :: nil) = 2.
Proof.
intros P Q R P' Q' R' alpha beta gamma;intros.
assert(HH0 := rk_distinct_points).
assert(HH := rk_distinct HH0);clear HH0;my_split;eq_duplicate;my_split.
generalize rk_lines;intro HH;use HH.
generalize rk_planes;intro HH;use HH.
case_clear_P1 P Q R.
idtac "1".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "2".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "3".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "4".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "5".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "6".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "7".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "8".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "9".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "10".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "11".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "12".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "13".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "14".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "15".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "16".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "17".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "18".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
Qed exporting.

Lemma Desargues_from_A_spec_2 :  forall P Q R P' Q' R' alpha beta gamma,
rk(P :: Q :: gamma :: nil) = 2 -> rk(P' :: Q' :: gamma :: nil) = 2 ->
rk(P :: R :: beta :: nil) = 2 -> rk(P' :: R' :: beta :: nil) = 2 ->
rk(Q :: R :: alpha :: nil) = 2 -> rk(Q' :: R' :: alpha :: nil) = 2 ->
rk(A :: P :: P' :: nil) = 2 -> rk(A :: Q :: Q' :: nil) = 2 -> rk(A :: R :: R' :: nil) = 2 ->
rk(P :: A :: B :: C :: D :: nil) = 2 -> rk(P':: A :: B :: C :: D :: nil) = 2 ->
rk(Q :: A :: E :: F :: G :: nil) = 2 -> rk(Q' :: A :: E :: F :: G :: nil) = 2 ->
rk(R :: A :: H :: K :: L :: nil) = 2 -> rk(R' :: A :: H :: K :: L :: nil) = 2 ->
rk(A :: P :: Q :: nil) = 3 -> rk(A :: P :: R :: nil) = 3 -> rk(A :: Q :: R :: nil) = 3 ->
rk(P :: Q :: R :: nil) = 3 -> rk(P' :: Q' :: R' :: nil) = 3 -> 
(rk(P :: P' :: nil) = 2 \/ rk(Q :: Q' :: nil) = 2 \/ rk(R :: R' :: nil) = 2) ->
rk(alpha :: beta :: gamma :: nil) = 2.
Proof.
intros P Q R P' Q' R' alpha beta gamma;intros.
assert(HH0 := rk_distinct_points).
assert(HH := rk_distinct HH0);clear HH0;my_split;eq_duplicate;my_split.
generalize rk_lines;intro HH;use HH.
generalize rk_planes;intro HH;use HH.
case_clear_P1 P Q R.
idtac "1".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "2".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "3".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "4".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "5".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "6".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "7".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "8".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "9".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "10".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "11".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "12".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "13".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "14".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "15".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "16".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "17".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "18".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
Qed exporting.

Lemma Desargues_from_A_spec_3 :  forall P Q R P' Q' R' alpha beta gamma,
rk(P :: Q :: gamma :: nil) = 2 -> rk(P' :: Q' :: gamma :: nil) = 2 ->
rk(P :: R :: beta :: nil) = 2 -> rk(P' :: R' :: beta :: nil) = 2 ->
rk(Q :: R :: alpha :: nil) = 2 -> rk(Q' :: R' :: alpha :: nil) = 2 ->
rk(A :: P :: P' :: nil) = 2 -> rk(A :: Q :: Q' :: nil) = 2 -> rk(A :: R :: R' :: nil) = 2 ->
rk(P :: A :: B :: C :: D :: nil) = 2 -> rk(P':: A :: B :: C :: D :: nil) = 2 ->
rk(Q :: A :: I :: J :: M :: nil) = 2 -> rk(Q' :: A :: I :: J :: M :: nil) = 2 ->
rk(R :: A :: H :: K :: L :: nil) = 2 -> rk(R' :: A :: H :: K :: L :: nil) = 2 ->
rk(A :: P :: Q :: nil) = 3 -> rk(A :: P :: R :: nil) = 3 -> rk(A :: Q :: R :: nil) = 3 ->
rk(P :: Q :: R :: nil) = 3 -> rk(P' :: Q' :: R' :: nil) = 3 -> 
(rk(P :: P' :: nil) = 2 \/ rk(Q :: Q' :: nil) = 2 \/ rk(R :: R' :: nil) = 2) ->
rk(alpha :: beta :: gamma :: nil) = 2.
Proof.
intros P Q R P' Q' R' alpha beta gamma;intros.
assert(HH0 := rk_distinct_points).
assert(HH := rk_distinct HH0);clear HH0;my_split;eq_duplicate;my_split.
generalize rk_lines;intro HH;use HH.
generalize rk_planes;intro HH;use HH.
case_clear_P1 P Q R.
idtac "1".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "2".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "3".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "4".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "5".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "6".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "7".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "8".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "9".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "10".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "11".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "12".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "13".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "14".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "15".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "16".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "17".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "18".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
Qed exporting.

Lemma Desargues_from_A_spec_4 :  forall P Q R P' Q' R' alpha beta gamma,
rk(P :: Q :: gamma :: nil) = 2 -> rk(P' :: Q' :: gamma :: nil) = 2 ->
rk(P :: R :: beta :: nil) = 2 -> rk(P' :: R' :: beta :: nil) = 2 ->
rk(Q :: R :: alpha :: nil) = 2 -> rk(Q' :: R' :: alpha :: nil) = 2 ->
rk(A :: P :: P' :: nil) = 2 -> rk(A :: Q :: Q' :: nil) = 2 -> rk(A :: R :: R' :: nil) = 2 ->
rk(P :: A :: E :: F :: G :: nil) = 2 -> rk(P':: A :: E :: F :: G :: nil) = 2 ->
rk(Q :: A :: I :: J :: M :: nil) = 2 -> rk(Q' :: A :: I :: J :: M :: nil) = 2 ->
rk(R :: A :: H :: K :: L :: nil) = 2 -> rk(R' :: A :: H :: K :: L :: nil) = 2 ->
rk(A :: P :: Q :: nil) = 3 -> rk(A :: P :: R :: nil) = 3 -> rk(A :: Q :: R :: nil) = 3 ->
rk(P :: Q :: R :: nil) = 3 -> rk(P' :: Q' :: R' :: nil) = 3 -> 
(rk(P :: P' :: nil) = 2 \/ rk(Q :: Q' :: nil) = 2 \/ rk(R :: R' :: nil) = 2) ->
rk(alpha :: beta :: gamma :: nil) = 2.
Proof.
intros P Q R P' Q' R' alpha beta gamma;intros.
assert(HH0 := rk_distinct_points).
assert(HH := rk_distinct HH0);clear HH0;my_split;eq_duplicate;my_split.
generalize rk_lines;intro HH;use HH.
generalize rk_planes;intro HH;use HH.
case_clear_P1 P Q R.
idtac "1".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "2".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "3".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "4".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "5".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "6".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "7".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "8".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "9".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "10".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "11".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "12".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "13".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "14".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "15".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "16".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "17".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
idtac "18".
time(abstract (case_clear_P2_P3 P' Q' R' alpha beta gamma)).
Qed exporting.

Ltac case_clear_4 P := case_clear_1 P;subst;try solve[equal_degens];try solve[rk_quadruple_2_3_bis_bis].

Lemma degens_or : forall P P' Q Q' R R', 
rk(P :: P' :: nil) = 2 \/ rk(Q :: Q' :: nil) = 2 \/ rk(R :: R' :: nil) = 2 ->
(rk(P :: P' :: nil) = 2 \/ rk(R :: R' :: nil) = 2 \/ rk(Q :: Q' :: nil) = 2) /\
(rk(Q :: Q' :: nil) = 2 \/ rk(P :: P' :: nil) = 2 \/ rk(R :: R' :: nil) = 2) /\
(rk(Q :: Q' :: nil) = 2 \/ rk(R :: R' :: nil) = 2 \/ rk(P :: P' :: nil) = 2) /\
(rk(R :: R' :: nil) = 2 \/ rk(P :: P' :: nil) = 2 \/ rk(Q :: Q' :: nil) = 2) /\
(rk(R :: R' :: nil) = 2 \/ rk(Q :: Q' :: nil) = 2 \/ rk(P :: P' :: nil) = 2).
Proof.
intros;intuition.
Qed.

Ltac rk_quintuple_fixe P A B C D :=
match goal with
| H0 : rk(P :: A :: B :: C :: D :: nil) = 2 |- _ => assumption
| H0 : rk(P :: A :: B :: D :: C :: nil) = 2 |- _ => rewrite <-quintuple_permut_1 in H0;assumption
| H0 : rk(P :: A :: C :: B :: D :: nil) = 2 |- _ => rewrite <-quintuple_permut_2 in H0;assumption
| H0 : rk(P :: A :: C :: D :: B :: nil) = 2 |- _ => rewrite <-quintuple_permut_3 in H0;assumption
| H0 : rk(P :: A :: D :: B :: C :: nil) = 2 |- _ => rewrite <-quintuple_permut_4 in H0;assumption
| H0 : rk(P :: A :: D :: C :: B :: nil) = 2 |- _ => rewrite <-quintuple_permut_5 in H0;assumption
end.

Ltac rk_quintuple_fixe_bis :=
match goal with
| H : _ |- rk(?P :: ?A :: ?B :: ?C :: ?D :: nil) = 2 => solve [rk_quintuple_fixe P A B C D]
end.

Ltac solve_desargues_from_A_spec P Q R P' Q' R' alpha beta gamma HH HH0 HH1 HH2 HH3 HH4:=
match goal with
| Hyp : rk(P :: A :: B :: _ :: _ :: nil) = 2 |- _ => match goal with
      | Hyp : rk(Q :: A :: E :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[apply Desargues_from_A_spec_1 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_1 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_1 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[apply Desargues_from_A_spec_2 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_2 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_2 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: F :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[apply Desargues_from_A_spec_1 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_1 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_1 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[apply Desargues_from_A_spec_2 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_2 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_2 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: G :: _ :: _ :: nil) = 2 |- _ => match goal with
             | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[apply Desargues_from_A_spec_1 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_1 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_1 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[apply Desargues_from_A_spec_2 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_2 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_2 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: I :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH;apply Desargues_from_A_spec_1 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_1 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_1 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[apply Desargues_from_A_spec_3 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_3 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_3 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: J :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH;apply Desargues_from_A_spec_1 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_1 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_1 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[apply Desargues_from_A_spec_3 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_3 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_3 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: M :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH;apply Desargues_from_A_spec_1 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_1 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_1 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[apply Desargues_from_A_spec_3 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_3 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_3 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: H :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH;apply Desargues_from_A_spec_2 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_2 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_2 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH;apply Desargues_from_A_spec_3 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_3 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_3 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: K :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH;apply Desargues_from_A_spec_2 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_2 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_2 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH;apply Desargues_from_A_spec_3 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_3 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_3 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: L :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH;apply Desargues_from_A_spec_2 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_2 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_2 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH;apply Desargues_from_A_spec_3 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_3 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_3 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
      end
| Hyp : rk(P :: A :: C :: _ :: _ :: nil) = 2 |- _ => match goal with
      | Hyp : rk(Q :: A :: E :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[apply Desargues_from_A_spec_1 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_1 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_1 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[apply Desargues_from_A_spec_2 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_2 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_2 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: F :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[apply Desargues_from_A_spec_1 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_1 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_1 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[apply Desargues_from_A_spec_2 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_2 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_2 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: G :: _ :: _ :: nil) = 2 |- _ => match goal with
             | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[apply Desargues_from_A_spec_1 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_1 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_1 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[apply Desargues_from_A_spec_2 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_2 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_2 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: I :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH;apply Desargues_from_A_spec_1 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_1 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_1 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[apply Desargues_from_A_spec_3 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_3 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_3 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: J :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH;apply Desargues_from_A_spec_1 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_1 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_1 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[apply Desargues_from_A_spec_3 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_3 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_3 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: M :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH;apply Desargues_from_A_spec_1 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_1 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_1 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[apply Desargues_from_A_spec_3 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_3 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_3 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: H :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH;apply Desargues_from_A_spec_2 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_2 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_2 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH;apply Desargues_from_A_spec_3 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_3 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_3 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: K :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH;apply Desargues_from_A_spec_2 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_2 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_2 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH;apply Desargues_from_A_spec_3 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_3 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_3 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: L :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH;apply Desargues_from_A_spec_2 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_2 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_2 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH;apply Desargues_from_A_spec_3 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_3 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_3 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
      end
| Hyp : rk(P :: A :: D :: _ :: _ :: nil) = 2 |- _ => match goal with
      | Hyp : rk(Q :: A :: E :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[apply Desargues_from_A_spec_1 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_1 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_1 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[apply Desargues_from_A_spec_2 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_2 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_2 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: F :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[apply Desargues_from_A_spec_1 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_1 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_1 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[apply Desargues_from_A_spec_2 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_2 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_2 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: G :: _ :: _ :: nil) = 2 |- _ => match goal with
             | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[apply Desargues_from_A_spec_1 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_1 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_1 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[apply Desargues_from_A_spec_2 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_2 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_2 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: I :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH;apply Desargues_from_A_spec_1 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_1 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_1 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[apply Desargues_from_A_spec_3 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_3 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_3 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: J :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH;apply Desargues_from_A_spec_1 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_1 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_1 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[apply Desargues_from_A_spec_3 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_3 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_3 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: M :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH;apply Desargues_from_A_spec_1 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_1 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_1 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[apply Desargues_from_A_spec_3 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_3 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_3 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: H :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH;apply Desargues_from_A_spec_2 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_2 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_2 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH;apply Desargues_from_A_spec_3 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_3 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_3 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: K :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH;apply Desargues_from_A_spec_2 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_2 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_2 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH;apply Desargues_from_A_spec_3 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_3 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_3 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: L :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH;apply Desargues_from_A_spec_2 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_2 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_2 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH;apply Desargues_from_A_spec_3 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_3 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_3 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
      end
| Hyp : rk(P :: A :: E :: _ :: _ :: nil) = 2 |- _ => match goal with
       | Hyp : rk(Q :: A :: B :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH0;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH0;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: C :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH0;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH0;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: D :: _ :: _ :: nil) = 2 |- _ => match goal with
             | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH0;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH0;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: I :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH2;apply Desargues_from_A_spec_1 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_1 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_1 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[apply Desargues_from_A_spec_4 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_4 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_4 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: J :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH2;apply Desargues_from_A_spec_1 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_1 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_1 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[apply Desargues_from_A_spec_4 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_4 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_4 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: M :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH2;apply Desargues_from_A_spec_1 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_1 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_1 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[apply Desargues_from_A_spec_4 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_4 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_4 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: H :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH2;apply Desargues_from_A_spec_2 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_2 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_2 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH;apply Desargues_from_A_spec_4 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_4 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_4 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: K :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH2;apply Desargues_from_A_spec_2 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_2 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_2 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH;apply Desargues_from_A_spec_4 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_4 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_4 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: L :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH2;apply Desargues_from_A_spec_2 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_2 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_2 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH;apply Desargues_from_A_spec_4 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_4 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_4 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
      end
| Hyp : rk(P :: A :: F :: _ :: _ :: nil) = 2 |- _ => match goal with
       | Hyp : rk(Q :: A :: B :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH0;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH0;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: C :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH0;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH0;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: D :: _ :: _ :: nil) = 2 |- _ => match goal with
             | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH0;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH0;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: I :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH2;apply Desargues_from_A_spec_1 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_1 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_1 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[apply Desargues_from_A_spec_4 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_4 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_4 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: J :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH2;apply Desargues_from_A_spec_1 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_1 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_1 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[apply Desargues_from_A_spec_4 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_4 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_4 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: M :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH2;apply Desargues_from_A_spec_1 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_1 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_1 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[apply Desargues_from_A_spec_4 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_4 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_4 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: H :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH2;apply Desargues_from_A_spec_2 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_2 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_2 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH;apply Desargues_from_A_spec_4 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_4 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_4 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: K :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH2;apply Desargues_from_A_spec_2 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_2 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_2 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH;apply Desargues_from_A_spec_4 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_4 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_4 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: L :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH2;apply Desargues_from_A_spec_2 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_2 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_2 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH;apply Desargues_from_A_spec_4 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_4 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_4 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
      end
| Hyp : rk(P :: A :: G :: _ :: _ :: nil) = 2 |- _ => match goal with
       | Hyp : rk(Q :: A :: B :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH0;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH0;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: C :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH0;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH0;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: D :: _ :: _ :: nil) = 2 |- _ => match goal with
             | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH0;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH0;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: I :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH2;apply Desargues_from_A_spec_1 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_1 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_1 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[apply Desargues_from_A_spec_4 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_4 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_4 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: J :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH2;apply Desargues_from_A_spec_1 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_1 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_1 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[apply Desargues_from_A_spec_4 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_4 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_4 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: M :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH2;apply Desargues_from_A_spec_1 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_1 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_1 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[apply Desargues_from_A_spec_4 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_4 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[apply Desargues_from_A_spec_4 with (P:=P) (Q:=Q) (R:=R) (P':=P') (Q':=Q') (R':=R') (alpha:=alpha) (beta:=beta) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: H :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH2;apply Desargues_from_A_spec_2 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_2 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_2 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH;apply Desargues_from_A_spec_4 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_4 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_4 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: K :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH2;apply Desargues_from_A_spec_2 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_2 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_2 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH;apply Desargues_from_A_spec_4 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_4 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_4 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: L :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH2;apply Desargues_from_A_spec_2 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_2 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_2 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH;apply Desargues_from_A_spec_4 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_4 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH;apply Desargues_from_A_spec_4 with (P:=P) (Q:=R) (R:=Q) (P':=P') (Q':=R') (R':=Q') (alpha:=alpha) (beta:=gamma) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
      end
| Hyp : rk(P :: A :: I :: _ :: _ :: nil) = 2 |- _ => match goal with
       | Hyp : rk(Q :: A :: B :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH1;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH0;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: C :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH1;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH0;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: D :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH1;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH0;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: E :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH3;apply Desargues_from_A_spec_1 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_1 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_1 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH0;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: F :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH3;apply Desargues_from_A_spec_1 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_1 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_1 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH0;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: G :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH3;apply Desargues_from_A_spec_1 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_1 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_1 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH0;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: H :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH2;apply Desargues_from_A_spec_3 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_3 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_3 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH2;apply Desargues_from_A_spec_4 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_4 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_4 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: K :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH2;apply Desargues_from_A_spec_3 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_3 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_3 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH2;apply Desargues_from_A_spec_4 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_4 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_4 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: L :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH2;apply Desargues_from_A_spec_3 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_3 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_3 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH2;apply Desargues_from_A_spec_4 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_4 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_4 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
      end
| Hyp : rk(P :: A :: J :: _ :: _ :: nil) = 2 |- _ => match goal with
       | Hyp : rk(Q :: A :: B :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH1;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH0;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: C :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH1;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH0;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: D :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH1;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH0;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: E :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH3;apply Desargues_from_A_spec_1 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_1 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_1 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH0;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: F :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH3;apply Desargues_from_A_spec_1 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_1 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_1 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH0;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: G :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH3;apply Desargues_from_A_spec_1 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_1 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_1 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH0;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: H :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH2;apply Desargues_from_A_spec_3 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_3 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_3 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH2;apply Desargues_from_A_spec_4 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_4 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_4 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: K :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH2;apply Desargues_from_A_spec_3 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_3 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_3 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH2;apply Desargues_from_A_spec_4 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_4 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_4 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: L :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH2;apply Desargues_from_A_spec_3 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_3 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_3 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH2;apply Desargues_from_A_spec_4 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_4 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_4 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
      end
| Hyp : rk(P :: A :: M :: _ :: _ :: nil) = 2 |- _ => match goal with
       | Hyp : rk(Q :: A :: B :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH1;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH0;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: C :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH1;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH0;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: D :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH1;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_1 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH0;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: E :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH3;apply Desargues_from_A_spec_1 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_1 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_1 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH0;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: F :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH3;apply Desargues_from_A_spec_1 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_1 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_1 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH0;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: G :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH3;apply Desargues_from_A_spec_1 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_1 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_1 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: H :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH0;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: K :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: L :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH0;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=P) (R:=R) (P':=Q') (Q':=P') (R':=R') (alpha:=beta) (beta:=alpha) (gamma:=gamma);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: H :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH2;apply Desargues_from_A_spec_3 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_3 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_3 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH2;apply Desargues_from_A_spec_4 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_4 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_4 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: K :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH2;apply Desargues_from_A_spec_3 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_3 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_3 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH2;apply Desargues_from_A_spec_4 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_4 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_4 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: L :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH2;apply Desargues_from_A_spec_3 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_3 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_3 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH2;apply Desargues_from_A_spec_4 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_4 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH2;apply Desargues_from_A_spec_4 with (P:=R) (Q:=P) (R:=Q) (P':=R') (Q':=P') (R':=Q') (alpha:=gamma) (beta:=alpha) (gamma:=beta);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
      end
| Hyp : rk(P :: A :: H :: _ :: _ :: nil) = 2 |- _ => match goal with
       | Hyp : rk(Q :: A :: B :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH1;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH1;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: C :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH1;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH1;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: D :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH1;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH1;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: E :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH3;apply Desargues_from_A_spec_2 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_2 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_2 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH1;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: F :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH3;apply Desargues_from_A_spec_2 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_2 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_2 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH1;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: G :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH3;apply Desargues_from_A_spec_2 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_2 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_2 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH1;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: I :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH3;apply Desargues_from_A_spec_3 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_3 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_3 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH3;apply Desargues_from_A_spec_4 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_4 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_4 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: J :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH3;apply Desargues_from_A_spec_3 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_3 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_3 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH3;apply Desargues_from_A_spec_4 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_4 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_4 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: M :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH3;apply Desargues_from_A_spec_3 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_3 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_3 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH3;apply Desargues_from_A_spec_4 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_4 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_4 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
      end
| Hyp : rk(P :: A :: K :: _ :: _ :: nil) = 2 |- _ => match goal with
       | Hyp : rk(Q :: A :: B :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH1;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH1;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: C :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH1;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH1;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: D :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH1;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH1;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: E :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH3;apply Desargues_from_A_spec_2 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_2 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_2 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH1;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: F :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH3;apply Desargues_from_A_spec_2 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_2 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_2 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH1;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: G :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH3;apply Desargues_from_A_spec_2 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_2 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_2 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH1;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: I :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH3;apply Desargues_from_A_spec_3 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_3 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_3 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH3;apply Desargues_from_A_spec_4 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_4 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_4 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: J :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH3;apply Desargues_from_A_spec_3 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_3 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_3 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH3;apply Desargues_from_A_spec_4 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_4 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_4 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: M :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH3;apply Desargues_from_A_spec_3 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_3 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_3 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH3;apply Desargues_from_A_spec_4 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_4 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_4 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
      end
| Hyp : rk(P :: A :: L :: _ :: _ :: nil) = 2 |- _ => match goal with
       | Hyp : rk(Q :: A :: B :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH1;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH1;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: C :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH1;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH1;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: D :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH1;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_2 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH1;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_3 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: E :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH3;apply Desargues_from_A_spec_2 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_2 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_2 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH1;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: F :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH3;apply Desargues_from_A_spec_2 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_2 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_2 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH1;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: G :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH3;apply Desargues_from_A_spec_2 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_2 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_2 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: I :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH1;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: J :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: M :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH1;apply Desargues_from_A_spec_4 with (P:=Q) (Q:=R) (R:=P) (P':=Q') (Q':=R') (R':=P') (alpha:=beta) (beta:=gamma) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: I :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH3;apply Desargues_from_A_spec_3 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_3 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_3 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH3;apply Desargues_from_A_spec_4 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_4 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_4 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: J :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH3;apply Desargues_from_A_spec_3 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_3 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_3 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH3;apply Desargues_from_A_spec_4 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_4 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_4 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
       | Hyp : rk(Q :: A :: M :: _ :: _ :: nil) = 2 |- _ => match goal with
            | Hyp : rk(R :: A :: B :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH3;apply Desargues_from_A_spec_3 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: C :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_3 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: D :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_3 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: E :: _ :: _ :: nil) = 2 |- _ => try solve[rewrite HH3;apply Desargues_from_A_spec_4 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: F :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_4 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            | Hyp : rk(R :: A :: G :: _ :: _ :: nil) = 2 |- _  => try solve[rewrite HH3;apply Desargues_from_A_spec_4 with (P:=R) (Q:=Q) (R:=P) (P':=R') (Q':=Q') (R':=P') (alpha:=gamma) (beta:=beta) (gamma:=alpha);
                                                          try solve[assumption];try solve[rk_triple_bis_bis];try solve[rk_quintuple_fixe_bis]]
            end
      end
end.

Ltac case_clear_P4 P Q R :=
case_clear_4 P;
case_clear_4 Q;
case_clear_4 R.

Lemma Desargues_from_A :  forall X Y Z X' Y' Z' X'' Y'' Z'' P Q R P' Q' R' alpha beta gamma,
~ A = X /\ ~ A = Y /\ ~ A = Z /\ ~ X = Y /\ ~ X = Z /\ ~ Y = Z /\
~ A = X' /\ ~ A = Y' /\ ~ A = Z' /\ ~ X' = Y' /\ ~ X' = Z' /\ ~ Y' = Z' /\
~ A = X'' /\ ~ A = Y'' /\ ~ A = Z'' /\ ~ X'' = Y'' /\ ~ X'' = Z'' /\ ~ Y'' = Z'' /\
~ X = X' /\ ~ X = X'' /\ ~ X' = X'' /\
~ Y = Y' /\ ~ Y = Y'' /\ ~ Y' = Y'' /\
~ Z = Z' /\ ~ Z = Z'' /\ ~ Z' = Z'' /\
~ X = Y' /\ ~ X = Y'' /\ ~ X = Z' /\ ~ X = Z'' /\ ~ Y = Z' /\ ~ Y = Z'' /\
~ X' = Y /\ ~ X' = Y'' /\ ~ X' = Z /\ ~ X' = Z'' /\ ~ Y' = Z /\ ~ Y' = Z'' /\
~ X'' = Y /\ ~ X'' = Y' /\ ~ X'' = Z /\ ~ X'' = Z' /\ ~ Y'' = Z /\ ~ Y'' = Z' /\
rk(A :: X :: Y :: Z :: nil) = 2 /\ rk(A :: X' :: Y' :: Z' :: nil) = 2 /\ rk(A :: X'' :: Y'' :: Z'' :: nil) = 2 /\ 
rk(P :: Q :: gamma :: nil) = 2 /\ rk(P' :: Q' :: gamma :: nil) = 2 /\
rk(P :: R :: beta :: nil) = 2 /\ rk(P' :: R' :: beta :: nil) = 2 /\
rk(Q :: R :: alpha :: nil) = 2 /\ rk(Q' :: R' :: alpha :: nil) = 2 /\
rk(A :: P :: P' :: nil) = 2 /\ rk(A :: Q :: Q' :: nil) = 2 /\ rk(A :: R :: R' :: nil) = 2 /\
rk(P :: A :: X :: Y :: Z :: nil) = 2 /\ rk(P' :: A :: X :: Y :: Z :: nil) = 2 /\ 
rk(Q :: A :: X' :: Y' :: Z' :: nil) = 2 /\ rk(Q' :: A :: X' ::  Y' :: Z' :: nil) = 2 /\ 
rk(R :: A :: X'' :: Y'' :: Z'' :: nil) = 2 /\ rk(R' :: A :: X'' :: Y'' :: Z'' :: nil) = 2 /\
rk(A :: P :: Q :: nil) = 3 /\ rk(A :: P :: R :: nil) = 3 /\ rk(A :: Q :: R :: nil) = 3 /\
rk(P :: Q :: R :: nil) = 3 /\ rk(P' :: Q' :: R' :: nil) = 3 /\ (rk(P :: P' :: nil) = 2 \/ rk(Q :: Q' :: nil) = 2 \/ rk(R :: R' :: nil) = 2) ->
rk(alpha :: beta :: gamma :: nil) = 2.
Proof.
intros X Y Z X' Y' Z' X'' Y'' Z'' P Q R P' Q' R' alpha beta gamma.
assert(HH : equivlist (alpha :: beta :: gamma :: nil) (alpha :: gamma :: beta :: nil));[my_inA|].
assert(HH0 : equivlist (alpha :: beta :: gamma :: nil) (beta :: alpha :: gamma :: nil));[my_inA|].
assert(HH1 : equivlist (alpha :: beta :: gamma :: nil) (beta :: gamma :: alpha :: nil));[my_inA|].
assert(HH2 : equivlist (alpha :: beta :: gamma :: nil) (gamma :: alpha :: beta :: nil));[my_inA|].
assert(HH3 : equivlist (alpha :: beta :: gamma :: nil) (gamma :: beta :: alpha :: nil));[my_inA|].
intros.
my_split.
assert(HH4 := degens_or P P' Q Q' R R' H68);my_split.
generalize rk_planes;intro HH5;use HH5.
case_clear_P4 X Y Z.
time(abstract (case_clear_P4 X' Y' Z';
abstract (case_clear_P4 X'' Y'' Z'';try solve_desargues_from_A_spec P Q R P' Q' R' alpha beta gamma HH HH0 HH1 HH2 HH3 HH4))).
time(abstract (case_clear_P4 X' Y' Z';
abstract (case_clear_P4 X'' Y'' Z'';try solve_desargues_from_A_spec P Q R P' Q' R' alpha beta gamma HH HH0 HH1 HH2 HH3 HH4))).
time(abstract (case_clear_P4 X' Y' Z';
abstract (case_clear_P4 X'' Y'' Z'';try solve_desargues_from_A_spec P Q R P' Q' R' alpha beta gamma HH HH0 HH1 HH2 HH3 HH4))).
time(abstract (case_clear_P4 X' Y' Z';
abstract (case_clear_P4 X'' Y'' Z'';try solve_desargues_from_A_spec P Q R P' Q' R' alpha beta gamma HH HH0 HH1 HH2 HH3 HH4))).
time(abstract (case_clear_P4 X' Y' Z';
abstract (case_clear_P4 X'' Y'' Z'';try solve_desargues_from_A_spec P Q R P' Q' R' alpha beta gamma HH HH0 HH1 HH2 HH3 HH4))).
time(abstract (case_clear_P4 X' Y' Z';
abstract (case_clear_P4 X'' Y'' Z'';try solve_desargues_from_A_spec P Q R P' Q' R' alpha beta gamma HH HH0 HH1 HH2 HH3 HH4))).
time(abstract (case_clear_P4 X' Y' Z';
abstract (case_clear_P4 X'' Y'' Z'';try solve_desargues_from_A_spec P Q R P' Q' R' alpha beta gamma HH HH0 HH1 HH2 HH3 HH4))).
time(abstract (case_clear_P4 X' Y' Z';
abstract (case_clear_P4 X'' Y'' Z'';try solve_desargues_from_A_spec P Q R P' Q' R' alpha beta gamma HH HH0 HH1 HH2 HH3 HH4))).
time(abstract (case_clear_P4 X' Y' Z';
abstract (case_clear_P4 X'' Y'' Z'';try solve_desargues_from_A_spec P Q R P' Q' R' alpha beta gamma HH HH0 HH1 HH2 HH3 HH4))).
time(abstract (case_clear_P4 X' Y' Z';
abstract (case_clear_P4 X'' Y'' Z'';try solve_desargues_from_A_spec P Q R P' Q' R' alpha beta gamma HH HH0 HH1 HH2 HH3 HH4))).
time(abstract (case_clear_P4 X' Y' Z';
abstract (case_clear_P4 X'' Y'' Z'';try solve_desargues_from_A_spec P Q R P' Q' R' alpha beta gamma HH HH0 HH1 HH2 HH3 HH4))).
time(abstract (case_clear_P4 X' Y' Z';
abstract (case_clear_P4 X'' Y'' Z'';try solve_desargues_from_A_spec P Q R P' Q' R' alpha beta gamma HH HH0 HH1 HH2 HH3 HH4))).
time(abstract (case_clear_P4 X' Y' Z';
abstract (case_clear_P4 X'' Y'' Z'';try solve_desargues_from_A_spec P Q R P' Q' R' alpha beta gamma HH HH0 HH1 HH2 HH3 HH4))).
time(abstract (case_clear_P4 X' Y' Z';
abstract (case_clear_P4 X'' Y'' Z'';try solve_desargues_from_A_spec P Q R P' Q' R' alpha beta gamma HH HH0 HH1 HH2 HH3 HH4))).
time(abstract (case_clear_P4 X' Y' Z';
abstract (case_clear_P4 X'' Y'' Z'';try solve_desargues_from_A_spec P Q R P' Q' R' alpha beta gamma HH HH0 HH1 HH2 HH3 HH4))).
time(abstract (case_clear_P4 X' Y' Z';
abstract (case_clear_P4 X'' Y'' Z'';try solve_desargues_from_A_spec P Q R P' Q' R' alpha beta gamma HH HH0 HH1 HH2 HH3 HH4))).
time(abstract (case_clear_P4 X' Y' Z';
abstract (case_clear_P4 X'' Y'' Z'';try solve_desargues_from_A_spec P Q R P' Q' R' alpha beta gamma HH HH0 HH1 HH2 HH3 HH4))).
time(abstract (case_clear_P4 X' Y' Z';
abstract (case_clear_P4 X'' Y'' Z'';try solve_desargues_from_A_spec P Q R P' Q' R' alpha beta gamma HH HH0 HH1 HH2 HH3 HH4))).
time(abstract (case_clear_P4 X' Y' Z';
abstract (case_clear_P4 X'' Y'' Z'';try solve_desargues_from_A_spec P Q R P' Q' R' alpha beta gamma HH HH0 HH1 HH2 HH3 HH4))).
time(abstract (case_clear_P4 X' Y' Z';
abstract (case_clear_P4 X'' Y'' Z'';try solve_desargues_from_A_spec P Q R P' Q' R' alpha beta gamma HH HH0 HH1 HH2 HH3 HH4))).
time(abstract (case_clear_P4 X' Y' Z';
abstract (case_clear_P4 X'' Y'' Z'';try solve_desargues_from_A_spec P Q R P' Q' R' alpha beta gamma HH HH0 HH1 HH2 HH3 HH4))).
time(abstract (case_clear_P4 X' Y' Z';
abstract (case_clear_P4 X'' Y'' Z'';try solve_desargues_from_A_spec P Q R P' Q' R' alpha beta gamma HH HH0 HH1 HH2 HH3 HH4))).
time(abstract (case_clear_P4 X' Y' Z';
abstract (case_clear_P4 X'' Y'' Z'';try solve_desargues_from_A_spec P Q R P' Q' R' alpha beta gamma HH HH0 HH1 HH2 HH3 HH4))).
time(abstract (case_clear_P4 X' Y' Z';
abstract (case_clear_P4 X'' Y'' Z'';try solve_desargues_from_A_spec P Q R P' Q' R' alpha beta gamma HH HH0 HH1 HH2 HH3 HH4))).
Qed.

End Desargues_from_A.


Module Desargues (M:fano_plane_rank).

Import M.

Module Import M2:= Desargues_from_A M.

Module swaped_B := swapfr3 M.
Module swaped_B' := Desargues_from_A swaped_B.
Module swaped_E := swapfr3 swaped_B.
Module swaped_E' := Desargues_from_A swaped_E.
Module swaped_L := swapfr3 swaped_E.
Module swaped_L' := Desargues_from_A swaped_L.
Module swaped_D := swapfr3 swaped_L.
Module swaped_D' := Desargues_from_A swaped_D.
Module swaped_H := swapfr3 swaped_D.
Module swaped_H' := Desargues_from_A swaped_H.
Module swaped_C := swapfr3 swaped_H.
Module swaped_C' := Desargues_from_A swaped_C.
Module swaped_I := swapfr3 swaped_C.
Module swaped_I' := Desargues_from_A swaped_I.
Module swaped_M := swapfr3 swaped_I.
Module swaped_M' := Desargues_from_A swaped_M.
Module swaped_F := swapfr3 swaped_M.
Module swaped_F' := Desargues_from_A swaped_F.
Module swaped_G := swapfr3 swaped_F.
Module swaped_G' := Desargues_from_A swaped_G.
Module swaped_J := swapfr3 swaped_G.
Module swaped_J' := Desargues_from_A swaped_J.
Module swaped_K := swapfr3 swaped_J.
Module swaped_K' := Desargues_from_A swaped_K.

Theorem Desargues :  forall O X Y Z X' Y' Z' X'' Y'' Z'' P Q R P' Q' R' alpha beta gamma,
~ O = X /\ ~ O = Y /\ ~ O = Z /\ ~ X = Y /\ ~ X = Z /\ ~ Y = Z /\
~ O = X' /\ ~ O = Y' /\ ~ O = Z' /\ ~ X' = Y' /\ ~ X' = Z' /\ ~ Y' = Z' /\
~ O = X'' /\ ~ O = Y'' /\ ~ O = Z'' /\ ~ X'' = Y'' /\ ~ X'' = Z'' /\ ~ Y'' = Z'' /\
~ X = X' /\ ~ X = X'' /\ ~ X' = X'' /\
~ Y = Y' /\ ~ Y = Y'' /\ ~ Y' = Y'' /\
~ Z = Z' /\ ~ Z = Z'' /\ ~ Z' = Z'' /\
~ X = Y' /\ ~ X = Y'' /\ ~ X = Z' /\ ~ X = Z'' /\ ~ Y = Z' /\ ~ Y = Z'' /\
~ X' = Y /\ ~ X' = Y'' /\ ~ X' = Z /\ ~ X' = Z'' /\ ~ Y' = Z /\ ~ Y' = Z'' /\
~ X'' = Y /\ ~ X'' = Y' /\ ~ X'' = Z /\ ~ X'' = Z' /\ ~ Y'' = Z /\ ~ Y'' = Z' /\
rk(O :: X :: Y :: Z :: nil) = 2 /\ rk(O :: X' :: Y' :: Z' :: nil) = 2 /\ rk(O :: X'' :: Y'' :: Z'' :: nil) = 2 /\ 
rk(P :: Q :: gamma :: nil) = 2 /\ rk(P' :: Q' :: gamma :: nil) = 2 /\
rk(P :: R :: beta :: nil) = 2 /\ rk(P' :: R' :: beta :: nil) = 2 /\
rk(Q :: R :: alpha :: nil) = 2 /\ rk(Q' :: R' :: alpha :: nil) = 2 /\
rk(O :: P :: P' :: nil) = 2 /\ rk(O :: Q :: Q' :: nil) = 2 /\ rk(O :: R :: R' :: nil) = 2 /\
rk(P :: O :: X :: Y :: Z :: nil) = 2 /\ rk(P' :: O :: X :: Y :: Z :: nil) = 2 /\ 
rk(Q :: O :: X' :: Y' :: Z' :: nil) = 2 /\ rk(Q' :: O :: X' ::  Y' :: Z' :: nil) = 2 /\ 
rk(R :: O :: X'' :: Y'' :: Z'' :: nil) = 2 /\ rk(R' :: O :: X'' :: Y'' :: Z'' :: nil) = 2 /\
rk(O :: P :: Q :: nil) = 3 /\ rk(O :: P :: R :: nil) = 3 /\ rk(O :: Q :: R :: nil) = 3 /\
rk(P :: Q :: R :: nil) = 3 /\ rk(P' :: Q' :: R' :: nil) = 3 /\ (rk(P :: P' :: nil) = 2 \/ rk(Q :: Q' :: nil) = 2 \/ rk(R :: R' :: nil) = 2) ->
rk(alpha :: beta :: gamma :: nil) = 2.
Proof.
intros.
case_clear_1 O.
rewrite a0 in *.
apply (Desargues_from_A X Y Z X' Y' Z' X'' Y'' Z'' P Q R P' Q' R' alpha beta gamma);assumption.

rewrite b in *.
assert(T:=swaped_B'.Desargues_from_A ).
unfold swaped_B.A in *.
eapply (T X Y Z X' Y' Z' X'' Y'' Z'' P Q R P' Q' R' alpha beta gamma);assumption.

rewrite b in *.
assert(T:=swaped_C'.Desargues_from_A ).
unfold swaped_C.A in *.
eapply (T X Y Z X' Y' Z' X'' Y'' Z'' P Q R P' Q' R' alpha beta gamma);assumption.

rewrite b in *.
assert(T:=swaped_D'.Desargues_from_A ).
unfold swaped_D.A in *.
eapply (T X Y Z X' Y' Z' X'' Y'' Z'' P Q R P' Q' R' alpha beta gamma);assumption.

rewrite b in *.
assert(T:=swaped_E'.Desargues_from_A ).
unfold swaped_E.A in *.
eapply (T X Y Z X' Y' Z' X'' Y'' Z'' P Q R P' Q' R' alpha beta gamma);assumption.

rewrite b in *.
assert(T:=swaped_F'.Desargues_from_A ).
unfold swaped_F.A in *.
eapply (T X Y Z X' Y' Z' X'' Y'' Z'' P Q R P' Q' R' alpha beta gamma);assumption.

rewrite b in *.
assert(T:=swaped_G'.Desargues_from_A ).
unfold swaped_G.A in *.
eapply (T X Y Z X' Y' Z' X'' Y'' Z'' P Q R P' Q' R' alpha beta gamma);assumption.

rewrite b in *.
assert(T:=swaped_H'.Desargues_from_A ).
unfold swaped_H.A in *.
eapply (T X Y Z X' Y' Z' X'' Y'' Z'' P Q R P' Q' R' alpha beta gamma);assumption.

rewrite b in *.
assert(T:=swaped_I'.Desargues_from_A ).
unfold swaped_I.A in *.
eapply (T X Y Z X' Y' Z' X'' Y'' Z'' P Q R P' Q' R' alpha beta gamma);assumption.

rewrite b in *.
assert(T:=swaped_J'.Desargues_from_A ).
unfold swaped_J.A in *.
eapply (T X Y Z X' Y' Z' X'' Y'' Z'' P Q R P' Q' R' alpha beta gamma);assumption.

rewrite b in *.
assert(T:=swaped_K'.Desargues_from_A ).
unfold swaped_K.A in *.
eapply (T X Y Z X' Y' Z' X'' Y'' Z'' P Q R P' Q' R' alpha beta gamma);assumption.

rewrite b in *.
assert(T:=swaped_L'.Desargues_from_A ).
unfold swaped_L.A in *.
eapply (T X Y Z X' Y' Z' X'' Y'' Z'' P Q R P' Q' R' alpha beta gamma);assumption.

rewrite b in *.
assert(T:=swaped_M'.Desargues_from_A ).
unfold swaped_M.A in *.
eapply (T X Y Z X' Y' Z' X'' Y'' Z'' P Q R P' Q' R' alpha beta gamma);assumption.
Qed.

End Desargues.
