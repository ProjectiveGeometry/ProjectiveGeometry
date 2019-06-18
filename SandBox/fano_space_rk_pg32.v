Require Import ProjectiveGeometry.Dev.fano_rk_tactics.

(*****************************************************************************)
(** pg(3,2) rank **)

Module Type pg32_rank.

Parameter A B C D E F G H I J K L M N O: Point.

Parameter is_only_15_pts : forall P, {P=A}+{P=B}+{P=C}+{P=D}+{P=E}+{P=F}+{P=G}+{P=H}+{P=I}+{P=J}+{P=K}+{P=L}+{P=M}+{P=N}+{P=O}.

Parameter rk_points_fact : forall P, rk (P::nil) = 1.

Parameter rk_points : rk(A :: nil) = 1 /\ rk(B :: nil) = 1 /\ rk(C :: nil) = 1 /\ rk(D :: nil) = 1 /\
rk(E :: nil) = 1 /\ rk(F :: nil) = 1 /\ rk(G :: nil) = 1 /\ rk(H :: nil) = 1 /\ rk(I :: nil) = 1 /\ 
rk(J :: nil) = 1 /\ rk(K :: nil) = 1 /\ rk(L :: nil) = 1 /\ rk(M :: nil) = 1 /\ rk(N :: nil) = 1 /\ rk(O :: nil) = 1.

Parameter rk_distinct_points : 
rk(A :: B :: nil) = 2 /\ rk(A :: C :: nil) = 2 /\ rk(A :: D :: nil) = 2 /\ rk(A :: E :: nil) = 2 /\ rk(A :: F :: nil) = 2 /\ rk(A :: G :: nil) = 2 /\
rk(A :: H :: nil) = 2 /\ rk(A :: I :: nil) = 2 /\ rk(A :: J :: nil) = 2 /\ rk(A :: K :: nil) = 2 /\ rk(A :: L :: nil) = 2 /\ rk(A :: M :: nil) = 2 /\
rk(A :: N :: nil) = 2 /\ rk(A :: O :: nil) = 2 /\
rk(B :: C :: nil) = 2 /\ rk(B :: D :: nil) = 2 /\ rk(B :: E :: nil) = 2 /\ rk(B :: F :: nil) = 2 /\ rk(B :: G :: nil) = 2 /\
rk(B :: H :: nil) = 2 /\ rk(B :: I :: nil) = 2 /\ rk(B :: J :: nil) = 2 /\ rk(B :: K :: nil) = 2 /\ rk(B :: L :: nil) = 2 /\ rk(B :: M :: nil) = 2 /\
rk(B :: N :: nil) = 2 /\ rk(B :: O :: nil) = 2 /\
rk(C :: D :: nil) = 2 /\ rk(C :: E :: nil) = 2 /\ rk(C :: F :: nil) = 2 /\ rk(C :: G :: nil) = 2 /\
rk(C :: H :: nil) = 2 /\ rk(C :: I :: nil) = 2 /\ rk(C :: J :: nil) = 2 /\ rk(C :: K :: nil) = 2 /\ rk(C :: L :: nil) = 2 /\ rk(C :: M :: nil) = 2 /\
rk(C :: N :: nil) = 2 /\ rk(C :: O :: nil) = 2 /\
rk(D :: E :: nil) = 2 /\ rk(D :: F :: nil) = 2 /\ rk(D :: G :: nil) = 2 /\
rk(D :: H :: nil) = 2 /\ rk(D :: I :: nil) = 2 /\ rk(D :: J :: nil) = 2 /\ rk(D :: K :: nil) = 2 /\ rk(D :: L :: nil) = 2 /\ rk(D :: M :: nil) = 2 /\
rk(D :: N :: nil) = 2 /\ rk(D :: O :: nil) = 2 /\
rk(E :: F :: nil) = 2 /\ rk(E :: G :: nil) = 2 /\
rk(E :: H :: nil) = 2 /\ rk(E :: I :: nil) = 2 /\ rk(E :: J :: nil) = 2 /\ rk(E :: K :: nil) = 2 /\ rk(E :: L :: nil) = 2 /\ rk(E :: M :: nil) = 2 /\
rk(E :: N :: nil) = 2 /\ rk(E :: O :: nil) = 2 /\
rk(F :: G :: nil) = 2 /\
rk(F :: H :: nil) = 2 /\ rk(F :: I :: nil) = 2 /\ rk(F :: J :: nil) = 2 /\ rk(F :: K :: nil) = 2 /\ rk(F :: L :: nil) = 2 /\ rk(F :: M :: nil) = 2 /\
rk(F :: N :: nil) = 2 /\ rk(F :: O :: nil) = 2 /\
rk(G :: H :: nil) = 2 /\ rk(G :: I :: nil) = 2 /\ rk(G :: J :: nil) = 2 /\ rk(G :: K :: nil) = 2 /\ rk(G :: L :: nil) = 2 /\ rk(G :: M :: nil) = 2 /\
rk(G :: N :: nil) = 2 /\ rk(G :: O :: nil) = 2 /\
rk(H :: I :: nil) = 2 /\ rk(H :: J :: nil) = 2 /\ rk(H :: K :: nil) = 2 /\ rk(H :: L :: nil) = 2 /\ rk(H :: M :: nil) = 2 /\
rk(H :: N :: nil) = 2 /\ rk(H :: O :: nil) = 2 /\
rk(I :: J :: nil) = 2 /\ rk(I :: K :: nil) = 2 /\ rk(I :: L :: nil) = 2 /\ rk(I :: M :: nil) = 2 /\
rk(I :: N :: nil) = 2 /\ rk(I :: O :: nil) = 2 /\
rk(J :: K :: nil) = 2 /\ rk(J :: L :: nil) = 2 /\ rk(J :: M :: nil) = 2 /\
rk(J :: N :: nil) = 2 /\ rk(J :: O :: nil) = 2 /\
rk(K :: L :: nil) = 2 /\ rk(K :: M :: nil) = 2 /\
rk(K :: N :: nil) = 2 /\ rk(K :: O :: nil) = 2 /\
rk(L :: M :: nil) = 2 /\
rk(L :: N :: nil) = 2 /\ rk(L :: O :: nil) = 2 /\
rk(M :: N :: nil) = 2 /\ rk(M :: O ::nil) = 2 /\
rk(N :: O :: nil) = 2.

Parameter rk_lines :
  rk (A :: B :: C :: nil) = 2 /\ rk (A :: D :: E :: nil) = 2 /\
  rk (A :: F :: G :: nil) = 2 /\ rk (A :: H :: I :: nil) = 2 /\
  rk (A :: K :: J :: nil) = 2 /\ rk (A :: L :: M :: nil) = 2 /\
  rk (A :: N :: O :: nil) = 2 /\
  rk (B :: E :: G :: nil) = 2 /\ rk (B :: I :: K :: nil) = 2 /\
  rk (B :: M :: O :: nil) = 2 /\ rk (B :: H :: J :: nil) = 2 /\
  rk (B :: N :: L :: nil) = 2 /\ rk (B :: D :: F :: nil) = 2 /\
  rk (C :: H :: K :: nil) = 2 /\ rk (C :: L :: O :: nil) = 2 /\
  rk (C :: D :: G :: nil) = 2 /\ rk (C :: M :: N :: nil) = 2 /\
  rk (C :: E :: F :: nil) = 2 /\ rk (C :: I :: J :: nil) = 2 /\
  rk (D :: K :: O :: nil) = 2 /\ rk (D :: I :: M :: nil) = 2 /\
  rk (D :: J :: N :: nil) = 2 /\ rk (D :: H :: L :: nil) = 2 /\
  rk (E :: J :: O :: nil) = 2 /\ rk (E :: I :: L :: nil) = 2 /\
  rk (E :: K :: N :: nil) = 2 /\ rk (E :: H :: M :: nil) = 2 /\
  rk (F :: I :: O :: nil) = 2 /\ rk (F :: H :: N :: nil) = 2 /\
  rk (F :: J :: L :: nil) = 2 /\ rk (F :: K :: M :: nil) = 2 /\
  rk (G :: H :: O :: nil) = 2 /\ rk (G :: I :: N :: nil) = 2 /\
  rk (G :: J :: M :: nil) = 2 /\ rk (G :: K :: L :: nil) = 2.

(* Lemma rk_3_distinct : forall P Q R, P<>Q -> P<>R->Q<>R-> rk(P::Q::R::nil)=2\/rk(P::Q::R::nil)=3.
Proof.*)

  (* rk_planes from incid ? *)

Parameter rk_planes :
  (*1*)rk(A::B::D::nil)=3 /\ rk(A::B::E::nil)=3 /\ rk(A::B::F::nil)=3 /\ rk(A::B::G::nil)=3 /\ rk(A::B::H::nil)=3 /\
  rk(A::B::I::nil)=3 /\ rk(A::B::J::nil)=3 /\ rk(A::B::K::nil)=3 /\ rk(A::B::L::nil)=3 /\ rk(A::B::M::nil)=3 /\
  rk(A::B::N::nil)=3 /\ rk(A::B::O::nil)=3 /\
  (*2*)rk(A::C::D::nil)=3/\  rk(A::C::E::nil)=3/\  rk(A::C::F::nil)=3/\  rk(A::C::G::nil)=3/\  rk(A::C::H::nil)=3/\
  rk(A::C::I::nil)=3/\  rk(A::C::J::nil)=3/\  rk(A::C::K::nil)=3/\  rk(A::C::L::nil)=3/\  rk(A::C::M::nil)=3/\
  rk(A::C::N::nil)=3/\  rk(A::C::O::nil)=3/\
  (*3*)rk(A::D::F::nil) = 3 /\rk(A::D::G::nil) = 3 /\rk(A::D::H::nil) = 3 /\rk(A::D::I::nil) = 3 /\
  rk(A::D::J::nil) = 3 /\ rk(A::D::K::nil) = 3 /\rk(A::D::L::nil) = 3 /\rk(A::D::M::nil) = 3 /\rk(A::D::N::nil) = 3 /\
  rk(A::D::O::nil) = 3 /\
  (*4*)rk(A::E::F::nil)=3/\rk(A::E::G::nil)=3/\rk(A::E::H::nil)=3/\rk(A::E::I::nil)=3/\rk(A::E::J::nil)=3/\
  rk(A::E::K::nil)=3/\rk(A::E::L::nil)=3/\rk(A::E::M::nil)=3/\rk(A::E::N::nil)=3/\rk(A::E::O::nil)=3/\
  (*5*)rk(A::F::H::nil)=3/\rk(A::F::I::nil)=3/\rk(A::F::J::nil)=3/\rk(A::F::K::nil)=3/\rk(A::F::L::nil)=3/\
  rk(A::F::M::nil)=3/\rk(A::F::N::nil)=3/\rk(A::F::O::nil)=3/\
  (*6*)rk(A::G::H::nil)=3/\rk(A::G::I::nil)=3/\rk(A::G::J::nil)=3/\rk(A::G::K::nil)=3/\rk(A::G::L::nil)=3/\
  rk(A::G::M::nil)=3/\rk(A::G::N::nil)=3/\rk(A::G::O::nil)=3/\
  (*7*)rk(A::H::J::nil)=3/\rk(A::H::K::nil)=3/\rk(A::H::L::nil)=3/\rk(A::H::M::nil)=3/\rk(A::H::N::nil)=3/\
  rk(A::H::O::nil)=3/\
  (*8*)rk(A::I::J::nil)=3/\rk(A::I::K::nil)=3/\rk(A::I::L::nil)=3/\rk(A::I::M::nil)=3/\rk(A::I::N::nil)=3/\rk(A::I::O::nil)=3/\
  (*9*)rk(A::J::L::nil)=3/\rk(A::J::M::nil)=3/\rk(A::J::N::nil)=3/\rk(A::J::O::nil)=3/\
  (*10*)rk(A::K::L::nil)=3/\rk(A::K::M::nil)=3/\rk(A::K::N::nil)=3/\rk(A::K::O::nil)=3/\
  (*11*)rk(A::L::N::nil)=3/\rk(A::L::O::nil)=3/\
  (*12*)rk(A::M::N::nil)=3/\rk(A::L::O::nil)=3/\
  (*13*)(*rien*)
True. (* to be continued with B, C etc.*)


  
(*
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
 *)

Lemma rk_singleton_ge : forall x, rk (x ::nil) >= 1.
Proof.
  assert (H:=rk_points); use H.
  intros x; assert (s:=is_only_15_pts x); repeat destruct s as [s | H]; subst;omega.
Qed.
Lemma sub_lemma : forall P:Type, forall x:P, x<>x->False.
Proof.
  solve [intros; intuition].
Qed.

Lemma easy : forall x:nat, x=2 -> x>=2.
Proof.
  intros; omega.
Qed.

Lemma rk_couple_ge : forall P Q, ~ P = Q -> rk(P :: Q :: nil) >= 2.
Proof.
  assert (H:=rk_distinct_points); use H.
  intros x y Hxy.
  assert (sx:=is_only_15_pts x); repeat destruct sx as [sx | Hx];
  assert (sy:=is_only_15_pts y); repeat destruct sy as [sy | Hy]; subst; first [contradiction | apply easy; assumption | rewrite couple_equal; apply easy; assumption].
Qed.

Ltac new_case P := 
match (type of P) with 
| Point => generalize (is_only_15_pts P) ; let Q := fresh in (intros Q; decompose [sumor sumbool] Q; clear Q)
end.

Ltac case_eq_s O := new_case O.

Ltac case_clear_1 P := case_eq_s P.

Ltac case_clear_2 P :=
  case_clear_1 P;
  match goal with
| H : P = ?X |- _ => subst
  end.

Ltac degens_rk2 :=
match goal with
| H : _ |- rk(?P :: ?P :: ?R :: nil) = 2 => try solve[apply triple_rk2_1;rk_couple_bis_bis;assumption]
| H : _ |- rk(?P :: ?R :: ?P :: nil) = 2 => try solve[apply triple_rk2_2;rk_couple_bis_bis;assumption]
| H : _ |- rk(?R :: ?P :: ?P :: nil) = 2 => try solve[apply triple_rk2_3;rk_couple_bis_bis;assumption]
end.

Ltac solve_ex_1 L := solve[exists L;repeat split;[try degens_rk2;assumption|rk_couple_bis_bis|rk_couple_bis_bis]].

Ltac solve_ex_p_1 := first [
        solve_ex_1 A
     |  solve_ex_1 B
     |  solve_ex_1 C
     |  solve_ex_1 D
     |  solve_ex_1 E
     |  solve_ex_1 F
     |  solve_ex_1 G
     |  solve_ex_1 H
     |  solve_ex_1 I
     |  solve_ex_1 J
     |  solve_ex_1 K
     |  solve_ex_1 L
     |  solve_ex_1 M
     |  solve_ex_1 N
     |  solve_ex_1 O
 ].

Ltac rk_three_points_simplify P Q :=
match goal with
| H : rk(P :: Q :: ?X :: nil) = 2 |- _ => solve_ex_1 X
| H : rk(P :: ?X :: Q :: nil) = 2 |- _ => rewrite <-triple_equal_1 in H;solve_ex_1 X
| H : rk(Q :: P :: ?X :: nil) = 2 |- _ => rewrite <-triple_equal_2 in H;solve_ex_1 X
| H : rk(Q :: ?X :: P :: nil) = 2 |- _ => rewrite <-triple_equal_3 in H;solve_ex_1 X
| H : rk(?X :: P :: Q :: nil) = 2 |- _ => rewrite <-triple_equal_4 in H;solve_ex_1 X
| H : rk(?X :: Q :: P :: nil) = 2 |- _ => rewrite <-triple_equal_5 in H;solve_ex_1 X
end.

Ltac rk_three_points_simplify_bis :=
match goal with
| H : _ |- exists R, rk (?P :: ?P :: _ :: nil) = 2 /\ _ /\ _ => solve_ex_p_1
| H : _ |- exists R, rk (?P :: ?Q :: _ :: nil) = 2 /\ _ /\ _ => rk_three_points_simplify P Q
end.

Lemma rk_three_points_on_lines : forall P Q, exists R, rk ( P :: Q :: R :: nil) = 2 /\ rk (Q :: R :: nil) = 2 /\ rk (P :: R :: nil) = 2.
Proof.
  intros.
assert(HH := rk_distinct_points);assert(HH0 := rk_lines);use HH;use HH0.
time(case_clear_2 P;case_clear_2 Q; try rk_three_points_simplify_bis).
Qed.

Ltac rk_three_points_simplify_bis2 :=
match goal with
| H : _ |- exists R, rk (?P :: ?P :: _ :: nil) = 2 /\ _  => solve_ex_p_1
| H : _ |- exists R, rk (?P :: ?Q :: _ :: nil) = 2 /\ _  => rk_three_points_simplify P Q
end.

Ltac solver := match goal with
       | |- exists J0 : Point, rk (?X :: ?X :: J0 :: nil) = 2 /\ rk (?X :: ?Y :: J0 :: nil) = 2 => idtac "coucou" end.

Search (rk(_::_::_::nil)=2).
Lemma rk_simpl1 : forall P Q, rk(P::P::Q::nil)=rk(P::Q::nil).
Proof.
  intros; apply rk_compat.
  Search _ equivlist.
  split; intros; inversion H0; subst.
  apply in_eq.
  assumption.
apply in_eq.
   inversion H1; subst.
apply in_cons; apply in_cons; apply in_eq.
inversion H2.
Qed.

Parameter rk_simpl2 : forall P Q, rk(P::Q::Q::nil)=rk(P::Q::nil).
Check triple_rk2_3.

Lemma triple_equal_1' : forall n A B C, rk (A :: B :: C :: nil) = n -> rk (A :: C :: B :: nil) = n.
Proof.
  intros.
rewrite <- triple_equal_1; assumption.  
Qed.

Lemma triple_equal_2' : 
     forall n A B C,
    rk (A :: B :: C :: nil) = n -> rk (B :: A :: C :: nil) = n.
Proof.
  intros.
rewrite <- triple_equal_2; assumption.  
Qed.

Lemma triple_equal_3'
     : forall n A B C,
    rk (A :: B :: C :: nil) = n -> rk (B :: C :: A :: nil) = n.
Proof.
  intros.
  rewrite <- triple_equal_3; assumption.  
Qed.

Lemma triple_equal_4' 
     : forall n A B C,
    rk (A :: B :: C :: nil) = n -> rk (C :: A :: B :: nil) = n.

  Proof.
  intros.
  rewrite <- triple_equal_4; assumption.  
Qed.

Lemma triple_equal_5'
     : forall n A B C,
    rk (A :: B :: C :: nil) = n -> rk (C :: B :: A :: nil) = n.
 Proof.
  intros.
rewrite <- triple_equal_5; assumption.  
Qed.

Lemma couple_equal' : forall n A B,
       rk (A :: B :: nil) = n -> rk (B :: A :: nil) = n.
Proof.
  intros.
  rewrite couple_equal; assumption.
Qed.

Ltac assumption_modulo := match goal with
                          | H:rk(?A::?B::nil)=2 |- rk(?A::?B::nil)=2 => exact H
                          | H:rk(?B::?A::nil)=2 |- rk(?A::?B::nil)=2 => apply (couple_equal' _ _ _ H)

                          | H:rk(?A::?B::nil)=_ |- rk(?A::?A::?B::nil)=_ => apply (triple_rk2_1 _ _ H)
                          | H:rk(?B::?A::nil)=_ |- rk(?A::?B::?B::nil)=_ => apply (triple_rk2_3 _ _ H)
                          | H:rk(?A::?B::nil)=_ |- rk(?A::?B::?A::nil)=_ => apply (triple_rk2_2 _ _ H)

                          | H:rk(?B::?A::nil)=_ |- rk(?A::?A::?B::nil)=_ => apply (triple_rk2_1 _ _ (couple_equal' _ _ _ H))
                          | H:rk(?A::?B::nil)=_ |- rk(?A::?B::?B::nil)=_ => apply (triple_rk2_3 _ _ (couple_equal' _ _ _ H))
                          | H:rk(?B::?A::nil)=_ |- rk(?A::?B::?A::nil)=_ => apply (triple_rk2_2 _ _ (couple_equal' _ _ _ H))

                          | H:rk(?A::?B::?C::nil)=_ |- rk(?A::?B::?C::nil)=_ => exact H
                          | H:rk(?A::?B::?C::nil)=_ |- rk(?A::?C::?B::nil)=_ => apply (triple_equal_1' _ _ _ _ H)
                          | H:rk(?A::?B::?C::nil)=_ |- rk(?B::?A::?C::nil)=_ => apply (triple_equal_2' _ _ _ _ H)
                          | H:rk(?A::?B::?C::nil)=_ |- rk(?B::?C::?A::nil)=_ => apply (triple_equal_3' _ _ _ _ H)
                          | H:rk(?A::?B::?C::nil)=_ |- rk(?C::?A::?B::nil)=_ => apply (triple_equal_4' _ _ _ _ H)
                          | H:rk(?A::?B::?C::nil)=_ |- rk(?C::?B::?A::nil)=_ => apply (triple_equal_5' _ _ _ _ H)
end.


Lemma f : forall P Q R, rk(P::R::Q::nil)=2 -> rk(Q::P::R::nil)=2.
  intros.
  assumption_modulo.
Qed.

Ltac concl T := solve [exists T; split; assumption_modulo].

Ltac concl_all := first [
        concl A
     |  concl B
     |  concl C
     |  concl D
     |  concl E
     |  concl F
     |  concl G
     |  concl H
     |  concl I
     |  concl J
     |  concl K
     |  concl L
     |  concl M
     |  concl N
     |  concl O
 ].

Lemma rk_pasch : forall P Q R S, rk (P :: Q :: R :: S :: nil) <= 3 -> exists J, rk (P :: Q :: J :: nil) = 2 /\ rk (R :: S :: J :: nil) = 2.
Proof.
  intros.
  assert (HH := rk_distinct_points);assert(HH0 := rk_lines);use HH;use HH0.
  time(case_clear_2 P).
  Focus 1.
  Set Ltac Profiling.
  time ( case_clear_2 Q; case_clear_2 R; (case_clear_2 S; try concl_all)).
  Focus 5.
  Parameter rk_spaces :
    rk(A::B::D::H::nil)=4/\rk(A::B::D::I::nil)=4/\rk(A::B::D::J::nil)=4/\rk(A::B::D::K::nil)=4/\rk (A::B::D::L::nil)=4/\(rk (A::F::I::K::nil)=4).
  
  assert (rk (A::F::I::K::nil)>=4).
  assert (H:=matroid3 (A::F::I::nil) (A::F::K::nil)).
  assert (rk (A::F::I::K::nil)>= 
  rk AFI + rk AFK >= rk union (AFIAFK) + rk (AFI)inter (AFK) =2
      3       3             ?                         AF 2                   6 >= rk union (AFIAFK) + 2
                                                                                                        4>=rk union AFIAFK

rk(union X Y) + rk(inter X Y) <= rk X + rk Y                                                                                                             
  omega.
          rk X >= rk(union X Y) + rk (inter X Y) - rk Y
rk AFIK >= rk (AFIK union tout le reste)+ rk tout le reste inter AFIK - rk A
                                                      X=AFIK
          exists B.
  split.
  Check triple_rk2_3.
apply triple_rk2_3.
Check triple_rk2_1.
assumption_modulo.
apply 
assumption_modulo.
exists A.

  Show Ltac Profile.
concl B.
concl B.
concl C.
concl D.   
concl E.
concl F.   
concl G.
exists D.
   try rewrite rk_simpl1; try rewrite rk_simpl2. ; split; assumption.
Search _ rk.
  Locate triple_rk2_1.
rewrite rk_simpl2
  solvr.
  rk_three_points_simplify_bis2.
  
  
  exists B.
  Focus 1.
  
  split; rk_three_points_simplify A B.

  ; case_clear_2 S). 

  exists B.
*)
  
                                                                       Admitted.  

Lemma rk_lower_dim : exists P0, exists P1, exists P2, exists P3, rk (P0 :: P1 :: P2 :: P3 :: nil) = 4.
Proof.
(* easy from rk_spaces *)
Admitted.


Lemma rk_upper_dim : forall P Q R S, rk(P :: Q :: R :: S :: nil) <= 4.
  intros.
  case_clear_2 P; case_clear_2 Q.

Admitted.

End pg32_rank.
(*****************************************************************************)

(*****************************************************************************)


Locate decidability.Point.



P0 : Point;
P1 : Point;
P2 : Point;
P3 : Point;
rk_lower_dim : rk (quadruple P0 P1 P2 P3) = 4.

rk_upper_dim : forall A B C D, rk(quadruple A B C D) <= 4
                                                          
Instance ObjectPoint_PG32 : ObjectPoint := {Point := Point}.

Instance MatroidRk_PG32 : MatroidRk ObjectPoint_PG32 := {
rk := rk
}.

MatroidRk
Instance ObjectPointPG32 : ObjectPoint.

Instance ProjectiveStructureFano : ProjectiveStructure ObjectPointFano := {
Line := Line;
Incid := Incid;
incid_dec := incid_dec
}.

Instance ProjectiveStructureLEFano : ProjectiveStructureLE ProjectiveStructureFano := {
a1_exist := a1_exist
}.

Instance ProjectiveStructureLEUFano : ProjectiveStructureLEU ProjectiveStructureLEFano := {
uniqueness := uniqueness
}.

Instance PreProjectivePlaneFano : PreProjectivePlane ProjectiveStructureLEUFano := {
a2_exist := a2_exist
}.

Instance ProjectivePlaneFano : ProjectivePlane PreProjectivePlaneFano := {
a3 := a3
}.

Class RankProjectiveSpace `(RP : RankProjective) := {
rk_pasch : forall A B C D, rk (quadruple A B C D) <= 3 -> exists J, rk (triple A B J) = 2 /\ rk (triple C D J) = 2;

P0 : Point;
P1 : Point;
P2 : Point;
P3 : Point;
rk_lower_dim : rk (quadruple P0 P1 P2 P3) = 4;

rk_upper_dim : forall A B C D, rk(quadruple A B C D) <= 4
}.

(* Local Variables: *)
(* coq-prog-name: "/Users/magaud/.opam/4.04.0/bin/coqtop" *)
(* coq-load-path: (("/Users/magaud/containers/theories" "Containers") ("/Users/magaud/galapagos/dev/trunk/ProjectiveGeometry/" "ProjectiveGeometry")) *)
(* suffixes: .v *)
(* End: *)