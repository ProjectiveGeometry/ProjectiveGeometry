Require Export ProjectiveGeometry.Dev.basic_plane_facts.

Section s_ProjectivePlane'ToProjectivePlane.

Context `{PP : ProjectivePlane'}.
Context `{EP : EqDecidability Point}.

(** M and P are the same and lie at the meeting point between l1 and l2 **)

Lemma case1 : forall M N O P Q R : Point, forall l1 l2 : Line, 
  l1 <> l2 -> 
  ~ M [==] N /\ ~ M [==] O /\ ~ N [==] O /\ Incid M l1 /\ Incid N l1 /\ Incid O l1 ->
  ~ P [==] Q /\ ~ P [==] R /\ ~ Q [==] R /\ Incid P l2 /\ Incid Q l2 /\ Incid R l2 ->
  Incid M l2 -> Incid P l1 -> 
  {A : Point & {B : Point & {C : Point & {D : Point |
          forall l : Line,
            ~ A [==] B /\ ~ A [==] C /\ ~ A [==] D /\ ~ B [==] C /\ ~ B [==] D /\ ~ C [==] D /\
            (Incid A l /\ Incid B l -> ~ Incid C l /\ ~ Incid D l) /\
            (Incid A l /\ Incid C l -> ~ Incid B l /\ ~ Incid D l) /\
            (Incid A l /\ Incid D l -> ~ Incid C l /\ ~ Incid B l) /\
            (Incid C l /\ Incid B l -> ~ Incid A l /\ ~ Incid D l) /\
            (Incid D l /\ Incid B l -> ~ Incid C l /\ ~ Incid A l) /\
            (Incid C l /\ Incid D l -> ~ Incid B l /\ ~ Incid A l)}}}}.
Proof.
intros M N O P Q R l1 l2 H1 H2 H3 HMl2 HPl1.
intuition.
assert (~Incid N l2).
intro HNl2.
generalize (a2_unique l1 l2 M N H1 H6 HMl2 H8 HNl2); intros H'.
rewrite H' in *.
apply H; trivial.
assert (~Incid O l2).
intro HOl2.
generalize (a2_unique l1 l2 M O H1 H6 HMl2 H11 HOl2); intros H'.
rewrite H' in *.
apply H3; trivial.
assert (~Incid Q l1).
intros HQl1.
generalize (a2_unique l1 l2 P Q H1 HPl1 H7 HQl1 H9); intros H'.
rewrite H' in *.
apply H2; trivial.
assert (~Incid R l1).
intros HRl1.
generalize (a2_unique l1 l2 P R H1 HPl1 H7 HRl1 H12); intros H'.
rewrite H' in *.
apply H0; trivial.
exists N. 
exists O. 
exists Q. 
exists R.
intros l.
split.
assumption.
split.
intros HNQ.
rewrite HNQ in *;contradiction.
split.
intros HNR.
rewrite HNR in *;contradiction.
split.
intros HOQ.
rewrite HOQ in *;contradiction.
split.
intros HOR.
rewrite HOR in *;contradiction.
split.
assumption.
split.
intros (Hnew1, Hnew2).
generalize (a1_unique N O l l1 H4 Hnew1 Hnew2 H8 H11); intros H'.
subst l.
solve[intuition].
split.
intros (Hnew1, Hnew2).
split.
intros HOl.
generalize (a1_unique N O l l1 H4 Hnew1 HOl H8 H11); intros H'.

subst l.
solve[intuition].
intros HRl.
generalize (a1_unique Q R l l2 H5 Hnew2 HRl H9 H12) ; intros H'.
subst l.
solve[intuition].

split.
intros (Hnew1,Hnew2).
split.
intros HQl.
generalize (a1_unique Q R l l2 H5 HQl Hnew2 H9 H12) ; intros H'.
subst l.
solve[intuition].
intros HOl.
generalize (a1_unique N O l l1 H4 Hnew1 HOl H8 H11); intros H'.
subst l.
solve[intuition].
 
split.
intros (Hnew1, Hnew2).
split.
intros HNl.
generalize (a1_unique N O l l1 H4 HNl Hnew2 H8 H11); intros H'.
subst l.
solve[intuition].
intros HRl.
generalize (a1_unique Q R l l2 H5 Hnew1 HRl H9 H12) ; intros H'.
subst l.
solve[intuition].

split.
intros (Hnew1,Hnew2).
split.
intros HQl.
generalize (a1_unique Q R l l2 H5 HQl Hnew1 H9 H12) ; intros H'.
subst l.
solve[intuition].
intros HNl.
generalize (a1_unique N O l l1 H4 HNl Hnew2 H8 H11); intros H'.
subst l.
solve[intuition].
intros (Hnew1, Hnew2).
generalize (a1_unique Q R l l2 H5 Hnew1 Hnew2 H9 H12) ; intros H'.
subst l.
solve[intuition].
Qed.

Lemma case2 : forall M N O P Q R : Point, forall l1 l2 : Line, 
  l1 <> l2 -> 
  ~ M [==] N /\ ~ M [==] O /\ ~ N [==] O /\ Incid M l1 /\ Incid N l1 /\ Incid O l1 ->
  ~ P [==] Q /\ ~ P [==] R /\ ~ Q [==] R /\ Incid P l2 /\ Incid Q l2 /\ Incid R l2 ->
  Incid M l2 -> ~Incid P l1 -> ~Incid Q l1 -> ~Incid R l1 -> 
  {A : Point & {B : Point & {C : Point & {D : Point |
          forall l : Line,
            ~ A [==] B /\ ~ A [==] C /\ ~ A [==] D /\ ~ B [==] C /\ ~ B [==] D /\ ~ C [==] D /\
            (Incid A l /\ Incid B l -> ~ Incid C l /\ ~ Incid D l) /\
            (Incid A l /\ Incid C l -> ~ Incid B l /\ ~ Incid D l) /\
            (Incid A l /\ Incid D l -> ~ Incid C l /\ ~ Incid B l) /\
            (Incid C l /\ Incid B l -> ~ Incid A l /\ ~ Incid D l) /\
            (Incid D l /\ Incid B l -> ~ Incid C l /\ ~ Incid A l) /\
            (Incid C l /\ Incid D l -> ~ Incid B l /\ ~ Incid A l)}}}}.
Proof.
intros M N O P Q R l1 l2 H1 H2 H3 HMl2 HPl1 HQl1 HRl1.
intuition.
assert (~Incid N l2).
intro HNl2.
generalize (a2_unique l1 l2 M N H1 H6 HMl2 H8 HNl2); intros H'.
rewrite H' in *.
apply H; trivial.
assert (~Incid O l2).
intro HOl2.
generalize (a2_unique l1 l2 M O H1 H6 HMl2 H11 HOl2); intros H'.
rewrite H' in *.
apply H3; trivial.
exists N.
exists R.
exists Q.
exists O.
intros l.
split.
intros HNR.
rewrite HNR in *;contradiction.
split.
intros HNQ.
rewrite HNQ in *;contradiction.
split.
assumption.
split.
solve[intuition].
split.
intros HRO.
rewrite HRO in *;contradiction.
split.
intros HQO.
rewrite HQO in *;contradiction.
split.
intros (Hnew1,Hnew2).  
split.
intros HQl.
generalize (a1_unique Q R l l2 H5 HQl Hnew2 H9 H12); intros H'.
subst l.
solve[intuition].
intros HOl.
generalize (a1_unique N O l l1 H4 Hnew1 HOl H8 H11); intros H'. 
subst l.
solve[intuition].
split.
intros (Hnew1, Hnew2).
split.
intros HRl.
generalize (a1_unique Q R l l2 H5 Hnew2 HRl H9 H12); intros H'.
subst l.
solve[intuition].
intros HOl.
generalize (a1_unique N O l l1 H4 Hnew1 HOl H8 H11); intros H'. 
subst l.
solve[intuition].
split.
intros (Hnew1, Hnew2).
generalize (a1_unique N O l l1 H4 Hnew1 Hnew2 H8 H11); intros H'. 
subst l.
solve[intuition].
split.
intros (Hnew1, Hnew2).
generalize (a1_unique Q R l l2 H5 Hnew1 Hnew2 H9 H12); intros H'.
subst l.
solve[intuition].
split.
intros (Hnew1, Hnew2).
split.
intros HQl.
generalize (a1_unique Q R l l2 H5 HQl Hnew2 H9 H12); intros H'.
subst l.
solve[intuition].
intros HNl.
generalize (a1_unique N O l l1 H4 HNl Hnew1 H8 H11); intros H'. 
subst l.
solve[intuition].
intros (Hnew1, Hnew2).
split.
intros HRl.
generalize (a1_unique Q R l l2 H5 Hnew1 HRl H9 H12); intros H'.
subst l.
solve[intuition].
intros HNl.
generalize (a1_unique N O l l1 H4 HNl Hnew2 H8 H11); intros H'. 
subst l.
solve[intuition].
Qed.

(** case2 with l1 and l2 inverted *)
Lemma case3 : forall M N O P Q R : Point, forall l1 l2 : Line, 
  l1 <> l2 -> 
  ~ M [==] N /\ ~ M [==] O /\ ~ N [==] O /\ Incid M l1 /\ Incid N l1 /\ Incid O l1 ->
  ~ P [==] Q /\ ~ P [==] R /\ ~ Q [==] R /\ Incid P l2 /\ Incid Q l2 /\ Incid R l2 ->
  Incid P l1 -> ~Incid M l2 -> ~Incid N l2 -> ~Incid O l2 -> 
  {A : Point & {B : Point & {C : Point & {D : Point |
          forall l : Line,
            ~ A [==] B /\ ~ A [==] C /\ ~ A [==] D /\ ~ B [==] C /\ ~ B [==] D /\ ~ C [==] D /\
            (Incid A l /\ Incid B l -> ~ Incid C l /\ ~ Incid D l) /\
            (Incid A l /\ Incid C l -> ~ Incid B l /\ ~ Incid D l) /\
            (Incid A l /\ Incid D l -> ~ Incid C l /\ ~ Incid B l) /\
            (Incid C l /\ Incid B l -> ~ Incid A l /\ ~ Incid D l) /\
            (Incid D l /\ Incid B l -> ~ Incid C l /\ ~ Incid A l) /\
            (Incid C l /\ Incid D l -> ~ Incid B l /\ ~ Incid A l)}}}}.
Proof.
intros M N O P Q R l1 l2 H1 H2 H3 HPl1 HMl2 HNl2 HOl2.
eapply case2 with (l1:=l2) (l2:=l1);eauto.
Qed.

(** none of M, N, O, P, Q, and R are at the meeting point of l1 and l2 *)
Lemma case4 : forall M N O P Q R : Point, forall l1 l2 : Line, 
  l1 <> l2 -> 
  ~ M [==] N /\ ~ M [==] O /\ ~ N [==] O /\ Incid M l1 /\ Incid N l1 /\ Incid O l1 ->
  ~ P [==] Q /\ ~ P [==] R /\ ~ Q [==] R /\ Incid P l2 /\ Incid Q l2 /\ Incid R l2 ->
  ~Incid P l1 -> ~Incid Q l1 -> ~Incid R l1 -> ~Incid M l2 -> ~Incid N l2 -> ~Incid O l2 -> 
  {A : Point & {B : Point & {C : Point & {D : Point |
          forall l : Line,
            ~ A [==] B /\ ~ A [==] C /\ ~ A [==] D /\ ~ B [==] C /\ ~ B [==] D /\ ~ C [==] D /\
            (Incid A l /\ Incid B l -> ~ Incid C l /\ ~ Incid D l) /\
            (Incid A l /\ Incid C l -> ~ Incid B l /\ ~ Incid D l) /\
            (Incid A l /\ Incid D l -> ~ Incid C l /\ ~ Incid B l) /\
            (Incid C l /\ Incid B l -> ~ Incid A l /\ ~ Incid D l) /\
            (Incid D l /\ Incid B l -> ~ Incid C l /\ ~ Incid A l) /\
            (Incid C l /\ Incid D l -> ~ Incid B l /\ ~ Incid A l)}}}}.
Proof.
intros M N O P Q R l1 l2 H1 H2 H3 HPl1 HQl1 HRl1 HMl2 HNl2 HOl2.
intuition.
exists N.
exists R.
exists Q.
exists O.
intros l.
split.
intros HNR.
rewrite HNR in *;contradiction.
split.
intros HNQ.
rewrite HNQ in *;contradiction.
split.
assumption.
split.
intros HRQ.
solve[intuition].
split.
intros HRO.
rewrite HRO in *;contradiction.
split.
intros HQO.
rewrite HQO in *;contradiction.
split.
intros (Hnew1,Hnew2).  
split.
intros HQl.
generalize (a1_unique Q R l l2 H5 HQl Hnew2 H9 H12); intros H'.
subst l.
solve[intuition].
intros HOl.
generalize (a1_unique N O l l1 H4 Hnew1 HOl H8 H11); intros H'. 
subst l.
solve[intuition].
split.
intros (Hnew1, Hnew2).
split.
intros HRl.
generalize (a1_unique Q R l l2 H5 Hnew2 HRl H9 H12); intros H'.
subst l.
solve[intuition].
intros HOl.
generalize (a1_unique N O l l1 H4 Hnew1 HOl H8 H11); intros H'. 
subst l.
solve[intuition].
split.
intros (Hnew1, Hnew2).
generalize (a1_unique N O l l1 H4 Hnew1 Hnew2 H8 H11); intros H'. 
subst l.
solve[intuition].
split.
intros (Hnew1, Hnew2).
generalize (a1_unique Q R l l2 H5 Hnew1 Hnew2 H9 H12); intros H'.
subst l.
solve[intuition].
split.
intros (Hnew1, Hnew2).
split.
intros HQl.
generalize (a1_unique Q R l l2 H5 HQl Hnew2 H9 H12); intros H'.
subst l.
solve[intuition].
intros HNl.
generalize (a1_unique N O l l1 H4 HNl Hnew1 H8 H11); intros H'. 
subst l.
solve[intuition].
intros (Hnew1, Hnew2).
split.
intros HRl.
generalize (a1_unique Q R l l2 H5 Hnew1 HRl H9 H12); intros H'.
subst l.
solve[intuition].
intros HNl.
generalize (a1_unique N O l l1 H4 HNl Hnew2 H8 H11); intros H'. 
subst l.
solve[intuition].
Qed.

Definition a3 : {A:Point & {B :Point & {C:Point & {D :Point |
  (forall l :Line, ~ A [==] B /\ ~ A [==] C /\ ~ A [==] D /\ ~ B [==] C /\ ~ B [==] D /\ ~ C [==] D /\ 
    (Incid A l /\ Incid B l -> ~Incid C l /\ ~Incid D l)
    /\ (Incid A l /\ Incid C l -> ~Incid B l /\ ~Incid D l)
    /\  (Incid A l /\ Incid D l -> ~Incid C l /\ ~Incid B l)
    /\  (Incid C l /\ Incid B l -> ~Incid A l /\ ~Incid D l)
    /\ (Incid D l /\ Incid B l -> ~Incid C l /\ ~Incid A l)
    /\  (Incid C l /\ Incid D l -> ~Incid B l /\ ~Incid A l))}}}}.
Proof.
generalize a3_1 a3_2.
intros H1 H2.
elim H2; clear H2; intros l1 Hl1.
elim Hl1; clear Hl1; intros l2 HdistL.
generalize (H1 l1); intros Hl1.
generalize (H1 l2); intros Hl2.
clear H1.
elim Hl1; clear Hl1; intros A1 HA1.
elim HA1; clear HA1; intros B1 HB1.
elim HB1; clear HB1; intros C1 H1.
elim Hl2; clear Hl2; intros A2 HA2.
elim HA2; clear HA2; intros B2 HB2.
elim HB2; clear HB2; intros C2 H2.
elim (incid_dec A1 l2).
elim (incid_dec A2 l1).
intros Ha Hb.
eapply case1;eauto.
intros Ha Hb.
elim (incid_dec B1 l2).
intros Hc.
assert (~Incid B1 l2).
intuition.
generalize (a2_unique l1 l2 A1 B1 HdistL H6 Hb H8 Hc); intros H'.
rewrite H' in *.
solve[intuition].
solve[intuition].
intros Hc.
elim (incid_dec C1 l2).
intros Hd.
assert (~Incid C1 l2).
intuition.
generalize (a2_unique l1 l2 A1 C1 HdistL H6 Hb H11 Hd); intros H'.
rewrite H' in *.
solve[intuition].
solve[intuition].
intros Hd.
elim (incid_dec B2 l1).
intros H.
eapply case1 with (M:=A1) (N:=B1) (O:=C1) (P:=B2) (Q:=A2) (R:=C2);eauto;intuition.
intros He.
elim (incid_dec C2 l1).
intros H.
eapply case1 with (M:=A1) (N:=B1) (O:=C1) (P:=C2) (Q:=A2) (R:=B2);eauto;intuition.
intros Hf.
eapply case2;eauto.
intros Ha.
elim (incid_dec B1 l2).
intros Hb.
elim (incid_dec A2 l1).
intros Hc.
eapply case1 with (M:=B1) (N:=A1) (O:=C1) (P:=A2) (Q:=B2) (R:=C2);eauto;intuition.
intros Hc.
elim (incid_dec B2 l1).
intros Hd.
eapply case1 with (M:=B1) (N:=A1) (O:=C1) (P:=B2) (Q:=A2) (R:=C2);eauto;intuition.
intros He.
elim (incid_dec C2 l1).
intros Hf.
eapply case1 with (M:=B1) (N:=A1) (O:=C1) (P:=C2) (Q:=A2) (R:=B2);eauto;intuition.
intros Hf.
eapply case2 with (M:=B1) (N:=A1) (O:=C1) (P:=A2) (Q:=B2) (R:=C2);eauto;intuition.
intros Hb.
elim (incid_dec C1 l2).
intros Hc.
elim (incid_dec A2 l1).
intros Hd.
eapply case1 with (M:=C1) (N:=A1) (O:=B1) (P:=A2) (Q:=B2) (R:=C2);eauto;intuition.
intros Hd.
elim (incid_dec B2 l1).
intros He.
eapply case1 with (M:=C1) (N:=A1) (O:=B1) (P:=B2) (Q:=A2) (R:=C2);eauto;intuition.
intros He.
elim (incid_dec C2 l1).
intros Hf.
eapply case1 with (M:=C1) (N:=A1) (O:=B1) (P:=C2) (Q:=A2) (R:=B2);eauto;intuition.
intros Hf.
eapply case2 with (M:=C1) (N:=A1) (O:=B1) (P:=A2) (Q:=B2) (R:=C2);eauto;intuition.
intros Hc.
elim (incid_dec A2 l1).
intros Hd.
eapply case3 with (M:=A1) (N:=B1) (O:=C1) (P:=A2) (Q:=B2) (R:=C2);eauto;intuition.
intros Hd.
elim (incid_dec B2 l1).
intros He.
eapply case3 with (M:=A1) (N:=B1) (O:=C1) (P:=B2) (Q:=A2) (R:=C2);eauto;intuition.
intros He.
elim (incid_dec C2 l1).
intros Hf.
eapply case3 with (M:=A1) (N:=B1) (O:=C1) (P:=C2) (Q:=A2) (R:=B2);eauto;intuition.
intros Hf.
eapply case4;eauto.
Qed.

End s_ProjectivePlane'ToProjectivePlane.