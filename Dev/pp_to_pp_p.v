Require Export ProjectiveGeometry.Dev.basic_plane_facts.

Section s_ProjectivePlaneToProjectivePlane'.

Context `{PP : ProjectivePlane}.
Context `{EP : EqDecidability Point}.

(*
Cas 1 : 2 points sont sur L, 2 points n'y sont pas. Dans ce cas, on construit l'intersection de la ligne engendree
par les 2 points qui ne sont pas sur L. Cela donne 3 points alignes sur L. Ce point d'intersection ne peut pas etre
confondu avec un des 2 points deja  presents sur L, sinon on aura trois points alignes, ce qui est impossible par hypothese.
*)

Lemma cas1 : forall (A B C D : Point)(l:Line),
  ~ A [==] B /\ ~ A [==] C /\ ~ A [==] D /\ ~ B [==] C /\ ~ B [==] D /\ ~ C [==] D /\ 
  Incid A l /\ Incid B l /\ ~Incid C l /\ ~Incid D l  -> 
  (forall m : Line,
       ~ A [==] B /\ ~ A [==] C /\ ~ A [==] D /\ ~ B [==] C /\ ~ B [==] D /\ ~ C [==] D /\
       (Incid A m /\ Incid B m -> ~ Incid C m /\ ~ Incid D m) /\
       (Incid A m /\ Incid C m -> ~ Incid B m /\ ~ Incid D m) /\
       (Incid A m /\ Incid D m -> ~ Incid C m /\ ~ Incid B m) /\
       (Incid C m /\ Incid B m -> ~ Incid A m /\ ~ Incid D m) /\
       (Incid D m /\ Incid B m -> ~ Incid C m /\ ~ Incid A m) /\
       (Incid C m /\ Incid D m -> ~ Incid B m /\ ~ Incid A m)) -> 
  {E : Point | ~ A [==] B /\ ~ A [==] E /\ ~ B [==] E /\ Incid E l}.
Proof.
intros A B C D l H HIncid.
elim (a1_exist C D).
intros l1 Hl1.
assert(C <> D) by solve[intuition].

elim (a2_exist l l1).
intros E HE.
exists E.
my_split.
intuition.
rewrite H14 in *.
generalize (HIncid l1); intros H'.
solve[intuition].

rewrite H14 in *.
generalize (HIncid l1); intros H'.
solve[intuition].
Qed.

(* Cas 2 : 1 point sur L, 3 points n'y sont pas. Il faut construire 2 points de L 
   par intersection avec des lignes engendrees par les points n'appartenant pas a  L. 
   Il faut faire des cas sur les points choisis et les risques d'alignement. 
*)

Lemma cas2:forall (A B C D : Point)(l:Line),
  ~ A [==] B /\ ~ A [==] C /\ ~ A [==] D /\ ~ B [==] C /\ ~ B [==] D /\ ~ C [==] D /\ 
  Incid A l /\ ~Incid B l /\ ~Incid C l /\ ~Incid D l ->
  (forall m : Line,
       ~ A [==] B /\ ~ A [==] C /\ ~ A [==] D /\ ~ B [==] C /\ ~ B [==] D /\ ~ C [==] D /\ 
       (Incid A m /\ Incid B m -> ~ Incid C m /\ ~ Incid D m) /\
       (Incid A m /\ Incid C m -> ~ Incid B m /\ ~ Incid D m) /\
       (Incid A m /\ Incid D m -> ~ Incid C m /\ ~ Incid B m) /\
       (Incid C m /\ Incid B m -> ~ Incid A m /\ ~ Incid D m) /\
       (Incid D m /\ Incid B m -> ~ Incid C m /\ ~ Incid A m) /\
       (Incid C m /\ Incid D m -> ~ Incid B m /\ ~ Incid A m)) ->
  {E:Point & {F:Point | ~ A [==] E /\ ~ A [==] F /\ ~ E [==] F /\ Incid E l /\ Incid F l}}.
Proof.
intros A B C D l H Hincid.
elim (a1_exist B C).
intros d1 Hd1.
assert (B<>C).
solve[intuition].
elim (a2_exist l d1).
intros IBC HIBC.
elim (incid_dec A d1).
intros HAd1.

elim (Hincid d1).
solve[intuition].
intros HAd1.

elim (a1_exist B D).
intros d2 Hd2.
assert (B<>D) by solve[intuition].
elim (a2_exist l d2).
intros IBD HIBD.
elim (incid_dec A d2).
intros HAd2.
elim (Hincid d2).
solve[intuition].
intros HAd2.
exists IBC. 
exists IBD.
split.
intros HAIBC.
my_split;rewrite HAIBC in *;contradiction.
split.
intros HAIBD.
my_split;rewrite HAIBD in *;contradiction.
assert (d1 <> d2).
intros Hd1d2.
subst.
elim (Hincid d2); solve[intuition].

elim Hd1; intros Hd1B Hd1C.
elim Hd2; intros Hd2B Hd2D.
elim HIBC; intros HIBCl HIBCd1.
elim (incid_dec IBC d2).
intros HIBCd2.

generalize (a2_unique d1 d2 B IBC H2 Hd1B Hd2B HIBCd1 HIBCd2).
intros HBIBC.
my_split;rewrite HBIBC in *;contradiction.

intros HIBDd2.
split.
intro.
my_split;rewrite H3 in *;contradiction.
my_split;solve[intuition].
Qed.

(* Cas 3 : 0 point sur L, 4 points n'y sont pas. On doit mener le meme raisonnement 
   que pour le cas 2, mais avec un plus grand nombre de sous-cas. 
*)

Lemma cas3:forall (A B C D : Point)(l:Line),
  ~ A [==] B /\ ~ A [==] C /\ ~ A [==] D /\ ~ B [==] C /\ ~ B [==] D /\ ~ C [==] D /\ 
  ~Incid A l /\~Incid B l /\ ~Incid C l /\ ~Incid D l ->
  (forall m : Line,
    ~ A [==] B /\ ~ A [==] C /\ ~ A [==] D /\ ~ B [==] C /\ ~ B [==] D /\ ~ C [==] D /\
    (Incid A m /\ Incid B m -> ~ Incid C m /\ ~ Incid D m) /\
    (Incid A m /\ Incid C m -> ~ Incid B m /\ ~ Incid D m) /\
    (Incid A m /\ Incid D m -> ~ Incid C m /\ ~ Incid B m) /\
    (Incid C m /\ Incid B m -> ~ Incid A m /\ ~ Incid D m) /\
    (Incid D m /\ Incid B m -> ~ Incid C m /\ ~ Incid A m) /\
    (Incid C m /\ Incid D m -> ~ Incid B m /\ ~ Incid A m)) ->
  {E:Point & {F:Point & {G:Point |
    ~ E [==] F /\ ~ E [==] G /\ ~ F [==] G /\ Incid E l /\ Incid F l /\ Incid G l}}}.
Proof.
intros A B C D l H Hincid.
elim(a1_exist A B).
intros l1 Hl1.

elim(a1_exist A C).
intros l2 Hl2.

elim(a1_exist A D).
intros l3 Hl3.

elim (a2_exist l l1).
intros I HI.
elim (a2_exist l l2).
intros J HJ.
elim (a2_exist l l3).
intros K HK.

elim HI; intros HIl HIl1.
elim HJ; intros HJl HJl2.
(* 1 *)
elim (incid_dec I l2).
intros HIl2.
assert (Hl1l2 : l<>l2).
intros Hl1l2.
subst.
elim (Hincid l2); tauto.
generalize (a2_unique l l2 I J Hl1l2 HIl HIl2 HJl HJl2).
intros HIJ.
rewrite HIJ in *.
assert (~ A [==] J).
intro.
my_split;rewrite H0 in *;contradiction.
elim Hl1 ; intros HAl1 HBl1.
elim Hl2; intros HAl2 HCl2.
generalize (a1_unique A J l1 l2 H0 HAl1 HIl1 HAl2 HIl2).
intros H'; subst.
elim (Hincid l2); tauto.
(* 1 *)
intros HIl2.
elim (incid_dec I l3).
intros HIl3.
assert (Hl1l3 : l<>l3).
intros Hl1l3.
subst.
elim (Hincid l3);solve[intuition].
elim HK; intros HKl HKl3.
generalize (a2_unique l l3 I K Hl1l3 HIl HIl3 HKl HKl3).
intros HIK.
rewrite HIK in *.
assert (~ A [==] K).
intro.
my_split;rewrite H0 in *;contradiction.
elim Hl1 ; intros HAl1 HBl1.
elim Hl2; intros HAl2 HCl2.
elim Hl3; intros HAl3 HDl3.
generalize (a1_unique A K l1 l3 H0 HAl1 HIl1 HAl3 HIl3).
intros H'; subst.
elim (Hincid l3); solve[intuition].
intros HIl3.

elim (incid_dec J l1).
intros HJl1.
assert (Hll1 : l<>l1).
intros Hll1.
subst.
elim (Hincid l1); tauto.
generalize (a2_unique l l1 I J Hll1 HIl HIl1 HJl HJl1).
intros HIJ.
my_split;rewrite HIJ in *;contradiction.
intros HJl1.
elim (incid_dec K l2).
intros HKl2.
assert (Hll2 : l<>l2).
intros Hll2.
subst.
elim (Hincid l3);solve[intuition].
elim HK; intros HKl HKl3.
generalize (a2_unique l l2 J K Hll2 HJl HJl2 HKl HKl2).
intros HJK.
rewrite HJK in *.
assert (~ A [==] K).
intro.
my_split;rewrite H0 in *;contradiction.
elim Hl1 ; intros HAl1 HBl1.
elim Hl2; intros HAl2 HCl2.
elim Hl3; intros HAl3 HDl3.
generalize (a1_unique A K l2 l3 H0 HAl2 HJl2 HAl3 HKl3).
intros H'; subst.
elim (Hincid l3); tauto.
intros HKl2.
exists I.
exists J.
exists K.
split.
intro.
my_split;rewrite H0 in *;contradiction.
split.
intro.
my_split;rewrite H0 in *;contradiction.
split.
intro.
my_split;rewrite H0 in *;contradiction.
my_split;solve[intuition].
Qed.


(* A3s :  each line has at least three points and there are at least two lines *)

Definition a3_1 : 
  (forall l:Line,{A:Point & {B:Point & {C:Point | ( ~ A [==] B /\ ~ A [==] C /\ ~ B [==] C /\Incid A l /\Incid B l /\ Incid C l)}}}).
Proof.
generalize a3.
intros H.
intros l.
elim H; clear H; intros A HA.
elim HA; clear HA; intros B HB.
elim HB; clear HB; intros C HC.
elim HC; clear HC; intros D HD.
elim (HD l).
intros Hdist Hincid.
elim (incid_dec A l).
intros HAl.
elim (incid_dec B l).
intros HBl.
elim (incid_dec C l).
intros HCl.
solve[intuition].
intros HCl.
elim (incid_dec D l).
intros HDl.
solve[intuition].
intros HDl.
assert ( H' : ~ A [==] B /\ ~ A [==] C /\ ~ A [==] D /\ ~ B [==] C /\ ~ B [==] D /\ ~ C [==] D 
/\ Incid A l /\ Incid B l /\ ~ Incid C l /\ ~ Incid D l).
solve[intuition].

elim (cas1 A B C D l H' HD).
intros E HE.
exists A.
exists B.
exists E.
solve[intuition].

intros HBl.
elim (incid_dec C l).
intros HCl.
elim (incid_dec D l).
intros HDl.
assert ( H' : ~ A [==] B /\ ~ A [==] C /\ ~ A [==] D /\ ~ B [==] C /\ ~ B [==] D /\ ~ C [==] D 
/\ Incid A l /\ ~ Incid B l /\ ~ Incid C l /\ ~ Incid D l).
solve[intuition].
elim (cas2 A B C D l H' HD).
intros E HE.
elim HE; intros F HF.
exists A.
exists E.
exists F.
solve[intuition].
intros HDl.
assert (H' : ~ A [==] C /\ ~ A [==] B /\ ~ A [==] D /\ ~ C [==] B /\ ~ C [==] D /\ ~ B [==] D
 /\ Incid A l /\ Incid C l /\ ~ Incid B l /\ ~ Incid D l).
solve[intuition].
assert (HD' : forall m : Line,
  ~ A [==] C /\ ~ A [==] B /\ ~ A [==] D /\ ~ C [==] B /\ ~ C [==] D /\ ~ B [==] D /\
  (Incid A m /\ Incid C m -> ~ Incid B m /\ ~ Incid D m) /\
  (Incid A m /\ Incid B m -> ~ Incid C m /\ ~ Incid D m) /\
  (Incid A m /\ Incid D m -> ~ Incid B m /\ ~ Incid C m) /\
  (Incid B m /\ Incid C m -> ~ Incid A m /\ ~ Incid D m) /\
  (Incid D m /\ Incid C m -> ~ Incid B m /\ ~ Incid A m) /\
  (Incid B m /\ Incid D m -> ~ Incid C m /\ ~ Incid A m)).
intros m; elim (HD m); clear HD.
solve[intuition].
generalize (cas1 A C B D l H' HD').
intros H'' ; elim H''; intros E HE.
exists A.
exists C.
exists E.
solve[intuition].
intros HCl.
elim (incid_dec D l).
intros HDl.
assert (H' : ~ A [==] D /\ ~ A [==] B /\ ~ A [==] C /\ ~ D [==] B /\ ~ D [==] C /\ ~ B [==] C 
/\ Incid A l /\ Incid D l /\ ~ Incid B l /\ ~ Incid C l).
solve[intuition].
assert (HD' : (forall m : Line,
     ~ A [==] D /\ ~ A [==] B /\ ~ A [==] C /\ ~ D [==] B /\ ~ D [==] C /\ ~ B [==] C /\
     (Incid A m /\ Incid D m -> ~ Incid B m /\ ~ Incid C m) /\
     (Incid A m /\ Incid B m -> ~ Incid D m /\ ~ Incid C m) /\
     (Incid A m /\ Incid C m -> ~ Incid B m /\ ~ Incid D m) /\
     (Incid B m /\ Incid D m -> ~ Incid A m /\ ~ Incid C m) /\
     (Incid C m /\ Incid D m -> ~ Incid B m /\ ~ Incid A m) /\
     (Incid B m /\ Incid C m -> ~ Incid D m /\ ~ Incid A m))).
intros m; elim (HD m); clear HD.
solve[intuition].
elim (cas1 A D B C l H' HD').
intros E HE.
exists A.
exists D.
exists E.
solve[intuition].
intros HDl.
assert ( H' : ~ A [==] B /\ ~ A [==] C /\ ~ A [==] D /\ ~ B [==] C /\ ~ B [==] D /\ ~ C [==] D /\ 
Incid A l /\ ~ Incid B l /\ ~ Incid C l /\ ~ Incid D l).
intuition.
elim (cas2 A B C D l H' HD).
intros E HE.
elim HE; intros F HF.
exists A.
exists E.
exists F.
solve[intuition].
intros HAl.
elim (incid_dec B l).
intros HBl.
elim (incid_dec C l).
intros HCl.
elim (incid_dec D l).
intros HDl.
solve[intuition].
intros HDl.
assert (H' : ~ B [==] C /\ ~ B [==] A /\ ~ B [==] D /\ ~ C [==] A /\ ~ C [==] D /\ ~ A [==] D /\ 
Incid B l /\ Incid C l /\ ~ Incid A l /\ ~ Incid D l).
solve[intuition].
assert (HD' : (forall m : Line,
     ~ B [==] C /\ ~ B [==] A /\ ~ B [==] D /\ ~ C [==] A /\ ~ C [==] D /\ ~ A [==] D /\
     (Incid B m /\ Incid C m -> ~ Incid A m /\ ~ Incid D m) /\
     (Incid B m /\ Incid A m -> ~ Incid C m /\ ~ Incid D m) /\
     (Incid B m /\ Incid D m -> ~ Incid A m /\ ~ Incid C m) /\
     (Incid A m /\ Incid C m -> ~ Incid B m /\ ~ Incid D m) /\
     (Incid D m /\ Incid C m -> ~ Incid A m /\ ~ Incid B m) /\
     (Incid A m /\ Incid D m -> ~ Incid C m /\ ~ Incid B m))).
intros m; elim (HD m); clear HD.
solve[intuition].
elim (cas1 B C A D l H' HD').
intros E HE.
exists B.
exists C.
exists E.
solve[intuition].
intros HCl.
elim (incid_dec D l).
intros HDl.
assert (H' : ~ B [==] D /\ ~ B [==] A /\ ~ B [==] C /\ ~ D [==] A /\ ~ D [==] C /\ ~ A [==] C 
/\ Incid B l /\ Incid D l /\ ~ Incid A l /\ ~ Incid C l).
solve[intuition].
assert (HD' : (forall m : Line,
     ~ B [==] D /\ ~ B [==] A /\ ~ B [==] C /\ ~ D [==] A /\ ~ D [==] C /\ ~ A [==] C /\
     (Incid B m /\ Incid D m -> ~ Incid A m /\ ~ Incid C m) /\
     (Incid B m /\ Incid A m -> ~ Incid D m /\ ~ Incid C m) /\
     (Incid B m /\ Incid C m -> ~ Incid A m /\ ~ Incid D m) /\
     (Incid A m /\ Incid D m -> ~ Incid B m /\ ~ Incid C m) /\
     (Incid C m /\ Incid D m -> ~ Incid A m /\ ~ Incid B m) /\
     (Incid A m /\ Incid C m -> ~ Incid D m /\ ~ Incid B m))).
intros m; elim (HD m); clear HD.
solve[intuition].
elim (cas1 B D A C l H' HD').
intros E HE.
exists B.
exists D.
exists E.
solve[intuition].
intros HDl.
assert (H' : ~ B [==] A /\ ~ B [==] C /\ ~ B [==] D /\ ~ A [==] C /\ ~ A [==] D /\ ~ C [==] D /\
 Incid B l /\ ~ Incid A l /\ ~ Incid C l /\ ~ Incid D l).
solve[intuition].
assert (HD'  :  (forall m : Line,
     ~ B [==] A /\ ~ B [==] C /\ ~ B [==] D /\ ~ A [==] C /\ ~ A [==] D /\ ~ C [==] D /\
     (Incid B m /\ Incid A m -> ~ Incid C m /\ ~ Incid D m) /\
     (Incid B m /\ Incid C m -> ~ Incid A m /\ ~ Incid D m) /\
     (Incid B m /\ Incid D m -> ~ Incid C m /\ ~ Incid A m) /\
     (Incid C m /\ Incid A m -> ~ Incid B m /\ ~ Incid D m) /\
     (Incid D m /\ Incid A m -> ~ Incid C m /\ ~ Incid B m) /\
     (Incid C m /\ Incid D m -> ~ Incid A m /\ ~ Incid B m))).
intros m; elim (HD m); clear HD.
solve[intuition].
elim (cas2 B A C D l H' HD').
intros E HE.
elim HE; intros F HF.
exists B.
exists E.
exists F.
solve[intuition].
intros HBl.
elim (incid_dec C l).
intros HCl.
elim (incid_dec D l).
intros HDl.
assert (H' : ~ C [==] D /\ ~ C [==] A /\ ~ C [==] B /\ ~ D [==] A /\ ~ D [==] B /\ ~ A [==] B /\ 
Incid C l /\ Incid D l /\ ~ Incid A l /\ ~ Incid B l).
solve[intuition].
assert (HD' : (forall m : Line,
     ~ C [==] D /\ ~ C [==] A /\ ~ C [==] B /\ ~ D [==] A /\ ~ D [==] B /\ ~ A [==] B /\
     (Incid C m /\ Incid D m -> ~ Incid A m /\ ~ Incid B m) /\
     (Incid C m /\ Incid A m -> ~ Incid D m /\ ~ Incid B m) /\
     (Incid C m /\ Incid B m -> ~ Incid A m /\ ~ Incid D m) /\
     (Incid A m /\ Incid D m -> ~ Incid C m /\ ~ Incid B m) /\
     (Incid B m /\ Incid D m -> ~ Incid A m /\ ~ Incid C m) /\
     (Incid A m /\ Incid B m -> ~ Incid D m /\ ~ Incid C m))).
intros m; elim (HD m); clear HD.
solve[intuition].
elim (cas1 C D A B l H' HD').
intros E HE.
exists C.
exists D.
exists E.
solve[intuition].
intros HDl.
assert (H' : ~ C [==] A /\ ~ C [==] B /\ ~ C [==] D /\ ~ A [==] B /\ ~ A [==] D /\ ~ B [==] D /\ 
Incid C l /\ ~ Incid A l /\ ~ Incid B l /\ ~ Incid D l).
solve[intuition].
assert (HD' : (forall m : Line,
     ~ C [==] A /\ ~ C [==] B /\ ~ C [==] D /\ ~ A [==] B /\ ~ A [==] D /\ ~ B [==] D /\
     (Incid C m /\ Incid A m -> ~ Incid B m /\ ~ Incid D m) /\
     (Incid C m /\ Incid B m -> ~ Incid A m /\ ~ Incid D m) /\
     (Incid C m /\ Incid D m -> ~ Incid B m /\ ~ Incid A m) /\
     (Incid B m /\ Incid A m -> ~ Incid C m /\ ~ Incid D m) /\
     (Incid D m /\ Incid A m -> ~ Incid B m /\ ~ Incid C m) /\
     (Incid B m /\ Incid D m -> ~ Incid A m /\ ~ Incid C m))).
intros m; elim (HD m); clear HD.
solve[intuition].
elim (cas2 C A B D l H' HD').
intros E HE.
elim HE; intros F HF.
exists C.
exists E.
exists F.
solve[intuition].
intros HCl.
elim (incid_dec D l).
intros HDl.
assert (H' : ~ D [==] A /\ ~ D [==] B /\ ~ D [==] C /\ ~ A [==] B /\ ~ A [==] C /\ ~ B [==] C /\ 
Incid D l /\ ~ Incid A l /\ ~ Incid B l /\ ~ Incid C l).
solve[intuition].
assert (HD' : (forall m : Line,
     ~ D [==] A /\ ~ D [==] B /\ ~ D [==] C /\ ~ A [==] B /\ ~ A [==] C /\ ~ B [==] C /\
     (Incid D m /\ Incid A m -> ~ Incid B m /\ ~ Incid C m) /\
     (Incid D m /\ Incid B m -> ~ Incid A m /\ ~ Incid C m) /\
     (Incid D m /\ Incid C m -> ~ Incid B m /\ ~ Incid A m) /\
     (Incid B m /\ Incid A m -> ~ Incid D m /\ ~ Incid C m) /\
     (Incid C m /\ Incid A m -> ~ Incid B m /\ ~ Incid D m) /\
     (Incid B m /\ Incid C m -> ~ Incid A m /\ ~ Incid D m))).
intros m; elim (HD m); clear HD.
solve[intuition].
elim (cas2 D A B C l H' HD').
intros E HE.
elim HE; intros F HF.
exists D.
exists E.
exists F.
solve[intuition].
intros HDl.
assert (H' : ~ A [==] B /\ ~ A [==] C /\ ~ A [==] D /\ ~ B [==] C /\ ~ B [==] D /\ ~ C [==] D  /\ 
~ Incid A l /\ ~ Incid B l /\ ~ Incid C l /\ ~ Incid D l).
solve[intuition].
elim (cas3 A B C D l H' HD).
intros E HE.
elim HE; intros F HF.
elim HF; intros G HG.
exists E.
exists F.
exists G.
solve[intuition].
Qed.

Definition a3_2 : {l1:Line & {l2:Line | l1 <> l2}}.
Proof.
generalize a3.
intros H.
elim H;clear H.
intros A.
intros Ha.
elim Ha;clear Ha.
intros B.
intros Hb.
elim Hb ; clear Hb.
intros C.
intros Hc.
elim Hc ;clear Hc.
intros D.
intros Hd.
generalize (a1_exist A B ).
intros Hex.
elim Hex.
intros L.
intros H1.
assert (A <> B).
elim (Hd L).
intros.
solve[intuition].

generalize (a1_exist C D).
intros Hex2.
elim Hex2.
intros L2.
intros H2.
assert( C <> D).
elim (Hd L2).
intros.
solve[intuition].
exists L.
exists L2.

intro HLL2.
subst L2.
elim (Hd L).
solve[intuition].
Qed.

End s_ProjectivePlaneToProjectivePlane'.