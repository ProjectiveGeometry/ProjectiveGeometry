Require Export ProjectiveGeometry.Dev.p_equiv_c2p.

(*****************************************************************************)
(** Collinear **)


Section s_pEquivCol_1.

Context `{PSLEU : ProjectiveStructureLEU}.
Context `{EP : EqDecidability Point}.
Context `{OP : OrderedType Point}.

Global Instance incid_morph : Proper (eq ==> Logic.eq ==> impl) Incid.
repeat red.
intros.
rewrite <-H.
rewrite <-H0.
assumption.
Qed.

(*** Definition dist3 ***)
Definition dist3 (a b c : Point) := 
 ~ a [==] b /\ ~ a [==] c /\ ~ a [==] c.

(*** Definition collinear ***)
Definition collinear (a b c : Point) : bool :=
if (eq_dec_u a b) 
   then true 
   else if incid_dec c (proj1_sig (a1_exist a b)) then true else false.

End s_pEquivCol_1.


Ltac my_col :=
  unfold collinear;intuition
  repeat match goal with
  |[H : _ |- _] => progress intros
  |[H : _ |- _] => progress intro
  |[H : _ |- _] => progress intuition
  (*|[H : _ |- _] => progress my_subst*)
  |[H : (if incid_dec _ (proj1_sig ?X) then _ else _) = _ |- _] => destruct X in H; simpl in H
  |[H : _ = (if incid_dec _ (proj1_sig ?X) then _ else _) |- _] => destruct X in H; simpl in H
  |[H : _ |- (if incid_dec _ (proj1_sig ?X) then _ else _) = _ ] => destruct X; simpl
  |[H : _ |- _ = (if incid_dec _ (proj1_sig ?X) then _ else _)] => destruct X; simpl
  |[H : (if ?X then _ else _) = _ |- _] => destruct X in H; simpl in H
  |[H : _ = (if ?X then _ else _) |- _] => destruct X in H; simpl in H
  |[H : _ |- (if ?X then _ else _) = _] => destruct X
  |[H : _ |- _ = (if ?X then _ else _)] => destruct X
  |[H : ?X[==]?X -> False |- _] => apply False_ind;apply H; intuition
  |[H : _ \/ _ |- _] => destruct H
  |[H : _ |- _ \/ _] => apply uniqueness
  |[H : false = true |- _] => inversion H
  end.


Section s_pEquivCol_2.

Context `{PSLEU : ProjectiveStructureLEU}.
Context `{EP : EqDecidability Point}.
Context `{OP : OrderedType Point}.

Lemma col_1 : forall a b, collinear a a b = true.
Proof.
my_col.
Qed.

Lemma col_2 : forall a b, collinear a b b = true.
Proof.
my_col.
Qed.

Lemma col_exchange : forall a b c, collinear a b c = collinear b a c.
Proof.
my_col;my_subst;my_col;
[assert(HH : a[==]b \/ x = x0)|];
my_col;my_subst;my_col;
assert(HH : a[==]b \/ x = x0);
my_col;my_subst;my_col.
Qed.

Lemma col_exchange2 : forall a b c, collinear a b c = collinear a c b.
Proof.
my_col;my_subst;my_col;
[assert( HH : a[==]c \/ x = x0)|];
my_col;my_subst;my_col;my_subst;my_col;
assert( HH : a[==]b \/ x = x0);
my_col;my_col;my_subst;my_col.
Qed.

Lemma col_shift : forall a b c, collinear a b c = collinear b c a.
Proof.
my_col;my_subst;my_col;
[assert( HH : b[==]c \/ x = x0)|];
my_col;my_subst;my_col;my_subst;my_col;
assert( HH : a[==]b \/ x = x0);
my_col;my_subst;my_col.
Qed.

Lemma col_trans_aux : forall a b c, forall x, ~a[==]b -> collinear a b c = true -> Incid a x -> Incid b x -> Incid c x.
Proof.
my_col;
assert( HH0 : a[==]b \/ x = x0);
my_col;my_subst;my_col.
Qed.

Lemma col_trans : forall a b c d, ~a[==]b -> collinear a b c = true -> collinear a b d = true -> collinear a c d = true.
Proof.
my_col;
assert(HH : a[==]b \/ x = x0);
my_col;my_subst;
assert(HH : a[==]c \/ x0 = x1);
my_col;my_subst;my_col.
Qed.

Lemma col_trans_bis : forall a b c d, ~a[==]b -> collinear a b c = true -> collinear a b d = true -> collinear b c d = true.
Proof.
my_col;
assert(HH : a[==]b \/ x = x0);
my_col;my_subst;
assert(HH : b[==]c \/ x0 = x1);
my_col;my_subst;my_col.
Qed.

Global Instance collinear_morph : Proper (eq ==> eq ==> eq ==> Logic.eq) collinear.
Proof.
repeat red.
my_col;my_subst; my_col;
assert(HH0 : y[==]y0 \/ x2 = x3);
my_col;my_subst;my_col.
Qed.

End s_pEquivCol_2.


Ltac my_col2 :=
  repeat match goal with
  |[H : collinear ?X ?Y ?Z = true |- collinear ?X ?Y ?Z = true] => solve[intuition]
  |[H : collinear ?X ?Z ?Y = true |- collinear ?X ?Y ?Z = true] => rewrite col_exchange2 in H;solve[intuition]
  |[H : collinear ?Z ?X ?Y = true |- collinear ?X ?Y ?Z = true] => rewrite col_exchange in H;rewrite col_exchange2 in H;solve[intuition]
  |[H : collinear ?Z ?Y ?X = true |- collinear ?X ?Y ?Z = true] => rewrite col_exchange2 in H;rewrite col_exchange in H;rewrite col_exchange2 in H;solve[intuition]
  |[H : collinear ?Y ?X ?Z = true |- collinear ?X ?Y ?Z = true] => rewrite col_exchange in H;solve[intuition]
  |[H : collinear ?Y ?Z ?X = true |- collinear ?X ?Y ?Z = true] => rewrite col_exchange2 in H;rewrite col_exchange in H;solve[intuition]
end.