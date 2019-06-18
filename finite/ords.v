Require Import ssreflect ssrfun ssrbool.

(** some simple lemmas about bool *)

Lemma degen_bool : forall P, is_true false -> P.
Proof.
  intros; discriminate.
Qed.

Lemma ab_bool_lr : forall a b, a && b -> a /\ b.
Proof.
  intros a b; case a; case b; intros H; inversion H; split; assumption.
Qed.

Lemma ab_bool : forall a b, a && b <-> a /\ b.
Proof.
  intros a b; split.
  apply ab_bool_lr.
  case a;case b; intros (ha,hb); solve [inversion ha | inversion hb | reflexivity].
Qed.

Lemma circ2 : forall a b, a&&b -> b&&a.
Proof.
  intros a b; destruct a; destruct b; intros H;inversion H; assumption.
Qed.

Lemma circ3: forall A B C: bool, B && C && A -> A && B &&C.
Proof.
  intros a b c; case a; case b; case c; intros; assumption.
Qed.

Lemma circ6: forall A B C D E F : bool,
       B && C && D && E &&F && A -> A && B && C && D && E && F.
Proof.
  intros a b c d e f; case a; case b; case c; case d; case e; case f; intros; assumption.
Qed.

Lemma bool6 : forall a b c d e f, a && b && c && d && e && f -> a && e && d && c && b && f.
Proof.
  intros a b c d e f; case a; case b; case c; case d; case e; case f; intros; assumption.
Qed.

Lemma comm12L: forall A B C:bool, B && A && C -> A && B && C.
   Proof.
     intros a b c; case a; case b; case c; intros; assumption.
   Qed.
   
Lemma comm12P: forall A B C D E F :bool,
       B && A && C && D &&E && F -> A && B && C && D && E && F.
Proof.
  intros a b c d e f; case a; case b; case c; case d; case e; case f; intros; assumption.
Qed.
 


(* Local Variables: *)
(* coq-prog-name: "/Users/magaud/.opam/4.06.0/bin/coqtop" *)
(* coq-load-path: (("." "Top") ) *)
(* suffixes: .v *)
(* End: *)
