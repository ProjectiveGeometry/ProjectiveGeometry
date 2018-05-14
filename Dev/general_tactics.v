Require Export ProjectiveGeometry.Dev.projective_axioms.

Ltac new_subst := 
  subst;repeat (match goal with  H:?X [==] ?Y  |- _ => (rewrite H in *; clear H) end).

Ltac my_split := 
  repeat match goal with [H : _ /\ _ |- _] => destruct H end.

Ltac fo := match goal with P:?Point |- _ => (exists P; solve [intuition]) 
end.

Ltac Apply_unicity := match goal with
| H1: ~?A [==] ?B, H2: ?Incid ?A ?l, H3: ?Incid ?B ?l, H4 : ?Incid ?A ?m, H5: ?Incid ?B ?m |- _ =>
let id:= fresh in assert (id: l=m); [try apply (a1_unique A B l m H1 H2 H3 H4 H5) | subst l]
| H1: ?l <> ?m, H2: ?Incid ?A ?l, H3: ?Incid ?A ?m, H4 : ?Incid ?B ?l, H5: ?Incid ?B ?m |- _ =>
let id:= fresh in assert (id: A[==]B); [try apply (a2_unique l m A B H1 H2 H3 H4 H5) | rewrite id in *; clear id]
end.

Ltac Apply_uniqueness := match goal with
| H : ~?A [==] ?B, H1 : ?Incid ?A ?l, H2: ?Incid ?B ?l, H3 : ?Incid ?A ?m, H4: ?Incid ?B ?m |- _ =>
  let id := fresh in assert(id := uniqueness A B l m H1 H2 H3 H4)
| H : ?l <> ?m, H1 : ?Incid ?A ?l, H2: ?Incid ?B ?l, H3 : ?Incid ?A ?m, H4: ?Incid ?B ?m |- _ =>
  let id := fresh in assert(id := uniqueness A B l m H1 H2 H3 H4)
end.

Ltac CleanDuplicatedHypsModulo :=
  repeat match goal with
  | H:((?A [==] ?A) \/ (?C [==] ?D)) |- _ => clear H
  | H:((?A [==] ?A) \/ (?C = ?D)) |- _ => clear H

  | H:((?A [==] ?B) \/ (?C [==] ?C)) |- _ => clear H
  | H:((?A [==] ?B) \/ (?C = ?C)) |- _ => clear H

  | H:((?A [==] ?B) \/ (?C [==] ?D)), H':((?B [==] ?A) \/ (?C [==] ?D)) |- _ => clear H'
  | H:((?A [==] ?B) \/ (?C [==] ?D)), H':((?A [==] ?B) \/ (?D [==] ?C)) |- _ => clear H'
  | H:((?A [==] ?B) \/ (?C [==] ?D)), H':((?B [==] ?A) \/ (?D [==] ?C)) |- _ => clear H'

  | H:((?A [==] ?B) \/ (?C = ?D)), H':((?B [==] ?A) \/ (?C = ?D)) |- _ => clear H'
  | H:((?A [==] ?B) \/ (?C = ?D)), H':((?A [==] ?B) \/ (?D = ?C)) |- _ => clear H'
  | H:((?A [==] ?B) \/ (?C = ?D)), H':((?B [==] ?A) \/ (?D = ?C)) |- _ => clear H'

  | H:(?A \/ ?B), H':(?B \/ ?A) |- _ => clear H'
  end.

Ltac ExistHyp t := match goal with
                   | H1:t |- _ => idtac
                   end.

Ltac HypOfType t := match goal with
                    | H1:t |- _ => H1
                    end.

Ltac CleanDuplicatedHyps :=
  repeat match goal with
         | H:?X1 |- _ => clear H; ExistHyp X1
         end.

Ltac Collapse := repeat (Apply_unicity; CleanDuplicatedHyps).

Ltac Collapse2 := repeat (Apply_uniqueness; CleanDuplicatedHyps).

Ltac simplify_ors :=
  match goal with
  | H: (?A [==] ?B) \/ (?C [==] ?D), H': ~(?A [==] ?B) |- _ => 
    elim H;[solve [intuition]|let Ha := fresh in intro Ha;rewrite Ha in *];clear H
  | H: (?A [==]?B) \/ (?C [==] ?D), H': ~(?B [==] ?A) |- _ => 
    elim H;[solve [let x:=fresh in intro x; symmetry in x;intuition]|let Ha:= fresh in intro Ha;rewrite Ha in *];clear H
  | H: (?A [==] ?B) \/ (?C [==] ?D), H': ~(?C [==] ?D) |- _ => 
    elim H;[intro;rewrite H' in * |solve [intuition]];clear H
  | H: (?A [==] ?B) \/ (?C [==] ?D), H': ~(?D [==] ?C) |- _ => 
    elim H;[let Ha:=fresh in intro Ha;rewrite Ha in *|solve [let x:=fresh in intro x; symmetry in x; intuition]];clear H
end.

Ltac not_exist_hyp t := match goal with
  | H1:t |- _ => fail 2
 end || idtac.


Ltac assert_if_not_exist H :=
  not_exist_hyp H;assert H.

Ltac assert_if_not_exist_t t :=
  let ty := type of t in (not_exist_hyp ty);let H := fresh in assert (H:=t).

Ltac compute_case := match goal with
| H1: Incid ?A ?l1, H2 : Incid ?A ?l2, H3: Incid ?B ?l1, H4: Incid ?B ?l2 |- _ => 
  assert_if_not_exist_t (uniqueness A B l1 l2 H1 H3 H2 H4)  
end.

Ltac compute_cases_old := repeat compute_case.

Ltac compute_cases := repeat compute_case;CleanDuplicatedHypsModulo;
repeat (try simplify_ors;CleanDuplicatedHypsModulo).

Ltac suppose t := cut t;[intro|idtac].

Ltac clear_all := repeat match goal with 
| H: _ |-_ => clear H
end.

Ltac DecompEx H P := elim H;intro P;intro;clear H.

Ltac DecompExAnd H P :=
  elim H;intro P;
  let id:=fresh in intro id;decompose [and] id;clear id;clear H.

Ltac DecompAndAll :=
 repeat
 match goal with
   | H:(?X1 /\ ?X2) |- _ => decompose [and] H;clear H
end.

Ltac use H := decompose [and ex] H; clear H.

Ltac use_all := repeat match goal with
| H: ?A /\ ?B  |- _ => use H
| H: ex ?P |- _ => use H
end.

Ltac rewrite_all H := 
 match type of H with
 | ?t1 = ?t2 => 
   let rec aux H :=
     match goal with
     | id : context [t1] |- _ => 
       match type of id with 
       | t1 = t2 => fail 1 
       | _ => revert id; try aux H; intro id
       end
     | _ => try rewrite H
     end in
   aux H
 end.

Ltac rewrite_all_inv H := 
 match type of H with
 | ?t1 = ?t2 => 
   let rec aux H :=
     match goal with
     | id : context [t2] |- _ => 
       match type of id with 
       | t1 = t2 => fail 1 
       | _ => revert id; try aux H; intro id
       end
     | _ => try rewrite <- H
     end in
   aux H
 end.