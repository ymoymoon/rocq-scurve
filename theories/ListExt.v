Require Export List.
Require Import Arith.
Import ListNotations.

Set Implicit Arguments.

Section Prefix.
  Variable A: Type.

  Definition Prefix (pre xs: list A) := exists r, xs = pre ++ r.

  Lemma Prefix_app (pre r: list A) : Prefix pre (pre ++ r).
  Admitted.


  Lemma prefix_brothers_is_prefix (p1 p2 xs : list A) :
    Prefix p1 xs -> Prefix p2 xs ->
    Prefix p1 p2 \/ Prefix p2 p1.
  Admitted.

End Prefix.

Hint Resolve Prefix_app : core.

Fixpoint all_prefix {A:Set} (xs : list A) : list (list A) :=
  match xs with
  | [] => [[]]
  | x::xs' =>
      [] :: map (fun ys => x :: ys) (all_prefix xs')
  end.

Fixpoint all_sublists {A:Set} (xs: list A) : list (list A) :=
  match xs with
  | [] => [[]]
  | x::xs' =>
      map (fun ys => x :: ys) (all_prefix xs') ++ all_sublists xs'
  end.

Inductive sublist {A:Set} : list A -> list A -> Prop:=
| SL l xs r: sublist xs (l ++ xs ++ r).

Lemma all_prefix_iff {A:Set} (l: list A) :
  forall sub, (In sub (all_prefix l) <-> Prefix sub l).
Proof.
  intros sub. split.
  - revert sub. induction l as [| a l IHl].
    + intros sub Hin. unfold all_prefix in Hin. inversion Hin as [Heq|Hcontra]. exists []. rewrite <- Heq. reflexivity. contradiction.
    + intros sub Hin. destruct Hin as [eq|Hin]. 
      * subst. exists (a::l). reflexivity.
      * apply in_map_iff in Hin. destruct Hin as [r [eq Hin]]. apply IHl in Hin. destruct Hin as [lr _eq]. subst. exists lr. reflexivity.
  - revert sub. induction l.
    + intros sub HPre. destruct HPre as [lr eq]. apply eq_sym in eq. apply app_eq_nil in eq as [eq _]. subst. simpl. now auto.
    + intros sub HPre. destruct HPre as [lr eq]. simpl. destruct sub as [|a0 sub];[now left|right].
      inversion eq as [[eqa eql]].
      assert(HPresubl: Prefix sub l). now exists lr.
      apply IHl in HPresubl. subst.
      apply in_map_iff. exists sub. split.
      * reflexivity.
      * now auto.
Qed.