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
      let ps := all_prefix xs' in
      ps ++ map (fun ys => x :: ys) ps
  end.

Fixpoint all_sublists {A:Set} (xs: list A) : list (list A) :=
  match xs with
  | [] => [[]]
  | x::xs' =>
      map (fun ys => x :: ys) (all_prefix xs') ++ all_sublists xs'
  end.

Inductive sublist {A:Set} : list A -> list A -> Prop:=
| SL l xs r: sublist xs (l ++ xs ++ r).

Lemma in_app_app: forall {A: Type} (ls: list A) (a: A) , In a ls -> exists ls1 ls2, ls = ls1 ++ [a] ++ ls2.
Proof.
  intros A ls. induction ls as [| a ls IHls].
  - contradiction.
  - intros a0 Hin. destruct Hin as [Heqa| Hin].
    + exists [], ls. simpl. rewrite Heqa. reflexivity.
    + apply IHls in Hin. destruct Hin as [ls1' [ls2' Heq]]. exists (a::ls1'), ls2'. rewrite Heq. reflexivity.
Qed.

Lemma last_app: forall {A:Type} (l r:list A) (d: A), r <> [] -> last r d = last (l ++ r) d.
Proof.
  intros A l r. revert l. induction r as [| a res IHr].
  - intros l d Hcontra. contradiction.
  - intros l d _. destruct res as [|a' res].
    + simpl. rewrite last_last. reflexivity.
    + assert(Heq: (l ++ a :: a' :: res) = ((l ++ [a]) ++ a' :: res )).
      { rewrite <- app_assoc. simpl. reflexivity. }
      rewrite Heq.
      assert(Heq2: last (a :: a' :: res) d = last (a' :: res) d). reflexivity.
      rewrite Heq2. apply IHr. discriminate.
Qed.
