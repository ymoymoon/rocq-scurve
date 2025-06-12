Require Import Stdlib.Lists.List.
Require Import ZArith.
Require Import PrimitiveSegment.
Import ListNotations.
Open Scope Z_scope.

(* 向き *)
Inductive Direction : Set :=
| Plus : Direction
| Minus : Direction
.

(* 単位セグメントから向きへの変換 *)
Definition orn (x:PrimitiveSegment) : Direction :=
match x with
| (n, e, cx) | (s, e, cx) | (s, w, cc) | (n, w, cc) => Plus
| (s ,w, cx) | (s, e, cc) | (n, e, cc) | (n, w, cx) => Minus
end.

Definition rotation_difference (ds: list Direction) : Z :=
  fold_right Z.add 0 (map (fun d =>
                             match d with
                             | Plus => 1
                             | Minus => -1
                             end
  ) ds).

Lemma rotation_difference_distribution:
  forall (ds ds': list Direction),
  rotation_difference (ds ++ ds') = rotation_difference ds + rotation_difference ds'.
Proof.
  intros ds ds'.
  unfold rotation_difference.
  set (F := fun d =>
              match d with
              | Plus => 1
              | Minus => -1
              end).
  induction ds as [| d ds IH]; [now simpl | simpl].
  rewrite IH. now auto with zarith.
Qed.

(* 簡約のルール
 * r1: s1 = s3 = inv(s2) ならば σ1 s1 s2 s3 σ2 を σ1 s1 σ2 に置き換える. +−+ ⇒ +, −+− ⇒ −
 * r2: s1 = s2 = inv(s3) = inv(s4) ならば σ1 s1 s2 s3 s4 σ2 を σ1 s1 s4 σ2 に置き換える. ++−− ⇒ +−, −−++ ⇒ −+
 *)
Inductive Rule : list Direction -> list Direction -> Prop :=
| R1Plus : Rule [Plus; Minus; Plus] [Plus]
| R1Minus : Rule [Minus; Plus; Minus] [Minus]
| R2Plus : Rule [Plus; Plus; Minus; Minus] [Plus; Minus]
| R2Minus : Rule [Minus; Minus; Plus; Plus] [Minus; Plus]
.

Lemma rotation_difference_preservation_rule:
  forall (ds ds': list Direction), Rule ds ds' -> rotation_difference ds = rotation_difference ds'.
Proof.
  intros ds ds' H. now destruct H.
Qed.

Inductive ReduceDirStep : list Direction -> list Direction -> Prop :=
| RDS : forall (l r ds ds': list Direction), Rule ds ds' ->
    ReduceDirStep (l ++ ds ++ r) (l ++ ds' ++ r)
.

Lemma rotation_difference_preservation_step:
  forall (ds ds': list Direction), ReduceDirStep ds ds' -> rotation_difference ds = rotation_difference ds'.
Proof.
  intros ds ds' H.
  destruct H.
  apply rotation_difference_preservation_rule in H.
  repeat rewrite rotation_difference_distribution.
  apply Z.add_cancel_l. apply Z.add_cancel_r. now apply H.
Qed.

Inductive ReduceDir : list Direction -> list Direction -> Prop :=
| RDRefl : forall ds, ReduceDir ds ds
| RDTrans : forall ds ds' ds'', ReduceDirStep ds ds' -> ReduceDir ds' ds'' ->
    ReduceDir ds ds''
.

Definition Reduce (p p': list PrimitiveSegment): Prop :=
  ReduceDir (map orn p) (map orn p').

  (**
    * 簡約の性質2: 回転差保持
    * 簡約において +, − の個数の差は保持される.
    *)
Lemma rotation_difference_preservation:
  forall (ds ds': list Direction), ReduceDir ds ds' -> rotation_difference ds = rotation_difference ds'.
Proof.
  intros ds ds' H.
  induction H as [| ds ds']; [now reflexivity |].
  apply rotation_difference_preservation_step in H.
  rewrite H. now apply IHReduceDir.
Qed.
