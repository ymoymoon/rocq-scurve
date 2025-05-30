Require Import Stdlib.Lists.List.
Require Import Stdlib.Bool.Bool.
Require Import PrimitiveSegment.
Import ListNotations.
From Equations Require Import Equations.

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

Inductive Rule : list Direction -> list Direction -> Prop :=
| R1Plus : Rule [Plus; Minus; Plus] [Plus]
| R1Minus : Rule [Minus; Plus; Minus] [Minus]
| R2Plus : Rule [Plus; Plus; Minus; Minus] [Plus; Minus]
| R2Minus : Rule [Minus; Minus; Plus; Plus] [Minus; Plus].

Inductive ReduceDirStep : list Direction -> list Direction -> Prop :=
| RDS : forall (l r ds ds': list Direction), Rule ds ds' ->
    ReduceDirStep (l ++ ds ++ r) (l ++ ds' ++ r).

Inductive ReduceDir : list Direction -> list Direction -> Prop :=
| RDRefl : forall ds, ReduceDir ds ds
| RDTrans : forall ds ds' ds'', ReduceDirStep ds ds' ->
    ReduceDir ds ds''.

Definition Reduce p p' :=
  ReduceDir (map orn p) (map orn p').
