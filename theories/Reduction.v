Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Bool.Bool.
Require Import FunInd.
Require Import PrimitiveSegment.
Open Scope R_scope.
Import ListNotations.

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

Definition inv (x:Direction) : Direction :=
match x with
| Plus => Minus
| Minus => Plus
end.

Definition eq_dir (x y: Direction) : bool :=
match x, y with
| Plus, Plus => true
| Minus, Minus => true
| _, _ => false
end.

Fixpoint eq_dirlist (xs ys: list Direction) : bool :=
  match xs, ys with
  | [], [] => true
  | x::xs', y::ys' => if eq_dir x y then eq_dirlist xs' ys' else false
  | _, _ => false
  end.

(* 向きのリストを単位セグメントに変換 *)

(* 簡約 *)
Definition r1 (xs: list Direction) : list Direction :=
match xs with
| s1 :: s2 :: s3 :: xs' =>
    if eq_dir s1 s3 && eq_dir s3 (inv s2) then
      s1 :: xs'
    else
      xs
| _ => xs
end.

Definition r2 (xs: list Direction) : list Direction :=
match xs with
| s1 :: s2 :: s3 :: s4 :: xs' =>
    if eq_dir s1 s2 && eq_dir s2 (inv s3) && eq_dir (inv s3) (inv s4) then
      s1 :: s4 :: xs'
    else
      xs
| _ => xs
end.

Definition reductionStep (xs: list Direction) : list Direction :=
  let xs := r1 xs in
  let xs := r2 xs in
  xs.
