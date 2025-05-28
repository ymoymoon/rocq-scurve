Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Bool.Bool.
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
Definition r1 (xs: list PrimitiveSegment) : option (list PrimitiveSegment) :=
match xs with
| s1 :: s2 :: s3 :: xs' =>
    if eq_dir (orn s1) (orn s3) && eq_dir (orn s3) (inv (orn s2)) then
      Some (s1 :: xs')
    else
      None
| _ => None
end.

Definition r2 (xs: list PrimitiveSegment) : option (list PrimitiveSegment) :=
match xs with
| s1 :: s2 :: s3 :: s4 :: xs' =>
    if eq_dir (orn s1) (orn s2) && eq_dir (orn s2) (inv (orn s3)) && eq_dir (inv (orn s3)) (inv (orn s4)) then
      Some (s1 :: s4 :: xs')
    else
      None
| _ => None
end.

Definition reductionStep (xs: list PrimitiveSegment) : list PrimitiveSegment :=
  match r1 xs with
  | Some xs' =>
      match r2 xs' with
      | Some xs'' => xs''
      | None => xs'
      end
  | None =>
      match r2 xs with
      | Some xs' => xs'
      | None => xs
      end
  end.
