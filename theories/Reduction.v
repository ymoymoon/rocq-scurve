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

(* r1, r2はすでに定義されているものとして、そいつらを使って1回変換する関数 *) 
Definition rule ps :=
  match r1 ps, r2 ps with
  | Some ps', _ => Some ps'
  | None, Some ps' => Some ps'
  | None, None => None
  end.

(* ruleが適用できたらかならずちっさくなる *)
Lemma rule_length_Some ps ps' :
  rule ps = Some ps' -> length ps' < length ps.
Admitted.

Definition inspect {A} (a : A) : {b | a = b} := exist _ a eq_refl.
Notation "x 'eqn' ':' p" := (exist _ x p) (only parsing, at level 20).

(* 先頭部分についてルールを繰り返し適用する再帰関数 *)
Equations? reduce_top (ps: list PrimitiveSegment)
  : list PrimitiveSegment by wf (length ps) :=
  reduce_top ps with inspect (rule ps) := {
    | Some ps' eqn:e => reduce_top ps'
    | None     eqn:e => ps
    }.
now apply rule_length_Some.
Qed.
