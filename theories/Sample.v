Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Lists.List.
Open Scope R_scope.

Inductive V : Set :=
| n : V
| s : V
.

Inductive H : Set :=
| e : H
| w : H
.

Inductive C : Set :=
| cx : C
| cc : C
.

Inductive Dir : Set :=
| Ver : V -> Dir
| Hor : H -> Dir
.

Definition i_v (v : V) : V :=
match v with
| n => s
| s => n
end.

Definition i_h (h : H) : H :=
match h with
| e => w
| w => e
end.

Definition i (d: Dir) : Dir :=
match d with
| Ver v => Ver (i_v v)
| Hor h => Hor (i_h h)
end.

Definition i_c (c: C) : C :=
match c with
| cx => cc
| cc => cx
end. 

(* PrimitiveSegment，単位セグメント *)
Definition PrimitiveSegment := (V * H * C)%type.
(* 各要素を取り出す *)
Definition V_of (x:PrimitiveSegment) := fst(fst x).
Definition H_of (x:PrimitiveSegment) := snd(fst x).
Definition C_of (x:PrimitiveSegment) := snd x.

Parameter Segment : Set.

Parameter Embbed : PrimitiveSegment -> Segment -> Prop.

Parameter init : Segment -> R * R.

Parameter term : Segment -> R * R.

Parameter onSegment : Segment -> R * R -> Prop.

Axiom onInit : forall s: Segment, onSegment s (init s).

Axiom onTerm : forall s: Segment, onSegment s (term s).

Inductive ifl: PrimitiveSegment -> PrimitiveSegment -> Prop :=
| Ifl: forall (v: V) (h: H) (c_x c_y : C), 
    c_x = i_c c_y -> ifl (v, h, c_x) (v, h, c_y).

Inductive xtrv: PrimitiveSegment -> PrimitiveSegment -> Prop :=
| XtrvN: forall h: H, xtrv (n, h, cx) (s, h, cx)
| XtrvS: forall h: H, xtrv (s, h, cc) (n, h, cc)
.

Inductive xtrh: PrimitiveSegment -> PrimitiveSegment -> Prop :=
| XtrhN: forall h: H, xtrh (n, h, cc) (n, i_h h, cx)
| XtrhS: forall h: H, xtrh (s, h, cx) (s, i_h h, cc)
.

(* direct connect, 直接連結可能 *)
Definition dc (x y: PrimitiveSegment) : Prop :=
ifl x y \/ xtrv x y \/ xtrh x y.

(* 単位セグメントが単位セグメントのリストの先頭と連結可能かどうか *)
Inductive dc_pseg_hd: PrimitiveSegment -> list PrimitiveSegment -> Prop :=
| DcNil: forall (x:PrimitiveSegment), dc_pseg_hd x nil
| DcCons: forall (x y:PrimitiveSegment) (l:list PrimitiveSegment), dc x y -> dc_pseg_hd x (y::l)
.

(* scurveの条件 *)
Inductive is_scurve: list PrimitiveSegment -> Prop :=
| IsScurveNil: is_scurve nil
| IsScurveCons: forall (x:PrimitiveSegment) (xs:list PrimitiveSegment) , is_scurve xs -> dc_pseg_hd x xs -> is_scurve (x :: xs).

Definition scurve : Set := { l: list PrimitiveSegment | is_scurve l }.

(* 単位セグメントをscurveに連結 *)
Definition connect (s: PrimitiveSegment) (lp: scurve) (A: dc_pseg_hd s (proj1_sig lp)) : scurve :=
exist _ (s :: (proj1_sig lp)) (IsScurveCons s (proj1_sig lp) (proj2_sig lp) A).
