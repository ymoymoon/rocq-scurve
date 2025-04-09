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


(*セグメントは[0,1]->R*Rの関数のうち次の条件を満たしたもの
・[0,1]で微分可能
・1要素目，2要素目の関数において，[0,1]で勾配の正負が一定．
・dy/dxが微分可能
・[0,1]において凸性が変わらない
    <=> forall t \in [0,1], d2y/dx2 = d/dt(dy/dx) * (dx/dt)の正負が一定
    <=> forall t \in [0,1], d2y/dx2 = d/dt(dy/dx)の正負が一定*)

(* R*Rの微分 *)
Definition derivable_pair_pt (f : R -> R * R) (t : R) : Set :=
  derivable_pt (fun t1 => fst (f t1)) t * derivable_pt (fun t1 => snd (f t1)) t.

Definition derivable_pair (f : R -> R * R) : Set :=
  forall t : R, derivable_pair_pt f t.

Definition derive_pair_fst (f : R -> R * R) (pr : derivable_pair f) (x : R) : R :=
  derive_pt (fun t => fst (f t)) x (fst (pr x)).
Definition derive_pair_snd (f : R -> R * R) (pr : derivable_pair f) (x : R) : R :=
  derive_pt (fun t => snd (f t)) x (snd (pr x)).

Definition derivable_dydx_pt (f : R -> R * R) (t : R) (pr : derivable_pair f): Set :=
  derivable_pt (fun t1 => (derive_pair_snd f pr t1) / (derive_pair_fst f pr t1)) t.

Definition derivable_dydx (f : R -> R * R) (pr : derivable_pair f): Set :=
  forall t: R, derivable_dydx_pt f t pr.


Parameter Segment : Set.

Parameter embed : PrimitiveSegment -> Segment -> Prop.

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

(* scurveの埋め込み．scurveとSegmentのリストの述語．
lp: scurve にps: PrimitiveSegment をくっつけたものが (s2::ls): list Segment にs1: Segment をくっつけたものとして埋め込まれる関係　*)
Inductive embed_scurve : scurve -> list Segment -> Prop :=
| EmbedScurveNil : embed_scurve (exist _ nil IsScurveNil) nil
| EmbedScurveSigle : forall (ps:PrimitiveSegment) (s:Segment), 
    embed ps s 
    -> embed_scurve (connect ps (exist _ nil IsScurveNil) (DcNil ps)) (s::nil)
| EmbedScurveCons : forall (ps:PrimitiveSegment) (lp: scurve) (A: dc_pseg_hd ps (proj1_sig lp)) (s1 s2: Segment) (ls: list Segment),
    embed ps s1
    -> embed_scurve lp (s2::ls)
    -> term s1 = init s2
    -> embed_scurve (connect ps lp A) (s1 :: s2 :: ls).

(* 埋め込んだ曲線を延長する *)
Parameter extend: list Segment -> list Segment.

Parameter crossed: Segment -> Segment -> Prop.

Definition close (ls: list Segment) : Prop :=
    (exists (s1 s2: Segment), In s1 (extend ls) -> In s2 (extend ls) -> crossed s1 s2).

(* 
Inductive close : list Segment -> Prop :=
| Close: forall (ls: list Segment), 
    (exists (s1 s2: Segment), In s1 (extend ls) -> In s2 (extend ls) -> crossed s1 s2)
     -> close ls. *)

(* admissible, 許容可能 *)
Definition admissible (lp: scurve) : Prop :=
    (exists ls: list Segment, embed_scurve lp ls -> close ls -> False).