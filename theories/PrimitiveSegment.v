
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
