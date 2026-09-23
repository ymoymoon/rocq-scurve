Require Export Sparse.Reconnect.
Require Import Stdlib.Lists.List.
Import ListNotations.

(* sub を固定し、必要な場合だけ両側の蓋を安全な再接続へ置換する。 *)
Definition ordinary_reconnect_split
  (l sub r : list Segment) (h : R) : list Segment :=
  reconnect_segs l sub r h l ++ sub ++ reconnect_segs l sub r h r.

Definition terminal_lid_blockers
    (l sub r : list Segment) (h : R) : list Segment :=
  nonadjacent_sides
    (removelast (reconnect_segs l sub r h l))
    (sub ++ reconnect_segs l sub r h r).

Definition initial_lid_blockers
    (l sub r : list Segment) (h : R) : list Segment :=
  nonadjacent_sides
    (reconnect_segs l sub r h l ++ sub)
    (tl (reconnect_segs l sub r h r)).

Definition terminal_lid_reconnect_spec
    (l sub r : list Segment) (h : R)
    (old : Segment) (blockers : list Segment) (new : Segment) : Prop :=
  reconnects_after l sub r h old new
  /\ slope_init new = slope_init old
  /\ segment_avoids_boxes new blockers.

Definition initial_lid_reconnect_spec
    (l sub r : list Segment) (h : R)
    (old : Segment) (blockers : list Segment) (new : Segment) : Prop :=
  reconnects_after l sub r h old new
  /\ slope_term new = slope_term old
  /\ segment_avoids_boxes new blockers.

(* 安全な蓋の具体的構成は、局所的な安全 corridor における
   セグメント再接続定理を導入するまで抽象化しておく。 *)
Parameter choose_terminal_lid :
  list Segment -> list Segment -> list Segment -> R -> Segment.

Parameter choose_initial_lid :
  list Segment -> list Segment -> list Segment -> R -> Segment.

Definition reconnect_left
    (l sub r : list Segment) (h : R) : list Segment :=
  if excluded_middle_informative (terminal_lid l) then
    removelast (reconnect_segs l sub r h l) ++
      [choose_terminal_lid l sub r h]
  else reconnect_segs l sub r h l.

Definition reconnect_right
    (l sub r : list Segment) (h : R) : list Segment :=
  if excluded_middle_informative (initial_lid r) then
    choose_initial_lid l sub r h :: tl (reconnect_segs l sub r h r)
  else reconnect_segs l sub r h r.

(* 通常再接続の後、必要な場合だけ sub に隣接する二つの蓋を
   障害長方形を避ける証人へ置換する。sub 自体は変更しない。 *)
Definition reconnect_split
    (l sub r : list Segment) (h : R) : list Segment :=
  reconnect_left l sub r h ++ sub ++ reconnect_right l sub r h.
