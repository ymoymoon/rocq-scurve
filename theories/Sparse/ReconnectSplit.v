Require Export Sparse.Reconnect.
Require Import Stdlib.Logic.ClassicalEpsilon.
Require Import Stdlib.Lists.List.
Import ListNotations.

(* sub を固定し、必要な場合だけ両側の蓋を安全な再接続へ置換する。 *)
Definition ordinary_reconnect_split
  (l sub r : list Segment) (h : R) : list Segment :=
  reconnect_segs l sub r h l ++ sub ++ reconnect_segs l sub r h r.

(* 蓋かどうかは、sub 側へ x 方向に戻る位置関係だけで判定する。
   可能な向きと凸性は、後で隣接関係 [dc] から導く。 *)
Definition terminal_lid (l : list Segment) : Prop :=
  l <> [] /\
  fst (term (last_segment l)) < fst (init (last_segment l)).

Definition initial_lid (r : list Segment) : Prop :=
  r <> [] /\
  fst (term (hd_segment r)) < fst (init (hd_segment r)).

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

(* sparse 性から得る安全な蓋を、epsilon で一つ選ぶ。 *)
Definition choose_terminal_lid
    (l sub r : list Segment) (h : R) : Segment :=
  epsilon (inhabits (reconnect_one l sub r h (last_segment l)))
    (terminal_lid_reconnect_spec l sub r h (last_segment l)
       (terminal_lid_blockers l sub r h)).

Definition choose_initial_lid
    (l sub r : list Segment) (h : R) : Segment :=
  epsilon (inhabits (reconnect_one l sub r h (hd_segment r)))
    (initial_lid_reconnect_spec l sub r h (hd_segment r)
       (initial_lid_blockers l sub r h)).

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
