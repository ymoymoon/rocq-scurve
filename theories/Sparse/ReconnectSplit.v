Require Export Sparse.Reconnect.
Require Import Stdlib.Lists.List.
Import ListNotations.

(* sub を固定し、左右の端点を再接続する。 *)
Definition ordinary_reconnect_split
  (l sub r : list Segment) (h : R) : list Segment :=
  reconnect_segs l sub r h l ++ sub ++ reconnect_segs l sub r h r.
