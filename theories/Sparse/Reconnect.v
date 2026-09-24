Require Export Sparse.Classify.
Require Import Stdlib.Logic.ClassicalDescription.
Require Import Stdlib.Lists.List.
Import ListNotations.

(* 分類後の端点から各セグメントを作り直す通常再接続。 *)
Definition reconnectable_after
  (l sub r : list Segment) (h : R) (s : Segment) : Prop :=
  reconnectable
    (operate_point l sub r h (init s))
    (operate_point l sub r h (term s))
    (orn_seg s).

Definition reconnect_slope_after
  (l sub r : list Segment) (h : R) (s : Segment) : Prop :=
  reconnect_slope
    (operate_point l sub r h (init s))
    (operate_point l sub r h (term s))
    (orn_seg s) (slope_init s) (slope_term s).

Definition reconnect_init_slope_after
  (l sub r : list Segment) (h : R) (s : Segment) : Prop :=
  reconnect_init_slope
    (operate_point l sub r h (init s))
    (operate_point l sub r h (term s))
    (orn_seg s) (slope_init s).

Definition reconnect_term_slope_after
  (l sub r : list Segment) (h : R) (s : Segment) : Prop :=
  reconnect_term_slope
    (operate_point l sub r h (init s))
    (operate_point l sub r h (term s))
    (orn_seg s) (slope_term s).

Definition head_init_slope_after
  (l sub r : list Segment) (h : R) (s : Segment) : Prop :=
  l <> [] /\ s = hd_segment l /\ reconnect_init_slope_after l sub r h s.

Definition last_term_slope_after
  (l sub r : list Segment) (h : R) (s : Segment) : Prop :=
  r <> [] /\ s = last_segment r /\ reconnect_term_slope_after l sub r h s.

Definition all_reconnectable
  (l sub r : list Segment) (h : R) (ls : list Segment) : Prop :=
  forall s, In s ls -> reconnectable_after l sub r h s.

Definition reconnect_one
  (l sub r : list Segment) (h : R) (s : Segment) : Segment :=
  match excluded_middle_informative (reconnectable_after l sub r h s) with
  | left H =>
      match excluded_middle_informative
              (reconnect_slope_after l sub r h s) with
      | left Hs => make_seg_slope
          (operate_point l sub r h (init s))
          (operate_point l sub r h (term s))
          (orn_seg s) (slope_init s) (slope_term s) Hs
      | right _ =>
          match excluded_middle_informative
                  (head_init_slope_after l sub r h s) with
          | left Hs => make_seg_init_slope
              (operate_point l sub r h (init s))
              (operate_point l sub r h (term s))
              (orn_seg s) (slope_init s) (proj2 (proj2 Hs))
          | right _ =>
              match excluded_middle_informative
                      (last_term_slope_after l sub r h s) with
              | left Hs => make_seg_term_slope
                  (operate_point l sub r h (init s))
                  (operate_point l sub r h (term s))
                  (orn_seg s) (slope_term s) (proj2 (proj2 Hs))
              | right _ => make_seg
                  (operate_point l sub r h (init s))
                  (operate_point l sub r h (term s))
                  (orn_seg s) H
              end
          end
      end
  | right _ => default_segment
  end.

Definition reconnect_segs
  (l sub r : list Segment) (h : R) (ls : list Segment) : list Segment :=
  map (reconnect_one l sub r h) ls.

(* sub 自体は変更せず、左右の全端点だけを通常の方法で再接続する。
   安全な先頭・末尾を選ぶ最終的な [reconnect_split] の内部候補である。 *)

Definition reconnects_after
    (l sub r : list Segment) (h : R) (s s' : Segment) : Prop :=
  init s' = operate_point l sub r h (init s)
  /\ term s' = operate_point l sub r h (term s)
  /\ orn_seg s' = orn_seg s.

(* 左右の各セグメントを、位置を保って再接続した対応。 *)
Definition reconnects_list_after
    (l sub r : list Segment) (h : R)
    (old new : list Segment) : Prop :=
  Forall2 (reconnects_after l sub r h) old new.

(* 同じ向きの再接続セグメントが、指定した全障害長方形を避けること。 *)
Definition segment_avoids_boxes
    (s : Segment) (blockers : list Segment) : Prop :=
  forall t p,
    In t blockers ->
    in_segment_rect_or_endpoints t p ->
    ~ onSegment s p.
