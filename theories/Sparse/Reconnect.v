Require Import Admissible.
Require Import Reduction.
Require Import Stdlib.Reals.Reals.
Require Import Embed.
Require Import PrimitiveSegment.
Require Import Segment.
Require Import SegmentsTranslation.
Require Import ListExt.
Require Import Stdlib.Logic.ClassicalDescription.
Import ListNotations.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.

Require Export Sparse.Classify.
(* ================================================================= *)
(* 端点移動後の再接続 *)
(* ================================================================= *)

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

(* sub 自体は変更せず、左右の全端点だけを移動して再接続する。 *)
Definition reconnect_split
  (l sub r : list Segment) (h : R) : list Segment :=
  reconnect_segs l sub r h l ++ sub ++ reconnect_segs l sub r h r.
