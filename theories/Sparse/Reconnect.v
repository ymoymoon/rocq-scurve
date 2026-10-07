Require Export Sparse.ClassifyDefinition.
Require Import Stdlib.Logic.ClassicalDescription.
Require Import Stdlib.Lists.List.
Import ListNotations.

(* 同じ再接続を、用途別の分類器に適用する。 *)
Module ReconnectByClassifier.
Section WithClassifier.
Variable classify : list Segment -> list Segment -> list Segment -> EndpointClassifier.

Definition operate_point (l sub r : list Segment) (h : R) (p : Point) : Point :=
  shift h (classify l sub r p) p.

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

(* sub を固定し、左右を再接続して曲線全体の列を返す。 *)
Definition reconnect_whole
  (l sub r : list Segment) (h : R) : list Segment :=
  reconnect_segs l sub r h l ++ sub ++ reconnect_segs l sub r h r.

End WithClassifier.
End ReconnectByClassifier.

(* 既存の PPMM・PM 呼び出し形は保持する。 *)
Definition reconnectable_after := ReconnectByClassifier.reconnectable_after classify.
Definition reconnect_slope_after := ReconnectByClassifier.reconnect_slope_after classify.
Definition reconnect_init_slope_after := ReconnectByClassifier.reconnect_init_slope_after classify.
Definition reconnect_term_slope_after := ReconnectByClassifier.reconnect_term_slope_after classify.
Definition head_init_slope_after := ReconnectByClassifier.head_init_slope_after classify.
Definition last_term_slope_after := ReconnectByClassifier.last_term_slope_after classify.
Definition all_reconnectable := ReconnectByClassifier.all_reconnectable classify.
Definition reconnect_one := ReconnectByClassifier.reconnect_one classify.
Definition reconnect_segs := ReconnectByClassifier.reconnect_segs classify.
Definition reconnect_whole := ReconnectByClassifier.reconnect_whole classify.
