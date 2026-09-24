Require Export Sparse.Sparsity.
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Lists.List.
Import ListNotations.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.
Open Scope R_scope.
(* ================================================================= *)
(* sub と移動量 *)
(* ================================================================= *)

Definition segment_coord_min (coord : Point -> R) (s : Segment) : R :=
  Rmin (coord (init s)) (coord (term s)).

Definition segment_coord_max (coord : Point -> R) (s : Segment) : R :=
  Rmax (coord (init s)) (coord (term s)).

(* 非空なセグメント列の全端点における座標の最小値・最大値。 *)
Fixpoint segments_coord_min
  (coord : Point -> R) (s : Segment) (rest : list Segment) : R :=
  match rest with
  | [] => segment_coord_min coord s
  | t :: rest' =>
      Rmin (segment_coord_min coord s) (segments_coord_min coord t rest')
  end.

Fixpoint segments_coord_max
  (coord : Point -> R) (s : Segment) (rest : list Segment) : R :=
  match rest with
  | [] => segment_coord_max coord s
  | t :: rest' =>
      Rmax (segment_coord_max coord s) (segments_coord_max coord t rest')
  end.

(* 空列の bbox は退化した原点とする。非空列では全端点の厳密な bbox。 *)
Definition bbox_of (ls : list Segment) : Rect :=
  match ls with
  | [] => mkRect 0 0 0 0
  | first :: rest =>
      mkRect
        (segments_coord_min (fun p : Point => fst p) first rest)
        (segments_coord_min (fun p : Point => snd p) first rest)
        (segments_coord_max (fun p : Point => fst p) first rest)
        (segments_coord_max (fun p : Point => snd p) first rest)
  end.

Lemma segments_coord_bounds : forall coord s rest t,
  In t (s :: rest) ->
  segments_coord_min coord s rest <= segment_coord_min coord t
  /\ segment_coord_max coord t <= segments_coord_max coord s rest.
Proof.
  intros coord s rest. revert s.
  induction rest as [|a rest IH]; intros s t Hin.
  - simpl in Hin. destruct Hin as [<- | []]. split; reflexivity.
  - simpl in Hin |- *.
    destruct Hin as [<- | Hin].
    + split; [apply Rmin_l | apply Rmax_l].
    + destruct (IH a t Hin) as [Hmin Hmax].
      split.
      * eapply Rle_trans; [apply Rmin_r | exact Hmin].
      * eapply Rle_trans; [exact Hmax | apply Rmax_r].
Qed.

Lemma onSegment_y_bounds : forall s p,
  onSegment s p ->
  segment_coord_min (fun q : Point => snd q) s <= snd p
  /\ snd p <= segment_coord_max (fun q : Point => snd q) s.
Proof.
  intros s p Hp.
  destruct (segment_in_rectangle_or_endpoints s p Hp)
    as [-> | [-> | Hinside]].
  - split; [apply Rmin_l | apply Rmax_l].
  - split; [apply Rmin_r | apply Rmax_r].
  - unfold segment_coord_min, segment_coord_max.
    unfold in_open_segment_rectangle, in_rect, rect_between in Hinside.
    simpl in Hinside. lra.
Qed.

Lemma bbox_of_bounds :
  forall sub p, onSegmentlist sub p ->
    ry0 (bbox_of sub) <= snd p <= ry1 (bbox_of sub).
Proof.
  intros sub p [t [Ht Hp]].
  destruct sub as [|s rest]; [contradiction|].
  change
    (segments_coord_min (fun q : Point => snd q) s rest <= snd p
     <= segments_coord_max (fun q : Point => snd q) s rest).
  destruct (segments_coord_bounds (fun q : Point => snd q) s rest t Ht)
    as [Hmin Hmax].
  destruct (onSegment_y_bounds t p Hp) as [Hlo Hhi].
  split; lra.
Qed.

Definition well_split (l sub r : list Segment) : Prop :=
  sub <> [] /\ x_monotone_segs sub /\ ~ close (l ++ sub ++ r).

Definition h_large (h : R) (sub : list Segment) : Prop :=
  0 < h /\ rect_height (bbox_of sub) < h.

Lemma choose_h : forall sub, exists h, h_large h sub.
Proof.
  intros sub. exists (Rmax 1 (rect_height (bbox_of sub) + 1)).
  unfold h_large. split.
  - eapply Rlt_le_trans; [apply Rlt_0_1 | apply Rmax_l].
  - eapply Rlt_le_trans; [| apply Rmax_r]. lra.
Qed.
