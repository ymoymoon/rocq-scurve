Require Import Admissible.
Require Import Reduction.
Require Import Stdlib.Reals.Reals.
Require Import Embed.
Require Import PrimitiveSegment.
Require Import Segment.
Require Import SegmentsTranslation.
Require Import ListExt.
Require Import Stdlib.Logic.ClassicalDescription.
Require Import Stdlib.Logic.ClassicalEpsilon.
Import ListNotations.
From Stdlib Require Import Lra.
From Stdlib Require Import Lia.



Require Export Sparsity.
(* ================================================================= *)
(*  1.  端点の分類と上下移動                                         *)
(* ================================================================= *)

Inductive Region : Type := RegFix | RegUp | RegDown.

Inductive region_above : Region -> Region -> Prop :=
  | RegUp_above_Fix : region_above RegUp RegFix
  | RegUp_above_Down : region_above RegUp RegDown
  | RegFix_above_Down : region_above RegFix RegDown.

Definition region_at_or_above (g1 g2 : Region) : Prop :=
  g1 = g2 \/ region_above g1 g2.

Lemma region_at_or_above_RegUp_inv : forall g,
  region_at_or_above g RegUp -> g = RegUp.
Proof. intros g [H | H]; [exact H | inversion H]. Qed.

Lemma RegDown_at_or_above_inv : forall g,
  region_at_or_above RegDown g -> g = RegDown.
Proof. intros g [H | H]; [now symmetry | inversion H]. Qed.

Lemma region_above_not_reverse :
  forall g1 g2,
    region_above g1 g2 -> ~ region_at_or_above g2 g1.
Proof.
  intros g1 g2 H. destruct H; intros [Heq | Hrev];
    try discriminate; inversion Hrev.
Qed.

Definition endpoint_of_seg (s : Segment) (p : Point) : Prop :=
  p = init s \/ p = term s.

Definition endpoint_of (ls : list Segment) (p : Point) : Prop :=
  exists s, In s ls /\ endpoint_of_seg s p.

Lemma endpoint_of_onSegmentlist : forall ls p,
  endpoint_of ls p -> onSegmentlist ls p.
Proof.
  intros ls p [s [Hs Hend]]. exists s. split; [exact Hs |].
  destruct Hend as [Hp | Hp].
  - subst p. apply onInit.
  - subst p. apply onTerm.
Qed.

(* ----------------------------------------------------------------- *)
(*  分類境界と端点補正                                               *)
(* ----------------------------------------------------------------- *)

Inductive CutSide : Type := CutLeft | CutRight.
Inductive EndKind : Type := HeadEnd | LastEnd.
Inductive PatchForce : Type := ForceUp | ForceDown.
Inductive PatchSource : Type := InnerHorizontal | EndTrace.

Record PatchPlan : Type := mkPatchPlan {
  plan_source : PatchSource;
  plan_force : PatchForce;
  plan_inclusive : bool
}.

Record RegionPatch : Type := mkRegionPatch {
  patch_side : CutSide;
  patch_start_x : R;
  patch_reference : Point -> Prop;
  patch_force : PatchForce;
  patch_inclusive : bool
}.

(* 分類と、次の end が交差を調べるための現在の境界高さを一緒に持つ。 *)
Record ClassifyState : Type := mkClassifyState {
  state_region : Point -> Region;
  state_height : R -> R
}.

Definition choose_sub_y (sub : list Segment) (x : R) : R :=
  epsilon (inhabits 0%R) (fun y => onSegmentlist sub (x, y)).

Lemma choose_sub_y_spec :
  forall sub x,
    (exists y, onSegmentlist sub (x, y)) ->
    onSegmentlist sub (x, choose_sub_y sub x).
Proof.
  intros sub x Hex.
  unfold choose_sub_y. now apply epsilon_spec.
Qed.

Definition simple_height (sub : list Segment) (x : R) : R :=
  if Rlt_dec x (rx0 (rect_of sub)) then
    snd (init (hd_segment sub))
  else if Rlt_dec (rx1 (rect_of sub)) x then
    snd (term (last_segment sub))
  else
    choose_sub_y sub x.

Definition classify_at_height (height : R -> R) (p : Point) : Region :=
  if Rlt_dec (snd p) (height (fst p)) then RegDown
  else if Rlt_dec (height (fst p)) (snd p) then RegUp
  else RegFix.

Definition simple_classify_state (sub : list Segment) : ClassifyState :=
  mkClassifyState (classify_at_height (simple_height sub))
                  (simple_height sub).

Definition unique_trace_y_at
    (trace : Point -> Prop) (x y : R) : Prop :=
  trace (x, y) /\ forall y', trace (x, y') -> y' = y.

Definition choose_trace_y (trace : Point -> Prop) (x : R) : R :=
  epsilon (inhabits 0%R) (fun y => unique_trace_y_at trace x y).

Lemma choose_trace_y_spec :
  forall trace x,
    (exists y, unique_trace_y_at trace x y) ->
    unique_trace_y_at trace x (choose_trace_y trace x).
Proof.
  intros trace x Hex.
  unfold choose_trace_y. now apply epsilon_spec.
Qed.

Definition trace_height
    (trace : Point -> Prop) (x : R) : option R :=
  match excluded_middle_informative
          (exists y, unique_trace_y_at trace x y) with
  | left _ => Some (choose_trace_y trace x)
  | right _ => None
  end.

Lemma trace_height_some_spec :
  forall trace x y,
    trace_height trace x = Some y ->
    unique_trace_y_at trace x y.
Proof.
  intros trace x y Hheight. unfold trace_height in Hheight.
  destruct (excluded_middle_informative
              (exists y0, unique_trace_y_at trace x y0))
    as [Hex | Hnone]; [|discriminate].
  injection Hheight as <-. now apply choose_trace_y_spec.
Qed.

Lemma trace_height_none_spec :
  forall trace x,
    trace_height trace x = None ->
    ~ exists y, unique_trace_y_at trace x y.
Proof.
  intros trace x Hheight. unfold trace_height in Hheight.
  destruct (excluded_middle_informative
              (exists y, unique_trace_y_at trace x y))
    as [Hex | Hnone]; [discriminate | exact Hnone].
Qed.

Definition horizontal_trace (y : R) : Point -> Prop :=
  fun p => snd p = y.

Lemma horizontal_trace_height :
  forall x y, trace_height (horizontal_trace y) x = Some y.
Proof.
  intros x y. unfold trace_height.
  destruct (excluded_middle_informative
              (exists y0, unique_trace_y_at (horizontal_trace y) x y0))
    as [Hex | Hnone].
  - f_equal.
    pose proof (choose_trace_y_spec (horizontal_trace y) x Hex)
      as [Hchosen _].
    exact Hchosen.
  - exfalso. apply Hnone. exists y. split; [reflexivity |].
    intros y' Hy'. exact Hy'.
Qed.

Definition end_segment
    (l r : list Segment) (k : EndKind) : option Segment :=
  match k with
  | HeadEnd =>
      match l with
      | [] => None
      | seg :: _ => Some seg
      end
  | LastEnd =>
      match r with
      | [] => None
      | _ => Some (last_segment r)
      end
  end.

Definition end_trace
    (l r : list Segment) (k : EndKind) : Point -> Prop :=
  match end_segment l r k with
  | None => fun _ => False
  | Some seg =>
      match k with
      | HeadEnd => onHeadSegment seg
      | LastEnd => onLastSegment seg
      end
  end.

Definition inner_endpoint (k : EndKind) (s : Segment) : Point :=
  match k with
  | HeadEnd => term s
  | LastEnd => init s
  end.

Definition reverse_primitive (d : PrimitiveSegment) : PrimitiveSegment :=
  let '(v, h, c) := d in (i_v v, i_h h, c).

Definition rotate180_primitive (d : PrimitiveSegment) : PrimitiveSegment :=
  let '(v, h, c) := d in (i_v v, i_h h, c).

Definition normalize_patch_primitive
    (k : EndKind) (side : CutSide) (d : PrimitiveSegment)
    : PrimitiveSegment :=
  let d1 := match k with HeadEnd => reverse_primitive d | LastEnd => d end in
  match side with
  | CutLeft => d1
  | CutRight => rotate180_primitive d1
  end.

(* 基準形は「末尾が sub 左側の水平境界と交差する」場合。
   他の三配置はパラメータ反転と180度回転でこの表へ移す。 *)
Definition canonical_last_left_plan (d : PrimitiveSegment) : PatchPlan :=
  match d with
  | (n, e, cx) => mkPatchPlan InnerHorizontal ForceUp false
  | (n, e, cc) => mkPatchPlan InnerHorizontal ForceUp true
  | (s, e, cx) => mkPatchPlan InnerHorizontal ForceDown true
  | (s, e, cc) => mkPatchPlan InnerHorizontal ForceDown false
  | (s, w, _)  => mkPatchPlan EndTrace ForceUp true
  | (n, w, _)  => mkPatchPlan EndTrace ForceDown true
  end.

Definition opposite_force (f : PatchForce) : PatchForce :=
  match f with ForceUp => ForceDown | ForceDown => ForceUp end.

Definition patch_plan
    (k : EndKind) (side : CutSide) (s : Segment) : PatchPlan :=
  let base := canonical_last_left_plan
                (normalize_patch_primitive k side (primitive_segment s)) in
  match side with
  | CutLeft => base
  | CutRight =>
      mkPatchPlan (plan_source base) (opposite_force (plan_force base))
                  (plan_inclusive base)
  end.

Definition make_end_patch
    (l r : list Segment) (k : EndKind) (side : CutSide)
    : option RegionPatch :=
  match end_segment l r k with
  | None => None
  | Some seg =>
      let inner := inner_endpoint k seg in
      let plan := patch_plan k side seg in
      let reference :=
        match plan_source plan with
        | InnerHorizontal => horizontal_trace (snd inner)
        | EndTrace => end_trace l r k
        end in
      Some (mkRegionPatch side (fst inner) reference
               (plan_force plan) (plan_inclusive plan))
  end.

Lemma make_end_patch_side_and_start :
  forall l r k side patch,
    make_end_patch l r k side = Some patch ->
    exists seg,
      end_segment l r k = Some seg
      /\ patch_side patch = side
      /\ patch_start_x patch = fst (inner_endpoint k seg).
Proof.
  intros l r k side patch Hpatch. unfold make_end_patch in Hpatch.
  destruct (end_segment l r k) as [seg |] eqn:Hseg; [|discriminate].
  injection Hpatch as <-.
  exists seg. split; [reflexivity | now split].
Qed.

Definition patch_active_at (patch : RegionPatch) (x : R) : Prop :=
  match patch_side patch with
  | CutLeft => x < patch_start_x patch
  | CutRight => patch_start_x patch < x
  end.

Definition patch_active_dec (patch : RegionPatch) (x : R) :
  {patch_active_at patch x} + {~ patch_active_at patch x} :=
  match patch_side patch as side
        return {match side with
                | CutLeft => x < patch_start_x patch
                | CutRight => patch_start_x patch < x
                end} +
               {~ match side with
                  | CutLeft => x < patch_start_x patch
                  | CutRight => patch_start_x patch < x
                  end} with
  | CutLeft => Rlt_dec x (patch_start_x patch)
  | CutRight => Rlt_dec (patch_start_x patch) x
  end.

Definition patch_forces_at
    (patch : RegionPatch) (reference_y : R) (p : Point) : Prop :=
  match patch_force patch, patch_inclusive patch with
  | ForceUp, false => reference_y < snd p
  | ForceUp, true => reference_y <= snd p
  | ForceDown, false => snd p < reference_y
  | ForceDown, true => snd p <= reference_y
  end.

Definition patch_forces_dec
    (patch : RegionPatch) (reference_y : R) (p : Point) :
  {patch_forces_at patch reference_y p} +
  {~ patch_forces_at patch reference_y p}.
Proof.
  destruct patch as [side start trace force inclusive].
  destruct force, inclusive; simpl; [apply Rle_dec | apply Rlt_dec |
    apply Rle_dec | apply Rlt_dec].
Defined.

Definition forced_region (f : PatchForce) : Region :=
  match f with ForceUp => RegUp | ForceDown => RegDown end.

Definition apply_region_patch
    (old : Point -> Region) (patch : RegionPatch) (p : Point) : Region :=
  match patch_active_dec patch (fst p) with
  | left _ =>
      match trace_height (patch_reference patch) (fst p) with
      | None => old p
      | Some y =>
          match patch_forces_dec patch y p with
          | left _ => forced_region (patch_force patch)
          | right _ => old p
          end
      end
  | right _ => old p
  end.

Definition apply_height_patch
    (old : R -> R) (patch : RegionPatch) (x : R) : R :=
  match patch_active_dec patch x with
  | left _ =>
      match trace_height (patch_reference patch) x with
      | Some y => y
      | None => old x
      end
  | right _ => old x
  end.

Definition apply_patch
    (st : ClassifyState) (patch : RegionPatch) : ClassifyState :=
  mkClassifyState
    (apply_region_patch (state_region st) patch)
    (apply_height_patch (state_height st) patch).

Lemma apply_region_patch_inactive :
  forall old patch p,
    ~ patch_active_at patch (fst p) ->
    apply_region_patch old patch p = old p.
Proof.
  intros old patch p Hinactive. unfold apply_region_patch.
  destruct (patch_active_dec patch (fst p)) as [Hactive |];
    [contradiction | reflexivity].
Qed.

Lemma apply_height_patch_inactive :
  forall old patch x,
    ~ patch_active_at patch x ->
    apply_height_patch old patch x = old x.
Proof.
  intros old patch x Hinactive. unfold apply_height_patch.
  destruct (patch_active_dec patch x) as [Hactive |];
    [contradiction | reflexivity].
Qed.

Lemma apply_region_patch_without_reference :
  forall old patch p,
    trace_height (patch_reference patch) (fst p) = None ->
    apply_region_patch old patch p = old p.
Proof.
  intros old patch p Hnone. unfold apply_region_patch.
  destruct (patch_active_dec patch (fst p)); [now rewrite Hnone | reflexivity].
Qed.

(* 点が補正範囲外か、基準線との比較が補正方向を満たさないこと。 *)
Definition patch_does_not_force_at
    (patch : RegionPatch) (p : Point) : Prop :=
  ~ patch_active_at patch (fst p)
  \/ forall y,
       trace_height (patch_reference patch) (fst p) = Some y ->
       ~ patch_forces_at patch y p.

Lemma apply_region_patch_not_forced :
  forall old patch p,
    patch_does_not_force_at patch p ->
    apply_region_patch old patch p = old p.
Proof.
  intros old patch p [Hinactive | Hunforced].
  - now apply apply_region_patch_inactive.
  - unfold apply_region_patch.
    destruct (patch_active_dec patch (fst p)); [|reflexivity].
    destruct (trace_height (patch_reference patch) (fst p)) as [y |] eqn:Hy;
      [|reflexivity].
    destruct (patch_forces_dec patch y p) as [Hforce |];
      [exfalso; exact (Hunforced y eq_refl Hforce) | reflexivity].
Qed.

(* 補正は Up/Down しか新しく作らないため、補正後の Fix は補正前から Fix。 *)
Lemma apply_region_patch_fix_inv :
  forall old patch p,
    apply_region_patch old patch p = RegFix ->
    old p = RegFix.
Proof.
  intros old patch p Hfix.
  unfold apply_region_patch in Hfix.
  destruct (patch_active_dec patch (fst p)); [|exact Hfix].
  destruct (trace_height (patch_reference patch) (fst p)); [|exact Hfix].
  destruct (patch_forces_dec patch r p); [|exact Hfix].
  destruct (patch_force patch); discriminate.
Qed.

Definition below_state_boundary (st : ClassifyState) (p : Point) : Prop :=
  snd p < state_height st (fst p).

Definition above_state_boundary (st : ClassifyState) (p : Point) : Prop :=
  state_height st (fst p) < snd p.

(* 垂直な重なりや水平な一致を除き、x の両側で上下が入れ替わる交点。 *)
Definition proper_state_crossing
    (st : ClassifyState) (trace : Point -> Prop) (p : Point) : Prop :=
  trace p
  /\ snd p = state_height st (fst p)
  /\ unique_trace_y_at trace (fst p) (snd p)
  /\ exists q r,
       trace q /\ trace r
       /\ fst q < fst p < fst r
       /\ ((below_state_boundary st q /\ above_state_boundary st r)
           \/ (above_state_boundary st q /\ below_state_boundary st r)).

Definition crossing_on_side
    (sub : list Segment) (side : CutSide) (p : Point) : Prop :=
  match side with
  | CutLeft => fst p < rx0 (rect_of sub)
  | CutRight => rx1 (rect_of sub) < fst p
  end.

Definition end_crossing
    (st : ClassifyState) (l sub r : list Segment)
    (k : EndKind) (side : CutSide) (p : Point) : Prop :=
  proper_state_crossing st (end_trace l r k) p
  /\ crossing_on_side sub side p.

Definition closest_end_crossing
    (st : ClassifyState) (l sub r : list Segment)
    (k : EndKind) (side : CutSide) (p : Point) : Prop :=
  end_crossing st l sub r k side p
  /\ forall q,
       end_crossing st l sub r k side q ->
       match side with
       | CutLeft => fst q <= fst p
       | CutRight => fst p <= fst q
       end.

Definition choose_closest_crossing
    (st : ClassifyState) (l sub r : list Segment)
    (k : EndKind) (side : CutSide) : Point :=
  epsilon (inhabits (0%R, 0%R))
    (closest_end_crossing st l sub r k side).

Lemma choose_closest_crossing_spec :
  forall st l sub r k side,
    (exists p, closest_end_crossing st l sub r k side p) ->
    closest_end_crossing st l sub r k side
      (choose_closest_crossing st l sub r k side).
Proof.
  intros st l sub r k side Hex.
  unfold choose_closest_crossing. now apply epsilon_spec.
Qed.

Definition nearest_end_crossing
    (st : ClassifyState) (l sub r : list Segment)
    (k : EndKind) (side : CutSide) : option Point :=
  match excluded_middle_informative
          (exists p, closest_end_crossing st l sub r k side p) with
  | left _ => Some (choose_closest_crossing st l sub r k side)
  | right _ => None
  end.

Lemma nearest_end_crossing_some_spec :
  forall st l sub r k side p,
    nearest_end_crossing st l sub r k side = Some p ->
    closest_end_crossing st l sub r k side p.
Proof.
  intros st l sub r k side p Hnearest.
  unfold nearest_end_crossing in Hnearest.
  destruct (excluded_middle_informative
              (exists p0, closest_end_crossing st l sub r k side p0))
    as [Hex | Hnone]; [|discriminate].
  injection Hnearest as <-. now apply choose_closest_crossing_spec.
Qed.

Lemma nearest_end_crossing_none_spec :
  forall st l sub r k side,
    nearest_end_crossing st l sub r k side = None ->
    ~ exists p, closest_end_crossing st l sub r k side p.
Proof.
  intros st l sub r k side Hnearest.
  unfold nearest_end_crossing in Hnearest.
  destruct (excluded_middle_informative
              (exists p, closest_end_crossing st l sub r k side p))
    as [Hex | Hnone]; [discriminate | exact Hnone].
Qed.

Lemma no_end_crossing_gives_none :
  forall st l sub r k side,
    (~ exists p, end_crossing st l sub r k side p) ->
    nearest_end_crossing st l sub r k side = None.
Proof.
  intros st l sub r k side Hnone. unfold nearest_end_crossing.
  destruct (excluded_middle_informative
              (exists p, closest_end_crossing st l sub r k side p))
    as [Hex |]; [|reflexivity].
  exfalso. apply Hnone. destruct Hex as [p [Hcross _]].
  now exists p.
Qed.

Definition apply_end_at
    (st : ClassifyState) (l r : list Segment)
    (k : EndKind) (side : CutSide) : ClassifyState :=
  match make_end_patch l r k side with
  | Some patch => apply_patch st patch
  | None => st
  end.

Definition process_end
    (st : ClassifyState) (l sub r : list Segment)
    (k : EndKind) (side : CutSide) : ClassifyState :=
  match nearest_end_crossing st l sub r k side with
  | Some _ => apply_end_at st l r k side
  | None => st
  end.

Definition crossing_closer
    (side : CutSide) (p q : Point) : Prop :=
  match side with
  | CutLeft => fst q < fst p
  | CutRight => fst p < fst q
  end.

Definition crossing_closer_dec (side : CutSide) (p q : Point) :
  {crossing_closer side p q} + {~ crossing_closer side p q}.
Proof. destruct side; simpl; apply Rlt_dec. Defined.

(* 二つ目の [process_end] は、一つ目の補正後の境界に対して交点を取り直す。
   一度処理した end は再検査せず、各側で補正は高々二回とする。 *)
Definition process_both_ends_on_side
    (st : ClassifyState) (l sub r : list Segment) (side : CutSide)
    : ClassifyState :=
  match nearest_end_crossing st l sub r HeadEnd side,
        nearest_end_crossing st l sub r LastEnd side with
  | None, None => st
  | Some _, None => apply_end_at st l r HeadEnd side
  | None, Some _ => apply_end_at st l r LastEnd side
  | Some ph, Some pl =>
      if crossing_closer_dec side ph pl then
        let st1 := apply_end_at st l r HeadEnd side in
        process_end st1 l sub r LastEnd side
      else
        let st1 := apply_end_at st l r LastEnd side in
        process_end st1 l sub r HeadEnd side
  end.

Definition end_patches_do_not_force_at
    (l r : list Segment) (p : Point) : Prop :=
  forall k side patch,
    make_end_patch l r k side = Some patch ->
    patch_does_not_force_at patch p.

Lemma apply_end_at_not_forced :
  forall st l r k side p,
    end_patches_do_not_force_at l r p ->
    state_region (apply_end_at st l r k side) p = state_region st p.
Proof.
  intros st l r k side p Hsafe. unfold apply_end_at.
  destruct (make_end_patch l r k side) as [patch |] eqn:Hpatch;
    [|reflexivity].
  simpl. apply apply_region_patch_not_forced.
  exact (Hsafe k side patch Hpatch).
Qed.

Lemma apply_end_at_fix_inv :
  forall st l r k side p,
    state_region (apply_end_at st l r k side) p = RegFix ->
    state_region st p = RegFix.
Proof.
  intros st l r k side p Hfix. unfold apply_end_at in Hfix.
  destruct (make_end_patch l r k side) as [patch |]; [|exact Hfix].
  simpl in Hfix. now apply apply_region_patch_fix_inv in Hfix.
Qed.

Lemma process_end_not_forced :
  forall st l sub r k side p,
    end_patches_do_not_force_at l r p ->
    state_region (process_end st l sub r k side) p = state_region st p.
Proof.
  intros st l sub r k side p Hsafe. unfold process_end.
  destruct (nearest_end_crossing st l sub r k side);
    [now apply apply_end_at_not_forced | reflexivity].
Qed.

Lemma process_end_without_crossing :
  forall st l sub r k side,
    (~ exists p, end_crossing st l sub r k side p) ->
    process_end st l sub r k side = st.
Proof.
  intros st l sub r k side Hnone. unfold process_end.
  now rewrite (no_end_crossing_gives_none st l sub r k side Hnone).
Qed.

Lemma process_end_fix_inv :
  forall st l sub r k side p,
    state_region (process_end st l sub r k side) p = RegFix ->
    state_region st p = RegFix.
Proof.
  intros st l sub r k side p Hfix. unfold process_end in Hfix.
  destruct (nearest_end_crossing st l sub r k side);
    [now apply apply_end_at_fix_inv in Hfix | exact Hfix].
Qed.

Lemma process_both_ends_not_forced :
  forall st l sub r side p,
    end_patches_do_not_force_at l r p ->
    state_region (process_both_ends_on_side st l sub r side) p =
    state_region st p.
Proof.
  intros st l sub r side p Hsafe.
  unfold process_both_ends_on_side.
  destruct (nearest_end_crossing st l sub r HeadEnd side) as [ph |];
  destruct (nearest_end_crossing st l sub r LastEnd side) as [pl |].
  - destruct (crossing_closer_dec side ph pl).
    + rewrite (process_end_not_forced
                 (apply_end_at st l r HeadEnd side)
                 l sub r LastEnd side p Hsafe).
      now apply apply_end_at_not_forced.
    + rewrite (process_end_not_forced
                 (apply_end_at st l r LastEnd side)
                 l sub r HeadEnd side p Hsafe).
      now apply apply_end_at_not_forced.
  - now apply apply_end_at_not_forced.
  - now apply apply_end_at_not_forced.
  - reflexivity.
Qed.

Lemma process_both_ends_fix_inv :
  forall st l sub r side p,
    state_region (process_both_ends_on_side st l sub r side) p = RegFix ->
    state_region st p = RegFix.
Proof.
  intros st l sub r side p Hfix.
  unfold process_both_ends_on_side in Hfix.
  destruct (nearest_end_crossing st l sub r HeadEnd side) as [ph |];
  destruct (nearest_end_crossing st l sub r LastEnd side) as [pl |].
  - destruct (crossing_closer_dec side ph pl).
    + apply process_end_fix_inv in Hfix.
      now apply apply_end_at_fix_inv in Hfix.
    + apply process_end_fix_inv in Hfix.
      now apply apply_end_at_fix_inv in Hfix.
  - now apply apply_end_at_fix_inv in Hfix.
  - now apply apply_end_at_fix_inv in Hfix.
  - exact Hfix.
Qed.

Definition build_classify_state
    (l sub r : list Segment) : ClassifyState :=
  let st0 := simple_classify_state sub in
  let st1 := process_both_ends_on_side st0 l sub r CutLeft in
  process_both_ends_on_side st1 l sub r CutRight.

(* 分類は基本境界から始め、各側で現在の境界に最も近い end を先に補正する。 *)
Definition classify
    (l sub r : list Segment) (p : Point) : Region :=
  state_region (build_classify_state l sub r) p.

Lemma classify_eq_simple_when_end_patches_do_not_force :
  forall l sub r p,
    end_patches_do_not_force_at l r p ->
    classify l sub r p = state_region (simple_classify_state sub) p.
Proof.
  intros l sub r p Hsafe. unfold classify, build_classify_state.
  rewrite (process_both_ends_not_forced
             (process_both_ends_on_side
                (simple_classify_state sub) l sub r CutLeft)
             l sub r CutRight p Hsafe).
  now apply process_both_ends_not_forced.
Qed.

Lemma nil_end_patches_do_not_force :
  forall p, end_patches_do_not_force_at [] [] p.
Proof.
  intros p k side patch Hpatch. destruct k; discriminate.
Qed.

Lemma classify_without_sides_eq_simple :
  forall sub p,
    classify [] sub [] p = state_region (simple_classify_state sub) p.
Proof.
  intros sub p. apply classify_eq_simple_when_end_patches_do_not_force.
  apply nil_end_patches_do_not_force.
Qed.

Lemma classify_fix_implies_simple_fix :
  forall l sub r p,
    classify l sub r p = RegFix ->
    state_region (simple_classify_state sub) p = RegFix.
Proof.
  intros l sub r p Hfix. unfold classify, build_classify_state in Hfix.
  apply process_both_ends_fix_inv in Hfix.
  now apply process_both_ends_fix_inv in Hfix.
Qed.

Definition in_sub_x_range (sub : list Segment) (p : Point) : Prop :=
  rx0 (rect_of sub) <= fst p <= rx1 (rect_of sub).

Definition above_sub_at_x (sub : list Segment) (p : Point) : Prop :=
  exists q,
    onSegmentlist sub q
    /\ fst p = fst q
    /\ snd q < snd p.

Definition below_sub_at_x (sub : list Segment) (p : Point) : Prop :=
  exists q,
    onSegmentlist sub q
    /\ fst p = fst q
    /\ snd p < snd q.

(* x 方向の閉区間が交わる二つの端点長方形。 *)
Definition segment_x_ranges_overlap (s t : Segment) : Prop :=
  rx0 (rect_of [s]) <= rx1 (rect_of [t])
  /\ rx0 (rect_of [t]) <= rx1 (rect_of [s]).

Record ClassificationSpec (l sub r : list Segment) : Prop := {

  (* sub は固定 *)
  classified_sub_fixed :
    forall p, onSegmentlist sub p -> classify l sub r p = RegFix;

  (* セグメントの始点が終点より低く，始点の領域が Up なら終点も Up など *)
  classified_segment_endpoints_monotone :
    forall s,
      In s (l ++ sub ++ r) ->
      (snd (init s) < snd (term s) ->
        region_at_or_above (classify l sub r (term s)) (classify l sub r (init s)))
      /\
      (snd (term s) < snd (init s) ->
        region_at_or_above (classify l sub r (init s)) (classify l sub r (term s)));

  (* x 範囲が重なる非隣接セグメントについては、sub 上にある端点を
     除き、下側の長方形が Up なら上側の長方形も Up など。 *)
  classified_nonadjacent_endpoint_order :
    forall i j s t ps pt,
      nth_error (l ++ sub ++ r) i = Some s ->
      nth_error (l ++ sub ++ r) j = Some t ->
      (S i < j \/ S j < i)%nat ->
      segment_x_ranges_overlap s t ->
      endpoint_of_seg s ps ->
      endpoint_of_seg t pt ->
      ~ onSegmentlist sub ps ->
      ~ onSegmentlist sub pt ->
      snd ps <= snd pt ->
      region_at_or_above
        (classify l sub r pt) (classify l sub r ps);

  (* sub と同じ x 座標を持つセグメントは Up もしくは Down *)
  classified_segment_at_sub_x :
    forall s p,
      In s (nonadjacent_sides l r) ->
      onSegment s p ->
      in_sub_x_range sub p ->
      (above_sub_at_x sub p ->
         classify l sub r (init s) = RegUp
         /\ classify l sub r (term s) = RegUp)
      /\
      (below_sub_at_x sub p ->
         classify l sub r (init s) = RegDown
         /\ classify l sub r (term s) = RegDown);

  (* strict 延長線が sub 長方形の閉 x 範囲へ入る場合，
     その延長線を動かす基点は Fix ではない。 *)
  classified_head_extension_at_sub_x :
    forall p,
      onHead_extend_strict (l ++ sub ++ r) p ->
      rx0 (rect_of sub) <= fst p <= rx1 (rect_of sub) ->
      classify l sub r (init (hd_segment (l ++ sub ++ r))) = RegUp
      \/ classify l sub r (init (hd_segment (l ++ sub ++ r))) = RegDown;

  classified_last_extension_at_sub_x :
    forall p,
      onLast_extend_strict (l ++ sub ++ r) p ->
      rx0 (rect_of sub) <= fst p <= rx1 (rect_of sub) ->
      classify l sub r (term (last_segment (l ++ sub ++ r))) = RegUp
      \/ classify l sub r (term (last_segment (l ++ sub ++ r))) = RegDown;

  (* 延長線が同じ x 座標の点を持つ時，下側が Up なら上側も Up など *)
  classified_head_last_extension_order :
    forall ph pl,
      onHead_extend (l ++ sub ++ r) ph ->
      onLast_extend (l ++ sub ++ r) pl ->
      fst ph = fst pl ->
      (snd ph < snd pl ->
         region_at_or_above
           (classify l sub r (term (last_segment (l ++ sub ++ r))))
           (classify l sub r (init (hd_segment (l ++ sub ++ r)))))
      /\
      (snd pl < snd ph ->
         region_at_or_above
           (classify l sub r (init (hd_segment (l ++ sub ++ r))))
           (classify l sub r (term (last_segment (l ++ sub ++ r)))));

  (* セグメントと延長線が同じ x 座標の点を持つ時，下側が Up なら上側も Up など *)
  classified_head_segment_crossing_order :
    forall s e q,
      In s (l ++ sub ++ r) ->
      onSegment s e ->
      onHead_extend_strict (l ++ sub ++ r) q ->
      fst e = fst q ->
      (snd q < snd e ->
         region_at_or_above
           (classify l sub r (init s))
           (classify l sub r (init (hd_segment (l ++ sub ++ r))))
         /\ region_at_or_above
           (classify l sub r (term s))
           (classify l sub r (init (hd_segment (l ++ sub ++ r)))))
      /\
      (snd e < snd q ->
         region_at_or_above
           (classify l sub r (init (hd_segment (l ++ sub ++ r))))
           (classify l sub r (init s))
         /\ region_at_or_above
           (classify l sub r (init (hd_segment (l ++ sub ++ r))))
           (classify l sub r (term s)));

  classified_last_segment_crossing_order :
    forall s e q,
      In s (l ++ sub ++ r) ->
      onSegment s e ->
      onLast_extend_strict (l ++ sub ++ r) q ->
      fst e = fst q ->
      (snd q < snd e ->
         region_at_or_above
           (classify l sub r (init s))
           (classify l sub r (term (last_segment (l ++ sub ++ r))))
         /\ region_at_or_above
           (classify l sub r (term s))
           (classify l sub r (term (last_segment (l ++ sub ++ r)))))
      /\
      (snd e < snd q ->
         region_at_or_above
           (classify l sub r (term (last_segment (l ++ sub ++ r))))
           (classify l sub r (init s))
         /\ region_at_or_above
           (classify l sub r (term (last_segment (l ++ sub ++ r))))
           (classify l sub r (term s)));

  (* 先頭の両端が別領域なら、始点傾きを保てる向き・凸性に限る。 *)
  classified_head_slope_case :
    l <> [] ->
    classify l sub r (init (hd_segment l)) =
      classify l sub r (term (hd_segment l))
    \/ (classify l sub r (init (hd_segment l)) = RegUp
        /\ (embed (s, w, cx) (hd_segment l)
            \/ embed (s, e, cx) (hd_segment l)))
    \/ (classify l sub r (init (hd_segment l)) = RegDown
        /\ (embed (n, w, cc) (hd_segment l)
            \/ embed (n, e, cc) (hd_segment l)));

  (* 末尾では双対的に、終点傾きを保てる場合だけ別領域を許す。 *)
  classified_last_slope_case :
    r <> [] ->
    classify l sub r (init (last_segment r)) =
      classify l sub r (term (last_segment r))
    \/ (classify l sub r (term (last_segment r)) = RegUp
        /\ (embed (n, w, cx) (last_segment r)
            \/ embed (n, e, cx) (last_segment r)))
    \/ (classify l sub r (term (last_segment r)) = RegDown
        /\ (embed (s, w, cc) (last_segment r)
            \/ embed (s, e, cc) (last_segment r)))
}.

Lemma connected_x_monotone_endpoints :
  forall sub,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    fst (init (hd_segment sub)) < fst (term (last_segment sub)).
Proof.
  intros sub Hne. destruct sub as [|a tail]; [contradiction|].
  clear Hne.
  revert a. induction tail as [|b tail IH]; intros a Hconn Hmono.
  - apply Hmono. now left.
  - assert (Hab : term a = init b).
    { apply (Hconn 0%nat a b); reflexivity. }
    assert (HconnTail : connected (b :: tail)).
    { intros i s1 s2 H1 H2.
      apply (Hconn (S i) s1 s2); simpl; assumption. }
    assert (HmonoTail : x_monotone_segs (b :: tail)).
    { intros t Ht. apply Hmono. now right. }
    pose proof (IH b HconnTail HmonoTail) as Htail.
    pose proof (Hmono a ltac:(now left)) as Ha.
    change (fst (init a) < fst (term (last_segment (b :: tail)))).
    change (fst (init b) < fst (term (last_segment (b :: tail)))) in Htail.
    unfold x_monotone_seg, init_x, term_x in Ha.
    rewrite Hab in Ha. lra.
Qed.

(* x 単調な連結列では、全体長方形の左右端は列の始終点である。 *)
Lemma x_monotone_rect_x_bounds :
  forall sub,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    rx0 (rect_of sub) = fst (init (hd_segment sub))
    /\ rx1 (rect_of sub) = fst (term (last_segment sub)).
Proof.
  intros sub Hne Hconn Hmono.
  pose proof (connected_x_monotone_endpoints sub Hne Hconn Hmono) as Hends.
  unfold rect_of; simpl.
  rewrite Rmin_left by lra.
  rewrite Rmax_right by lra.
  split; reflexivity.
Qed.

(* セグメントの端点 x 区間内の各 x 座標は、セグメント上で実現される。 *)
Lemma segment_has_point_at_x :
  forall s x,
    rx0 (rect_of [s]) <= x <= rx1 (rect_of [s]) ->
    exists p, onSegment s p /\ fst p = x.
Proof.
  intros s x Hx.
  destruct (total_order_T (fst (init s)) (fst (term s)))
    as [[Hix | Heq] | Htx].
  - change (Rmin (fst (init s)) (fst (term s)) <= x <=
            Rmax (fst (init s)) (fst (term s))) in Hx.
    rewrite Rmin_left in Hx by lra.
    rewrite Rmax_right in Hx by lra.
    destruct (Rle_dec (snd (init s)) (snd (term s))) as [Hy | Hy].
    + destruct (exist_between_x_pos s
                  (fst (init s)) (fst (term s))
                  (snd (init s)) (snd (term s)) x
                  ltac:(rewrite <- surjective_pairing; apply onInit)
                  ltac:(rewrite <- surjective_pairing; apply onTerm)
                  Hy (proj1 Hx) (proj2 Hx)) as [y [Hon _]].
      exists (x, y). split; [exact Hon | reflexivity].
    + destruct (exist_between_x_neg s
                  (fst (init s)) (fst (term s))
                  (snd (init s)) (snd (term s)) x
                  ltac:(rewrite <- surjective_pairing; apply onInit)
                  ltac:(rewrite <- surjective_pairing; apply onTerm)
                  ltac:(lra) (proj1 Hx) (proj2 Hx)) as [y [Hon _]].
      exists (x, y). split; [exact Hon | reflexivity].
  - exfalso. apply (neq_init_term_x s).
    unfold init_x, term_x. exact Heq.
  - change (Rmin (fst (init s)) (fst (term s)) <= x <=
            Rmax (fst (init s)) (fst (term s))) in Hx.
    rewrite Rmin_right in Hx by lra.
    rewrite Rmax_left in Hx by lra.
    destruct (Rle_dec (snd (term s)) (snd (init s))) as [Hy | Hy].
    + destruct (exist_between_x_pos s
                  (fst (term s)) (fst (init s))
                  (snd (term s)) (snd (init s)) x
                  ltac:(rewrite <- surjective_pairing; apply onTerm)
                  ltac:(rewrite <- surjective_pairing; apply onInit)
                  Hy (proj1 Hx) (proj2 Hx)) as [y [Hon _]].
      exists (x, y). split; [exact Hon | reflexivity].
    + destruct (exist_between_x_neg s
                  (fst (term s)) (fst (init s))
                  (snd (term s)) (snd (init s)) x
                  ltac:(rewrite <- surjective_pairing; apply onTerm)
                  ltac:(rewrite <- surjective_pairing; apply onInit)
                  ltac:(lra) (proj1 Hx) (proj2 Hx)) as [y [Hon _]].
      exists (x, y). split; [exact Hon | reflexivity].
Qed.

(* 連結な x 単調 sub は、始終点間の各 x 座標を通る。 *)
Lemma x_monotone_sub_has_point :
  forall sub x,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    rx0 (rect_of sub) <= x <= rx1 (rect_of sub) ->
    exists q, onSegmentlist sub q /\ fst q = x.
Proof.
  intros sub x Hne. destruct sub as [|a tail]; [contradiction|].
  clear Hne. revert a x.
  induction tail as [|b tail IH]; intros a x Hconn Hmono Hx.
  - destruct (segment_has_point_at_x a x Hx) as [q [Hon Hqx]].
    exists q. split; [exists a; split; [now left | exact Hon] | exact Hqx].
  - assert (Hab : term a = init b).
    { apply (Hconn 0%nat a b); reflexivity. }
    assert (HconnTail : connected (b :: tail)).
    { intros i s1 s2 H1 H2.
      apply (Hconn (S i) s1 s2); simpl; assumption. }
    assert (HmonoTail : x_monotone_segs (b :: tail)).
    { intros s Hs. apply Hmono. now right. }
    pose proof (x_monotone_rect_x_bounds
                  (a :: b :: tail) ltac:(discriminate) Hconn Hmono)
      as [Hleft Hright].
    change (rx0 (rect_of (a :: b :: tail)) = fst (init a)) in Hleft.
    assert (Hlast :
      last_segment (a :: b :: tail) = last_segment (b :: tail)).
    { change (last_segment ([a] ++ b :: tail) = last_segment (b :: tail)).
      apply last_app_nonnil. discriminate. }
    rewrite Hleft, Hright in Hx.
    destruct (Rle_dec x (fst (term a))) as [Hxa | Hax].
    + assert (Hsingle :
          rx0 (rect_of [a]) <= x <= rx1 (rect_of [a])).
      { pose proof (Hmono a ltac:(now left)) as Ha.
        unfold x_monotone_seg, init_x, term_x in Ha.
        change (Rmin (fst (init a)) (fst (term a)) <= x <=
                Rmax (fst (init a)) (fst (term a))).
        rewrite Rmin_left by lra. rewrite Rmax_right by lra.
        lra. }
      destruct (segment_has_point_at_x a x Hsingle) as [q [Hon Hqx]].
      exists q. split.
      * exists a. split; [now left | exact Hon].
      * exact Hqx.
    + assert (Htailx :
          rx0 (rect_of (b :: tail)) <= x <=
          rx1 (rect_of (b :: tail))).
      { pose proof (x_monotone_rect_x_bounds
                      (b :: tail) ltac:(discriminate)
                      HconnTail HmonoTail) as [HtailLeft HtailRight].
        change (rx0 (rect_of (b :: tail)) = fst (init b)) in HtailLeft.
        rewrite HtailLeft, HtailRight.
        rewrite Hlast in Hx.
        rewrite Hab in Hax. lra. }
      destruct (IH b x HconnTail HmonoTail Htailx)
        as [q [[s [Hs Hon]] Hqx]].
      exists q. split.
      * exists s. split; [now right | exact Hon].
      * exact Hqx.
Qed.

(* x が始点から終点へ増えるセグメント上では、各点の x もその間にある。 *)
Lemma x_monotone_segment_point_bounds :
  forall s p,
    x_monotone_seg s ->
    onSegment s p ->
    init_x s <= fst p <= term_x s.
Proof.
  intros seg p Hmono [t [[Ht0 Ht1] Hpoint]]. subst p.
  unfold x_monotone_seg, init_x, term_x in Hmono.
  destruct (x_strictly_monotone_seg seg) as [Hinc | Hdec].
  - split.
    + destruct (Req_dec t 0) as [-> | Ht]; [right; reflexivity |].
      left. apply Hinc. lra.
    + destruct (Req_dec t 1) as [-> | Ht]; [right; reflexivity |].
      left. apply Hinc. lra.
  - exfalso.
    pose proof (Hdec 0 1 ltac:(lra)) as Hbackwards.
    change (fst (point seg 0) < fst (point seg 1)) in Hmono.
    change (fst (point seg 1) < fst (point seg 0)) in Hbackwards.
    lra.
Qed.

(* 一つの x 単調セグメントは同じ x 座標を二度取らない。 *)
Lemma x_monotone_segment_same_x_unique :
  forall s p q,
    x_monotone_seg s ->
    onSegment s p ->
    onSegment s q ->
    fst p = fst q ->
    p = q.
Proof.
  intros seg p q Hmono
    [tp [[Htp0 Htp1] Hpointp]]
    [tq [[Htq0 Htq1] Hpointq]] Hx.
  subst p q.
  destruct (x_strictly_monotone_seg seg) as [Hinc | Hdec];
  destruct (total_order_T tp tq) as [[Hlt | Heq] | Hgt].
  - pose proof (Hinc tp tq ltac:(lra)) as Hstrict. lra.
  - now subst tq.
  - pose proof (Hinc tq tp ltac:(lra)) as Hstrict. lra.
  - pose proof (Hdec tp tq ltac:(lra)) as Hstrict. lra.
  - now subst tq.
  - pose proof (Hdec tq tp ltac:(lra)) as Hstrict. lra.
Qed.

(* 連結な x 単調列上の全点は、列全体の始終点 x の間にある。 *)
Lemma connected_x_monotone_point_bounds :
  forall ls p,
    ls <> [] ->
    connected ls ->
    x_monotone_segs ls ->
    onSegmentlist ls p ->
    init_x (hd_segment ls) <= fst p <= term_x (last_segment ls).
Proof.
  induction ls as [|a tail IH]; intros p Hne Hconn Hmono
    [seg [Hin Hon]]; [contradiction |].
  destruct tail as [|b rest].
  - simpl in Hin. destruct Hin as [<- | Hin]; [|contradiction].
    simpl. apply x_monotone_segment_point_bounds; [|exact Hon].
    apply Hmono. now left.
  - assert (Hab : term a = init b).
    { apply (Hconn 0%nat a b); reflexivity. }
    assert (HconnTail : connected (b :: rest)).
    { intros i s1 s2 H1 H2.
      apply (Hconn (S i) s1 s2); simpl; assumption. }
    assert (HmonoTail : x_monotone_segs (b :: rest)).
    { intros s Hs. apply Hmono. now right. }
    assert (Hlast :
      last_segment (a :: b :: rest) = last_segment (b :: rest)).
    { change (last_segment ([a] ++ b :: rest) = last_segment (b :: rest)).
      apply last_app_nonnil. discriminate. }
    destruct Hin as [Hseg | Hseg].
    + subst seg.
      pose proof (x_monotone_segment_point_bounds a p
                    (Hmono a ltac:(now left)) Hon) as [Hleft Hpa].
      pose proof (connected_x_monotone_endpoints
                    (b :: rest) ltac:(discriminate)
                    HconnTail HmonoTail) as Htail.
      simpl. rewrite Hlast. split; [exact Hleft |].
      change (fst p <= fst (term a)) in Hpa.
      change (fst (init b) < fst (term (last_segment (b :: rest))))
        in Htail.
      change (fst p <= fst (term (last_segment (b :: rest)))).
      rewrite Hab in Hpa. lra.
    + pose proof (IH p ltac:(discriminate) HconnTail HmonoTail
                    (ex_intro _ seg (conj Hseg Hon))) as [Hbp Hright].
      pose proof (Hmono a ltac:(now left)) as Ha.
      simpl. rewrite Hlast. split; [|exact Hright].
      change (fst (init a) < fst (term a)) in Ha.
      change (fst (init b) <= fst p) in Hbp.
      change (fst (init a) <= fst p).
      rewrite Hab in Ha. lra.
Qed.

Lemma x_monotone_sub_point_rect_bounds :
  forall sub p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    onSegmentlist sub p ->
    rx0 (rect_of sub) <= fst p <= rx1 (rect_of sub).
Proof.
  intros sub p Hne Hconn Hmono Hp.
  pose proof (connected_x_monotone_point_bounds
                sub p Hne Hconn Hmono Hp) as Hbounds.
  pose proof (x_monotone_rect_x_bounds sub Hne Hconn Hmono)
    as [Hleft Hright].
  rewrite Hleft, Hright. exact Hbounds.
Qed.

(* 補正開始点が sub より外側なら、その側の補正は sub 上で発火しない。 *)
Lemma outside_patch_start_does_not_force_on_sub :
  forall sub p patch,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    onSegmentlist sub p ->
    ((patch_side patch = CutLeft
      /\ patch_start_x patch <= rx0 (rect_of sub))
     \/ (patch_side patch = CutRight
         /\ rx1 (rect_of sub) <= patch_start_x patch)) ->
    patch_does_not_force_at patch p.
Proof.
  intros sub p [side start trace force inclusive]
    Hne Hconn Hmono Hp Houtside.
  left. unfold patch_active_at; simpl.
  pose proof (x_monotone_sub_point_rect_bounds
                sub p Hne Hconn Hmono Hp) as [Hleft Hright].
  destruct side; simpl in Houtside |- *.
  - destruct Houtside as [[_ Hstart] | [Hbad _]]; [|discriminate].
    intro Hactive. apply (Rlt_irrefl (fst p)).
    eapply Rlt_le_trans; [exact Hactive |].
    eapply Rle_trans; [exact Hstart | exact Hleft].
  - destruct Houtside as [[Hbad _] | [_ Hstart]]; [discriminate |].
    intro Hactive. apply (Rlt_irrefl start).
    eapply Rlt_le_trans; [exact Hactive |].
    eapply Rle_trans; [exact Hright | exact Hstart].
Qed.

Lemma singleton_head_left_patch_does_not_force_on_sub :
  forall s sub r p patch,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    connected ([s] ++ sub ++ r) ->
    onSegmentlist sub p ->
    make_end_patch [s] r HeadEnd CutLeft = Some patch ->
    patch_does_not_force_at patch p.
Proof.
  intros s sub r p patch Hne Hconn Hmono Hwhole Hp Hpatch.
  destruct (make_end_patch_side_and_start
              [s] r HeadEnd CutLeft patch Hpatch)
    as [seg [Hseg [Hside Hstart]]].
  simpl in Hseg. injection Hseg as <-. simpl in Hstart.
  pose proof (connected_app_junction [s] (sub ++ r)
                Hwhole ltac:(discriminate)
                ltac:(destruct sub; [contradiction | discriminate])) as Hjoin.
  simpl in Hjoin.
  destruct sub as [|a tail]; [contradiction |].
  change (term s = init a) in Hjoin.
  pose proof (x_monotone_rect_x_bounds
                (a :: tail) ltac:(discriminate) Hconn Hmono) as [Hleft _].
  apply (outside_patch_start_does_not_force_on_sub
           (a :: tail) p patch); try assumption.
  left. split; [exact Hside |].
  rewrite Hstart, Hjoin, Hleft. reflexivity.
Qed.

Lemma singleton_last_right_patch_does_not_force_on_sub :
  forall l sub s p patch,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    connected (l ++ sub ++ [s]) ->
    onSegmentlist sub p ->
    make_end_patch l [s] LastEnd CutRight = Some patch ->
    patch_does_not_force_at patch p.
Proof.
  intros l sub s p patch Hne Hconn Hmono Hwhole Hp Hpatch.
  destruct (make_end_patch_side_and_start
              l [s] LastEnd CutRight patch Hpatch)
    as [seg [Hseg [Hside Hstart]]].
  simpl in Hseg. injection Hseg as <-. simpl in Hstart.
  change (patch_start_x patch = fst (init s)) in Hstart.
  assert (Hwhole' : connected ((l ++ sub) ++ [s])).
  { replace ((l ++ sub) ++ [s]) with (l ++ (sub ++ [s])) by
      apply app_assoc.
    exact Hwhole. }
  pose proof (connected_app_junction (l ++ sub) [s]
                Hwhole'
                ltac:(intro Hnil; apply app_eq_nil in Hnil as [_ Hsub]; contradiction)
                ltac:(discriminate)) as Hjoin.
  simpl in Hjoin.
  rewrite last_app_nonnil in Hjoin by exact Hne.
  change (term (last_segment sub) = init s) in Hjoin.
  pose proof (x_monotone_rect_x_bounds sub Hne Hconn Hmono) as [_ Hright].
  apply (outside_patch_start_does_not_force_on_sub sub p patch);
    try assumption.
  right. split; [exact Hside |].
  rewrite Hstart, <- Hjoin, Hright. reflexivity.
Qed.

(* 左側の先頭補正で先頭が二本以上ある場合は、疎性と先頭延長線の
   交差順序を結ぶ幾何が必要になる。 *)
Lemma multi_head_left_patch_does_not_force_on_sub :
  forall a b tail sub r p patch,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding ((a :: b :: tail) ++ sub ++ r) ->
    connected ((a :: b :: tail) ++ sub ++ r) ->
    onSegmentlist sub p ->
    make_end_patch (a :: b :: tail) r HeadEnd CutLeft = Some patch ->
    patch_does_not_force_at patch p.
Admitted.

(* 先頭の右側補正では、延長線と更新済み右境界の相対位置が本質的。 *)
Lemma nonempty_head_right_patch_does_not_force_on_sub :
  forall a tail sub r p patch,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding ((a :: tail) ++ sub ++ r) ->
    connected ((a :: tail) ++ sub ++ r) ->
    onSegmentlist sub p ->
    make_end_patch (a :: tail) r HeadEnd CutRight = Some patch ->
    patch_does_not_force_at patch p.
Admitted.

(* 末尾の左側補正は上の双対で、更新済み左境界との比較を要する。 *)
Lemma nonempty_last_left_patch_does_not_force_on_sub :
  forall l sub a tail p patch,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ (a :: tail)) ->
    connected (l ++ sub ++ (a :: tail)) ->
    onSegmentlist sub p ->
    make_end_patch l (a :: tail) LastEnd CutLeft = Some patch ->
    patch_does_not_force_at patch p.
Admitted.

(* 右側の末尾補正で末尾が二本以上ある場合の双対的な幾何。 *)
Lemma multi_last_right_patch_does_not_force_on_sub :
  forall l sub a b tail p patch,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ (a :: b :: tail)) ->
    connected (l ++ sub ++ (a :: b :: tail)) ->
    onSegmentlist sub p ->
    make_end_patch l (a :: b :: tail) LastEnd CutRight = Some patch ->
    patch_does_not_force_at patch p.
Admitted.

(* end、左右、空/singleton/一般列を分けると、未証明なのは上の四つの
   延長線・更新境界の幾何だけになる。 *)
Lemma end_patch_does_not_force_on_sub :
  forall l sub r p k side patch,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    onSegmentlist sub p ->
    make_end_patch l r k side = Some patch ->
    patch_does_not_force_at patch p.
Proof.
  intros l sub r p k side patch Hne Hconn Hmono Hsparse Hwhole Hp Hpatch.
  destruct k, side.
  - destruct l as [|a tail].
    + unfold make_end_patch, end_segment in Hpatch. discriminate.
    + destruct tail as [|b tail].
      * eapply singleton_head_left_patch_does_not_force_on_sub; eauto.
      * eapply multi_head_left_patch_does_not_force_on_sub; eauto.
  - destruct l as [|a tail].
    + unfold make_end_patch, end_segment in Hpatch. discriminate.
    + eapply nonempty_head_right_patch_does_not_force_on_sub; eauto.
  - destruct r as [|a tail].
    + unfold make_end_patch, end_segment in Hpatch. discriminate.
    + eapply nonempty_last_left_patch_does_not_force_on_sub; eauto.
  - destruct r as [|a tail].
    + unfold make_end_patch, end_segment in Hpatch. discriminate.
    + destruct tail as [|b tail].
      * eapply singleton_last_right_patch_does_not_force_on_sub; eauto.
      * eapply multi_last_right_patch_does_not_force_on_sub; eauto.
Qed.

Lemma end_patches_do_not_force_on_sub :
  forall l sub r,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    forall p,
      onSegmentlist sub p ->
      end_patches_do_not_force_at l r p.
Proof.
  intros l sub r Hne Hconn Hmono Hsparse Hwhole p Hp
    k side patch Hpatch.
  eapply end_patch_does_not_force_on_sub; eauto.
Qed.

(* 連結な x 単調列は各 x 座標に高々一つの点を持つ。 *)
Lemma x_monotone_sub_point_unique :
  forall sub p q,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    onSegmentlist sub p ->
    onSegmentlist sub q ->
    fst p = fst q ->
    p = q.
Proof.
  induction sub as [|a tail IH]; intros p q Hne Hconn Hmono
    [sp [Hsp Hp]] [sq [Hsq Hq]] Hx; [contradiction |].
  destruct tail as [|b rest].
  - simpl in Hsp, Hsq.
    destruct Hsp as [<- | Hsp], Hsq as [<- | Hsq];
      try contradiction.
    eapply x_monotone_segment_same_x_unique; eauto.
    apply Hmono. now left.
  - assert (Hab : term a = init b).
    { apply (Hconn 0%nat a b); reflexivity. }
    assert (HconnTail : connected (b :: rest)).
    { intros i s1 s2 H1 H2.
      apply (Hconn (S i) s1 s2); simpl; assumption. }
    assert (HmonoTail : x_monotone_segs (b :: rest)).
    { intros s Hs. apply Hmono. now right. }
    destruct Hsp as [Hsp | Hsp], Hsq as [Hsq | Hsq].
    + subst sp sq. eapply x_monotone_segment_same_x_unique; eauto.
      apply Hmono. now left.
    + subst sp.
      pose proof (x_monotone_segment_point_bounds a p
                    (Hmono a ltac:(now left)) Hp) as [_ Hpa].
      pose proof (connected_x_monotone_point_bounds
                    (b :: rest) q ltac:(discriminate)
                    HconnTail HmonoTail
                    (ex_intro _ sq (conj Hsq Hq))) as [Hbq _].
      change (fst p <= fst (term a)) in Hpa.
      change (fst (init b) <= fst q) in Hbq.
      assert (Hpx : fst p = fst (term a)) by
        (rewrite <- Hab in Hbq; lra).
      assert (Hqx : fst q = fst (init b)) by
        (rewrite <- Hab; lra).
      assert (Hpterm : p = term a).
      { exact (x_monotone_segment_same_x_unique a p (term a)
                 (Hmono a ltac:(now left)) Hp (onTerm a) Hpx). }
      assert (Hqinit : q = init b).
      { eapply (IH q (init b) ltac:(discriminate)
                  HconnTail HmonoTail).
        - exists sq. now split.
        - exists b. split; [now left | apply onInit].
        - exact Hqx. }
      now rewrite Hpterm, Hqinit, Hab.
    + subst sq.
      pose proof (connected_x_monotone_point_bounds
                    (b :: rest) p ltac:(discriminate)
                    HconnTail HmonoTail
                    (ex_intro _ sp (conj Hsp Hp))) as [Hbp _].
      pose proof (x_monotone_segment_point_bounds a q
                    (Hmono a ltac:(now left)) Hq) as [_ Hqa].
      change (fst (init b) <= fst p) in Hbp.
      change (fst q <= fst (term a)) in Hqa.
      assert (Hqx : fst q = fst (term a)) by
        (rewrite <- Hab in Hbp; lra).
      assert (Hpx : fst p = fst (init b)) by
        (rewrite <- Hab; lra).
      assert (Hqterm : q = term a).
      { exact (x_monotone_segment_same_x_unique a q (term a)
                 (Hmono a ltac:(now left)) Hq (onTerm a) Hqx). }
      assert (Hpinit : p = init b).
      { eapply (IH p (init b) ltac:(discriminate)
                  HconnTail HmonoTail).
        - exists sp. now split.
        - exists b. split; [now left | apply onInit].
        - exact Hpx. }
      now rewrite Hpinit, Hqterm, Hab.
    + eapply (IH p q ltac:(discriminate) HconnTail HmonoTail).
      * exists sp. now split.
      * exists sq. now split.
      * exact Hx.
Qed.

Lemma choose_sub_y_eq :
  forall sub p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    onSegmentlist sub p ->
    choose_sub_y sub (fst p) = snd p.
Proof.
  intros sub p Hne Hconn Hmono Hp.
  destruct p as [x y]. simpl in *.
  assert (Hex : exists y0, onSegmentlist sub (x, y0)).
  { exists y. exact Hp. }
  pose proof (choose_sub_y_spec sub x Hex) as Hchosen.
  pose proof (x_monotone_sub_point_unique sub
                (x, choose_sub_y sub x) (x, y)
                Hne Hconn Hmono Hchosen Hp eq_refl) as Heq.
  now injection Heq.
Qed.

Lemma simple_height_on_sub :
  forall sub p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    onSegmentlist sub p ->
    simple_height sub (fst p) = snd p.
Proof.
  intros sub p Hne Hconn Hmono Hp.
  pose proof (connected_x_monotone_point_bounds
                sub p Hne Hconn Hmono Hp) as Hbounds.
  pose proof (x_monotone_rect_x_bounds sub Hne Hconn Hmono)
    as [Hleft Hright].
  unfold simple_height.
  destruct (Rlt_dec (fst p) (rx0 (rect_of sub))) as [Hlt | Hnlt].
  - rewrite Hleft in Hlt. unfold init_x in Hbounds. lra.
  - destruct (Rlt_dec (rx1 (rect_of sub)) (fst p)) as [Hlt | Hnlt'].
    + rewrite Hright in Hlt. unfold term_x in Hbounds. lra.
    + now apply choose_sub_y_eq.
Qed.

Lemma simple_classify_sub_fixed :
  forall sub p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    onSegmentlist sub p ->
    state_region (simple_classify_state sub) p = RegFix.
Proof.
  intros sub p Hne Hconn Hmono Hp.
  unfold simple_classify_state, classify_at_height; simpl.
  rewrite (simple_height_on_sub sub p Hne Hconn Hmono Hp).
  destruct (Rlt_dec (snd p) (snd p)); [lra |].
  destruct (Rlt_dec (snd p) (snd p)); [lra | reflexivity].
Qed.

(* sub 上で各 end 補正が発火しなければ、最終分類でも sub は固定される。 *)
Lemma classify_sub_fixed_from_end_patch_safety :
  forall l sub r p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    onSegmentlist sub p ->
    end_patches_do_not_force_at l r p ->
    classify l sub r p = RegFix.
Proof.
  intros l sub r p Hne Hconn Hmono Hp Hsafe.
  rewrite (classify_eq_simple_when_end_patches_do_not_force
             l sub r p Hsafe).
  now apply simple_classify_sub_fixed.
Qed.

Lemma classify_without_sides_sub_fixed :
  forall sub p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    onSegmentlist sub p ->
    classify [] sub [] p = RegFix.
Proof.
  intros sub p Hne Hconn Hmono Hp.
  rewrite classify_without_sides_eq_simple.
  now apply simple_classify_sub_fixed.
Qed.

Lemma classify_at_height_same_x_monotone :
  forall height p q,
    fst p = fst q ->
    snd p < snd q ->
    region_at_or_above
      (classify_at_height height q)
      (classify_at_height height p).
Proof.
  intros height [xp yp] [xq yq] Hx Hy. simpl in Hx, Hy. subst xq.
  unfold classify_at_height. simpl.
  destruct (Rlt_dec yp (height xp)) as [Hpdown | Hpdown].
  - destruct (Rlt_dec yq (height xp)) as [Hqdown | Hqdown].
    + now left.
    + destruct (Rlt_dec (height xp) yq) as [Hqup | Hqup].
      * right. apply RegUp_above_Down.
      * right. apply RegFix_above_Down.
  - destruct (Rlt_dec (height xp) yp) as [Hpup | Hpup].
    + destruct (Rlt_dec yq (height xp)) as [Hqdown | Hqdown]; [lra |].
      destruct (Rlt_dec (height xp) yq) as [Hqup | Hqup]; [now left | lra].
    + destruct (Rlt_dec yq (height xp)) as [Hqdown | Hqdown]; [lra |].
      destruct (Rlt_dec (height xp) yq) as [Hqup | Hqup].
      * right. apply RegUp_above_Fix.
      * lra.
Qed.

Lemma simple_classify_same_x_monotone :
  forall sub p q,
    fst p = fst q ->
    snd p < snd q ->
    region_at_or_above
      (state_region (simple_classify_state sub) q)
      (state_region (simple_classify_state sub) p).
Proof.
  intros sub p q Hx Hy.
  exact (classify_at_height_same_x_monotone
           (simple_height sub) p q Hx Hy).
Qed.

Definition vertically_monotone_region (f : Point -> Region) : Prop :=
  forall p q,
    fst p = fst q ->
    snd p < snd q ->
    region_at_or_above (f q) (f p).

Lemma apply_region_patch_preserves_vertical_monotonicity :
  forall old patch,
    vertically_monotone_region old ->
    vertically_monotone_region (apply_region_patch old patch).
Proof.
  intros old [side start trace force inclusive] Hold
    [xp yp] [xq yq] Hx Hy.
  simpl in Hx, Hy. subst xq.
  unfold apply_region_patch. simpl.
  destruct (patch_active_dec
              {| patch_side := side;
                 patch_start_x := start;
                 patch_reference := trace;
                 patch_force := force;
                 patch_inclusive := inclusive |} xp) as [Hactive | Hinactive].
  2: apply Hold; simpl; lra.
  destruct (trace_height trace xp) as [reference_y |] eqn:Hheight.
  2: apply Hold; simpl; lra.
  destruct force, inclusive;
    cbn [patch_forces_dec patch_forces_at forced_region].
  - destruct (Rle_dec reference_y yp) as [Hp | Hp];
    destruct (Rle_dec reference_y yq) as [Hq | Hq]; simpl.
    + now left.
    + lra.
    + destruct (old (xp, yp));
        [right; apply RegUp_above_Fix | now left | right; apply RegUp_above_Down].
    + apply Hold; simpl; lra.
  - destruct (Rlt_dec reference_y yp) as [Hp | Hp];
    destruct (Rlt_dec reference_y yq) as [Hq | Hq]; simpl.
    + now left.
    + lra.
    + destruct (old (xp, yp));
        [right; apply RegUp_above_Fix | now left | right; apply RegUp_above_Down].
    + apply Hold; simpl; lra.
  - destruct (Rle_dec yp reference_y) as [Hp | Hp];
    destruct (Rle_dec yq reference_y) as [Hq | Hq]; simpl.
    + now left.
    + destruct (old (xp, yq));
        [right; apply RegFix_above_Down | right; apply RegUp_above_Down | now left].
    + lra.
    + apply Hold; simpl; lra.
  - destruct (Rlt_dec yp reference_y) as [Hp | Hp];
    destruct (Rlt_dec yq reference_y) as [Hq | Hq]; simpl.
    + now left.
    + destruct (old (xp, yq));
        [right; apply RegFix_above_Down | right; apply RegUp_above_Down | now left].
    + lra.
    + apply Hold; simpl; lra.
Qed.

Lemma apply_patch_preserves_vertical_monotonicity :
  forall st patch,
    vertically_monotone_region (state_region st) ->
    vertically_monotone_region (state_region (apply_patch st patch)).
Proof.
  intros [region height] patch Hmono. simpl in *.
  now apply apply_region_patch_preserves_vertical_monotonicity.
Qed.

Lemma simple_state_vertically_monotone :
  forall sub,
    vertically_monotone_region (state_region (simple_classify_state sub)).
Proof.
  intros sub p q Hx Hy.
  now apply simple_classify_same_x_monotone.
Qed.

Lemma apply_end_at_preserves_vertical_monotonicity :
  forall st l r k side,
    vertically_monotone_region (state_region st) ->
    vertically_monotone_region
      (state_region (apply_end_at st l r k side)).
Proof.
  intros st l r k side Hmono. unfold apply_end_at.
  destruct (make_end_patch l r k side) as [patch |];
    [now apply apply_patch_preserves_vertical_monotonicity | exact Hmono].
Qed.

Lemma process_end_preserves_vertical_monotonicity :
  forall st l sub r k side,
    vertically_monotone_region (state_region st) ->
    vertically_monotone_region
      (state_region (process_end st l sub r k side)).
Proof.
  intros st l sub r k side Hmono. unfold process_end.
  destruct (nearest_end_crossing st l sub r k side);
    [now apply apply_end_at_preserves_vertical_monotonicity | exact Hmono].
Qed.

Lemma process_both_ends_preserves_vertical_monotonicity :
  forall st l sub r side,
    vertically_monotone_region (state_region st) ->
    vertically_monotone_region
      (state_region (process_both_ends_on_side st l sub r side)).
Proof.
  intros st l sub r side Hmono.
  unfold process_both_ends_on_side.
  destruct (nearest_end_crossing st l sub r HeadEnd side) as [ph |];
  destruct (nearest_end_crossing st l sub r LastEnd side) as [pl |].
  - destruct (crossing_closer_dec side ph pl).
    + apply process_end_preserves_vertical_monotonicity.
      now apply apply_end_at_preserves_vertical_monotonicity.
    + apply process_end_preserves_vertical_monotonicity.
      now apply apply_end_at_preserves_vertical_monotonicity.
  - now apply apply_end_at_preserves_vertical_monotonicity.
  - now apply apply_end_at_preserves_vertical_monotonicity.
  - exact Hmono.
Qed.

Lemma build_classify_state_vertically_monotone :
  forall l sub r,
    vertically_monotone_region
      (state_region (build_classify_state l sub r)).
Proof.
  intros l sub r. unfold build_classify_state.
  apply process_both_ends_preserves_vertical_monotonicity.
  apply process_both_ends_preserves_vertical_monotonicity.
  apply simple_state_vertically_monotone.
Qed.

Lemma classify_same_x_monotone :
  forall l sub r p q,
    fst p = fst q ->
    snd p < snd q ->
    region_at_or_above
      (classify l sub r q) (classify l sub r p).
Proof.
  intros l sub r p q Hx Hy.
  exact (build_classify_state_vertically_monotone l sub r p q Hx Hy).
Qed.

(* 補正後の Fix は元の単純分類でも Fix なので、同じ x の Fix 点より
   真に上（下）の非 Fix 点は最終分類でも Up（Down）になる。 *)
Lemma classify_above_fixed_is_up :
  forall l sub r p q,
    fst p = fst q ->
    snd q < snd p ->
    classify l sub r q = RegFix ->
    state_region (simple_classify_state sub) p <> RegFix ->
    classify l sub r p = RegUp.
Proof.
  intros l sub r p q Hx Hy Hq Hsimple.
  pose proof (classify_same_x_monotone l sub r q p
                ltac:(now symmetry) Hy) as Horder.
  rewrite Hq in Horder.
  destruct (classify l sub r p) eqn:Hp.
  - exfalso. apply Hsimple.
    now apply (classify_fix_implies_simple_fix l sub r p).
  - reflexivity.
  - destruct Horder as [Heq | Habove]; [discriminate | inversion Habove].
Qed.

Lemma classify_below_fixed_is_down :
  forall l sub r p q,
    fst p = fst q ->
    snd p < snd q ->
    classify l sub r q = RegFix ->
    state_region (simple_classify_state sub) p <> RegFix ->
    classify l sub r p = RegDown.
Proof.
  intros l sub r p q Hx Hy Hq Hsimple.
  pose proof (classify_same_x_monotone l sub r p q Hx Hy) as Horder.
  rewrite Hq in Horder.
  destruct (classify l sub r p) eqn:Hp.
  - exfalso. apply Hsimple.
    now apply (classify_fix_implies_simple_fix l sub r p).
  - destruct Horder as [Heq | Habove]; [discriminate | inversion Habove].
  - reflexivity.
Qed.

(* sub 固定性は、四つの end/side 場合に分けた補正非発火補題から従う。 *)
Lemma classified_sub_fixed_from_construction :
  forall l sub r,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    forall p, onSegmentlist sub p -> classify l sub r p = RegFix.
Proof.
  intros l sub r Hne Hconn Hmono Hsparse Hwhole p Hp.
  eapply classify_sub_fixed_from_end_patch_safety; eauto.
  now apply (end_patches_do_not_force_on_sub
               l sub r Hne Hconn Hmono Hsparse Hwhole p Hp).
Qed.

(* sub と同じ x の点そのものの分類は、sub の固定性と鉛直単調性だけで
   決まる。セグメント両端への伝播は別の幾何補題で扱う。 *)
Lemma classify_above_sub_at_x :
  forall l sub r p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    above_sub_at_x sub p ->
    classify l sub r p = RegUp.
Proof.
  intros l sub r p Hne Hconn Hmono Hsparse Hwhole
    [q [Hq [Hx Hy]]].
  eapply classify_above_fixed_is_up with (q := q); eauto.
  - now apply (classified_sub_fixed_from_construction
                 l sub r Hne Hconn Hmono Hsparse Hwhole).
  - assert (Hheight : simple_height sub (fst p) = snd q).
    { rewrite Hx. now apply simple_height_on_sub. }
    unfold simple_classify_state, classify_at_height; simpl.
    rewrite Hheight.
    destruct (Rlt_dec (snd p) (snd q)); [lra |].
    destruct (Rlt_dec (snd q) (snd p)); [discriminate | lra].
Qed.

Lemma classify_below_sub_at_x :
  forall l sub r p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    below_sub_at_x sub p ->
    classify l sub r p = RegDown.
Proof.
  intros l sub r p Hne Hconn Hmono Hsparse Hwhole
    [q [Hq [Hx Hy]]].
  eapply classify_below_fixed_is_down with (q := q); eauto.
  - now apply (classified_sub_fixed_from_construction
                 l sub r Hne Hconn Hmono Hsparse Hwhole).
  - assert (Hheight : simple_height sub (fst p) = snd q).
    { rewrite Hx. now apply simple_height_on_sub. }
    unfold simple_classify_state, classify_at_height; simpl.
    rewrite Hheight.
    destruct (Rlt_dec (snd p) (snd q)); [discriminate |].
    destruct (Rlt_dec (snd q) (snd p)); [lra | lra].
Qed.

(* 各セグメントと現在の境界の交差順序。primitive の8場合に帰着するが、
   更新済み境界を横切る場合の中間値議論を残す。 *)
Lemma classified_segment_endpoints_monotone_from_construction :
  forall l sub r,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    forall seg,
      In seg (l ++ sub ++ r) ->
      (snd (init seg) < snd (term seg) ->
        region_at_or_above
          (classify l sub r (term seg)) (classify l sub r (init seg)))
      /\
      (snd (term seg) < snd (init seg) ->
        region_at_or_above
          (classify l sub r (init seg)) (classify l sub r (term seg))).
Admitted.

(* 非隣接長方形の上下分離を分類順序へ移す部分。 *)
Lemma classified_nonadjacent_endpoint_order_from_construction :
  forall l sub r,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    forall i j s t ps pt,
      nth_error (l ++ sub ++ r) i = Some s ->
      nth_error (l ++ sub ++ r) j = Some t ->
      (S i < j \/ S j < i)%nat ->
      segment_x_ranges_overlap s t ->
      endpoint_of_seg s ps ->
      endpoint_of_seg t pt ->
      ~ onSegmentlist sub ps ->
      ~ onSegmentlist sub pt ->
      snd ps <= snd pt ->
      region_at_or_above (classify l sub r pt) (classify l sub r ps).
Admitted.

(* sub の同じ x に点を持つ非隣接セグメントについて、疎性から長方形の
   上下どちら側に全端点があるかを確定する部分。 *)
Lemma classified_segment_at_sub_x_from_construction :
  forall l sub r,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    forall seg p,
      In seg (nonadjacent_sides l r) ->
      onSegment seg p ->
      in_sub_x_range sub p ->
      (above_sub_at_x sub p ->
         classify l sub r (init seg) = RegUp
         /\ classify l sub r (term seg) = RegUp)
      /\
      (below_sub_at_x sub p ->
         classify l sub r (init seg) = RegDown
         /\ classify l sub r (term seg) = RegDown).
Admitted.

(* strict 延長線が sub の x 範囲へ入る場合の先頭基点分類。 *)
Lemma classified_head_extension_at_sub_x_from_construction :
  forall l sub r,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    forall p,
      onHead_extend_strict (l ++ sub ++ r) p ->
      rx0 (rect_of sub) <= fst p <= rx1 (rect_of sub) ->
      classify l sub r (init (hd_segment (l ++ sub ++ r))) = RegUp
      \/ classify l sub r (init (hd_segment (l ++ sub ++ r))) = RegDown.
Admitted.

(* 上の末尾側の双対。 *)
Lemma classified_last_extension_at_sub_x_from_construction :
  forall l sub r,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    forall p,
      onLast_extend_strict (l ++ sub ++ r) p ->
      rx0 (rect_of sub) <= fst p <= rx1 (rect_of sub) ->
      classify l sub r (term (last_segment (l ++ sub ++ r))) = RegUp
      \/ classify l sub r (term (last_segment (l ++ sub ++ r))) = RegDown.
Admitted.

(* 同じ x にある先頭・末尾延長線の上下順序。 *)
Lemma classified_head_last_extension_order_from_construction :
  forall l sub r,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    forall ph pl,
      onHead_extend (l ++ sub ++ r) ph ->
      onLast_extend (l ++ sub ++ r) pl ->
      fst ph = fst pl ->
      (snd ph < snd pl ->
         region_at_or_above
           (classify l sub r (term (last_segment (l ++ sub ++ r))))
           (classify l sub r (init (hd_segment (l ++ sub ++ r)))))
      /\
      (snd pl < snd ph ->
         region_at_or_above
           (classify l sub r (init (hd_segment (l ++ sub ++ r))))
           (classify l sub r (term (last_segment (l ++ sub ++ r))))).
Admitted.

(* 先頭延長線と一セグメントの交差順序。 *)
Lemma classified_head_segment_crossing_order_from_construction :
  forall l sub r,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    forall seg e0 q,
      In seg (l ++ sub ++ r) ->
      onSegment seg e0 ->
      onHead_extend_strict (l ++ sub ++ r) q ->
      fst e0 = fst q ->
      (snd q < snd e0 ->
         region_at_or_above
           (classify l sub r (init seg))
           (classify l sub r (init (hd_segment (l ++ sub ++ r))))
         /\ region_at_or_above
           (classify l sub r (term seg))
           (classify l sub r (init (hd_segment (l ++ sub ++ r)))))
      /\
      (snd e0 < snd q ->
         region_at_or_above
           (classify l sub r (init (hd_segment (l ++ sub ++ r))))
           (classify l sub r (init seg))
         /\ region_at_or_above
           (classify l sub r (init (hd_segment (l ++ sub ++ r))))
           (classify l sub r (term seg))).
Admitted.

(* 上の末尾側の双対。 *)
Lemma classified_last_segment_crossing_order_from_construction :
  forall l sub r,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    forall seg e0 q,
      In seg (l ++ sub ++ r) ->
      onSegment seg e0 ->
      onLast_extend_strict (l ++ sub ++ r) q ->
      fst e0 = fst q ->
      (snd q < snd e0 ->
         region_at_or_above
           (classify l sub r (init seg))
           (classify l sub r (term (last_segment (l ++ sub ++ r))))
         /\ region_at_or_above
           (classify l sub r (term seg))
           (classify l sub r (term (last_segment (l ++ sub ++ r)))))
      /\
      (snd e0 < snd q ->
         region_at_or_above
           (classify l sub r (term (last_segment (l ++ sub ++ r))))
           (classify l sub r (init seg))
         /\ region_at_or_above
           (classify l sub r (term (last_segment (l ++ sub ++ r))))
           (classify l sub r (term seg))).
Admitted.

(* 先頭補正表の8 primitive 場合から、異領域となる場合を傾き保存可能な
   四形に限定する部分。 *)
Lemma classified_head_slope_case_from_construction :
  forall l sub r,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    l <> [] ->
    classify l sub r (init (hd_segment l)) =
      classify l sub r (term (hd_segment l))
    \/ (classify l sub r (init (hd_segment l)) = RegUp
        /\ (embed (s, w, cx) (hd_segment l)
            \/ embed (s, e, cx) (hd_segment l)))
    \/ (classify l sub r (init (hd_segment l)) = RegDown
        /\ (embed (n, w, cc) (hd_segment l)
            \/ embed (n, e, cc) (hd_segment l))).
Admitted.

(* 末尾補正表の双対。 *)
Lemma classified_last_slope_case_from_construction :
  forall l sub r,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    r <> [] ->
    classify l sub r (init (last_segment r)) =
      classify l sub r (term (last_segment r))
    \/ (classify l sub r (term (last_segment r)) = RegUp
        /\ (embed (n, w, cx) (last_segment r)
            \/ embed (n, e, cx) (last_segment r)))
    \/ (classify l sub r (term (last_segment r)) = RegDown
        /\ (embed (s, w, cc) (last_segment r)
            \/ embed (s, e, cc) (last_segment r))).
Admitted.

(* 一括公理ではなく、上で分離した幾何補題から仕様を組み立てる。 *)
Lemma classify_spec :
  forall l sub r,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    ClassificationSpec l sub r.
Proof.
  intros l sub r Hne Hconn Hmono Hsparse Hwhole. constructor.
  - now apply classified_sub_fixed_from_construction.
  - now apply classified_segment_endpoints_monotone_from_construction.
  - now apply classified_nonadjacent_endpoint_order_from_construction.
  - now apply classified_segment_at_sub_x_from_construction.
  - now apply classified_head_extension_at_sub_x_from_construction.
  - now apply classified_last_extension_at_sub_x_from_construction.
  - now apply classified_head_last_extension_order_from_construction.
  - now apply classified_head_segment_crossing_order_from_construction.
  - now apply classified_last_segment_crossing_order_from_construction.
  - now apply classified_head_slope_case_from_construction.
  - now apply classified_last_slope_case_from_construction.
Qed.

(* 同じ x 上の具体的な分類単調性から、異なる領域の上下順序を逆に読む。 *)
Lemma classified_vertical_order :
  forall l sub r p q,
    fst p = fst q ->
    region_above (classify l sub r p) (classify l sub r q) ->
    snd q < snd p.
Proof.
  intros l sub r p q Hx Habove.
  destruct (total_order_T (snd q) (snd p)) as [[Hlt | Heq] | Hgt].
  - exact Hlt.
  - exfalso. apply (region_above_not_reverse _ _ Habove).
    left. f_equal. destruct p as [xp yp], q as [xq yq].
    simpl in Hx, Heq |- *. f_equal; lra.
  - exfalso. apply (region_above_not_reverse _ _ Habove).
    eapply classify_same_x_monotone; eauto.
Qed.

Definition shift (h : R) (g : Region) (p : Point) : Point :=
  match g with
  | RegFix  => p
  | RegUp   => (fst p, snd p + h)
  | RegDown => (fst p, snd p - h)
  end.

Definition region_translation (h : R) (g : Region) : Point :=
  match g with
  | RegFix => (0, 0)
  | RegUp => (0, h)
  | RegDown => (0, - h)
  end.

Lemma shift_as_translation :
  forall h g p, shift h g p = translate_pt (region_translation h g) p.
Proof.
  intros h g [x y]. destruct g; unfold shift, region_translation, translate_pt;
    simpl; f_equal; ring.
Qed.

Lemma shift_preserves_strict_vertical_order :
  forall h p q gp gq,
    0 < h ->
    snd p < snd q ->
    region_at_or_above gq gp ->
    snd (shift h gp p) < snd (shift h gq q).
Proof.
  intros h [xp yp] [xq yq] gp gq Hh Hy [Heq | Habove].
  - subst gq. destruct gp; simpl in Hy |- *; lra.
  - destruct Habove; simpl in Hy |- *; lra.
Qed.

Lemma shift_preserves_vertical_order :
  forall h p q gp gq,
    0 < h ->
    snd p <= snd q ->
    region_at_or_above gq gp ->
    snd (shift h gp p) <= snd (shift h gq q).
Proof.
  intros h [xp yp] [xq yq] gp gq Hh Hy [Heq | Habove].
  - subst gq. destruct gp; simpl in Hy |- *; lra.
  - destruct Habove; simpl in Hy |- *; lra.
Qed.

Definition operate_point
  (l sub r : list Segment) (h : R) (p : Point) : Point :=
  shift h (classify l sub r p) p.

Lemma shift_fst :
  forall h g p, fst (shift h g p) = fst p.
Proof. intros h g p. destruct g; reflexivity. Qed.

Lemma operate_point_fst :
  forall l sub r h p, fst (operate_point l sub r h p) = fst p.
Proof. intros. unfold operate_point. apply shift_fst. Qed.

(* 同じ x 上の分類単調性により、正の高さの上下移動は平面上で単射となる。 *)
Lemma operate_point_injective :
  forall l sub r h p q,
    0 < h ->
    operate_point l sub r h p = operate_point l sub r h q ->
    p = q.
Proof.
  intros l sub r h [xp yp] [xq yq]
    Hh Heq.
  destruct (classify l sub r (xp, yp)) eqn:Hrp;
  destruct (classify l sub r (xq, yq)) eqn:Hrq;
  unfold operate_point, shift in Heq; rewrite Hrp, Hrq in Heq;
  pose proof (f_equal fst Heq) as Hx;
  pose proof (f_equal snd Heq) as Hy; simpl in Hx, Hy.
  - f_equal; lra.
  - exfalso.
    pose proof (classified_vertical_order
                  l sub r (xq, yq) (xp, yp)
                  ltac:(symmetry; exact Hx)
                  ltac:(rewrite Hrq, Hrp; constructor)) as Horder.
    simpl in Horder. lra.
  - exfalso.
    pose proof (classified_vertical_order
                  l sub r (xp, yp) (xq, yq)
                  ltac:(exact Hx)
                  ltac:(rewrite Hrp, Hrq; constructor)) as Horder.
    simpl in Horder. lra.
  - exfalso.
    pose proof (classified_vertical_order
                  l sub r (xp, yp) (xq, yq)
                  ltac:(exact Hx)
                  ltac:(rewrite Hrp, Hrq; constructor)) as Horder.
    simpl in Horder. lra.
  - f_equal; lra.
  - exfalso.
    pose proof (classified_vertical_order
                  l sub r (xp, yp) (xq, yq)
                  ltac:(exact Hx)
                  ltac:(rewrite Hrp, Hrq; constructor)) as Horder.
    simpl in Horder. lra.
  - exfalso.
    pose proof (classified_vertical_order
                  l sub r (xq, yq) (xp, yp)
                  ltac:(symmetry; exact Hx)
                  ltac:(rewrite Hrq, Hrp; constructor)) as Horder.
    simpl in Horder. lra.
  - exfalso.
    pose proof (classified_vertical_order
                  l sub r (xq, yq) (xp, yp)
                  ltac:(symmetry; exact Hx)
                  ltac:(rewrite Hrq, Hrp; constructor)) as Horder.
    simpl in Horder. lra.
  - f_equal; lra.
Qed.

Lemma operate_point_RegFix :
  forall l sub r h p,
    classify l sub r p = RegFix ->
    operate_point l sub r h p = p.
Proof.
  intros l sub r h p H. unfold operate_point. now rewrite H.
Qed.

Lemma classify_sub_endpoint :
  forall l sub r p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    endpoint_of sub p ->
    classify l sub r p = RegFix.
Proof.
  intros l sub r p Hne Hconn Hmono Hsparse Hwhole Hend.
  exact (classified_sub_fixed
           l sub r
           (classify_spec l sub r Hne Hconn Hmono Hsparse Hwhole)
           p (endpoint_of_onSegmentlist sub p Hend)).
Qed.

Lemma operate_sub_endpoint :
  forall l sub r h p,
    sub <> [] ->
    connected sub ->
    x_monotone_segs sub ->
    sparse_embedding (l ++ sub ++ r) ->
    connected (l ++ sub ++ r) ->
    endpoint_of sub p ->
    operate_point l sub r h p = p.
Proof.
  intros l sub r h p Hne Hconn Hmono Hsparse Hwhole Hend.
  apply operate_point_RegFix.
  now apply classify_sub_endpoint.
Qed.
