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

Require Export Sparse.ClassifyGeometry.

(* ================================================================= *)
(* 端点の分類と上下移動 *)
(* ================================================================= *)

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
