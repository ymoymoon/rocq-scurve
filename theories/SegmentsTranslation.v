Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Lists.List.
Require Import Segment.
Require Import Reduction.
Import ListNotations.
Open Scope R_scope.


(* ================================================================= *)
(*  セグメントの幾何変換と端点指定                                   *)
(* ================================================================= *)

Definition Point := (R * R)%type.

(* セグメントが表す向き。具体的な Segment の実装が与える基本仕様。 *)
Parameter orn_seg : Segment -> Direction.


(* ----------------------------------------------------------------- *)
(*  90 度単位の回転                                                   *)
(* ----------------------------------------------------------------- *)

Inductive Rot : Type := R0 | R90 | R180 | R270.

Definition rot_pt (g : Rot) (p : Point) : Point :=
  match g with
  | R0   => p
  | R90  => (- snd p, fst p)
  | R180 => (- fst p, - snd p)
  | R270 => (snd p, - fst p)
  end.

Definition rot_inv (g : Rot) : Rot :=
  match g with R0 => R0 | R90 => R270 | R180 => R180 | R270 => R90 end.

Lemma rot_inv_inv : forall g, rot_inv (rot_inv g) = g.
Proof. destruct g; reflexivity. Qed.

Lemma rot_pt_inv : forall g p, rot_pt (rot_inv g) (rot_pt g p) = p.
Proof.
  intros g [x y]; destruct g; simpl; f_equal; ring.
Qed.

Parameter rot_seg : Rot -> Segment -> Segment.

(* 回転したセグメントは、各パラメータ点を同じだけ回転したもの。 *)
Axiom rot_seg_point :
  forall g s t, point (rot_seg g s) t = rot_pt g (point s t).

(* 90 度単位の回転はセグメントの Direction を保つ。 *)
Axiom rot_seg_orn :
  forall g s, orn_seg (rot_seg g s) = orn_seg s.

(* 逆回転により元のセグメントへ戻る。 *)
Axiom rot_inv_seg :
  forall g s, rot_seg (rot_inv g) (rot_seg g s) = s.

Lemma rot_seg_inv :
  forall g s, rot_seg g (rot_seg (rot_inv g) s) = s.
Proof.
  intros g s.
  pose proof (rot_inv_seg (rot_inv g) s) as H.
  now rewrite rot_inv_inv in H.
Qed.

Lemma rot_seg_init :
  forall g s, init (rot_seg g s) = rot_pt g (init s).
Proof. intros g s. unfold init. apply rot_seg_point. Qed.

Lemma rot_seg_term :
  forall g s, term (rot_seg g s) = rot_pt g (term s).
Proof. intros g s. unfold term. apply rot_seg_point. Qed.

Definition rot_segs (g : Rot) (ls : list Segment) : list Segment :=
  map (rot_seg g) ls.

Lemma rot_inv_segs : forall g ls, rot_segs (rot_inv g) (rot_segs g ls) = ls.
Proof.
  intros g ls. induction ls as [|s ls IH]; simpl; [reflexivity |].
  rewrite rot_inv_seg, IH. reflexivity.
Qed.

Lemma rot_segs_inv : forall g ls, rot_segs g (rot_segs (rot_inv g) ls) = ls.
Proof.
  intros g ls. induction ls as [|s ls IH]; simpl; [reflexivity |].
  rewrite rot_seg_inv, IH. reflexivity.
Qed.

Lemma rot_segs_app :
  forall g ls1 ls2, rot_segs g (ls1 ++ ls2) = rot_segs g ls1 ++ rot_segs g ls2.
Proof. intros. unfold rot_segs. apply map_app. Qed.

Lemma rot_segs_nonnil : forall g ls, ls <> [] -> rot_segs g ls <> [].
Proof.
  intros g [|s ls] H; [contradiction | discriminate].
Qed.

Lemma onSegment_rot :
  forall g s p, onSegment s p -> onSegment (rot_seg g s) (rot_pt g p).
Proof.
  intros g s p [t [Ht Hp]]. exists t. split; [exact Ht |].
  now rewrite rot_seg_point, Hp.
Qed.


(* ----------------------------------------------------------------- *)
(*  単一セグメントの平行移動                                         *)
(* ----------------------------------------------------------------- *)

Definition translate_pt (v p : Point) : Point :=
  (fst p + fst v, snd p + snd v).

Definition opposite_translation (v : Point) : Point :=
  (- fst v, - snd v).

Parameter translate_seg : (R * R) -> Segment -> Segment.

(* 平行移動したセグメントの各点は、元の点を同じベクトルだけ移したもの。 *)
Axiom translate_seg_point :
  forall v s t, point (translate_seg v s) t = translate_pt v (point s t).

(* 平行移動はセグメントの向きを変えない。 *)
Axiom translate_seg_orn :
  forall v s, orn_seg (translate_seg v s) = orn_seg s.

(* 逆向きの平行移動により元のセグメントへ戻る。 *)
Axiom translate_seg_inverse :
  forall v s, translate_seg (opposite_translation v) (translate_seg v s) = s.

Lemma translate_seg_init :
  forall v s, init (translate_seg v s) = translate_pt v (init s).
Proof. intros v s. unfold init. apply translate_seg_point. Qed.

Lemma translate_seg_term :
  forall v s, term (translate_seg v s) = translate_pt v (term s).
Proof. intros v s. unfold term. apply translate_seg_point. Qed.

Lemma onSegment_translate :
  forall v s p,
    onSegment s p -> onSegment (translate_seg v s) (translate_pt v p).
Proof.
  intros v s p [t [Ht Hp]]. exists t. split; [exact Ht |].
  now rewrite translate_seg_point, Hp.
Qed.


(* ----------------------------------------------------------------- *)
(*  始点・終点・向きを指定したセグメント                             *)
(* ----------------------------------------------------------------- *)

(* Direction と両端点を同時に実現できることを表す。 *)
Parameter reconnectable : Point -> Point -> Direction -> Prop.

Parameter reconnect_seg : Point -> Point -> Direction -> Segment.

Axiom reconnectable_iff :
  forall p q d,
    reconnectable p q d <->
    exists s, init s = p /\ term s = q /\ orn_seg s = d.

Lemma reconnectable_segment_exists :
  forall p q d,
    reconnectable p q d ->
    exists s, init s = p /\ term s = q /\ orn_seg s = d.
Proof. intros p q d H. now apply reconnectable_iff. Qed.

(* reconnectable な三つ組について、選択したセグメントは指定を実現する。 *)
Axiom reconnect_seg_spec :
  forall p q d,
    reconnectable p q d ->
    init (reconnect_seg p q d) = p
    /\ term (reconnect_seg p q d) = q
    /\ orn_seg (reconnect_seg p q d) = d.

Lemma reconnect_init :
  forall p q d,
    reconnectable p q d -> init (reconnect_seg p q d) = p.
Proof. intros p q d H. exact (proj1 (reconnect_seg_spec p q d H)). Qed.

Lemma reconnect_term :
  forall p q d,
    reconnectable p q d -> term (reconnect_seg p q d) = q.
Proof. intros p q d H. exact (proj1 (proj2 (reconnect_seg_spec p q d H))). Qed.

Lemma reconnect_orn :
  forall p q d,
    reconnectable p q d -> orn_seg (reconnect_seg p q d) = d.
Proof. intros p q d H. exact (proj2 (proj2 (reconnect_seg_spec p q d H))). Qed.
