
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Lists.List.
Require Import PrimitiveSegment.
Require Import Lra.
Open Scope R_scope.
Import ListNotations.

(*
 * 自動で生成される名前がズレてしまうので無意味な定義を入れている。
 * TODO: 証明のintros とかで名前付けをサボらない
 *)
Definition H := H.
(*セグメントは[0,1]->R*Rの関数
埋め込み関係は次の条件を満たしたもの
・[0,1]で微分可能
・1要素目，2要素目の関数において，[0,1]で勾配の正負が一定．
・dy/dxが微分可能
・[0,1]において凸性が変わらない
    <=> forall t \in [0,1], d2y/dx2 = d/dt(dy/dx) * (dx/dt)の正負が一定
    <=> forall t \in [0,1], d2y/dx2 = d/dt(dy/dx)の正負が一定*)

(* R*Rの微分 *)
(* Definition derivable_pair_pt (f : R -> R * R) (t : R) : Set :=
  derivable_pt (fun t1 => fst (f t1)) t * derivable_pt (fun t1 => snd (f t1)) t.

Definition derivable_pair (f : R -> R * R) : Set :=
  forall t : R, derivable_pair_pt f t.

Definition derive_pair_fst (f : R -> R * R) (pr : derivable_pair f) (x : R) : R :=
  derive_pt (fun t => fst (f t)) x (fst (pr x)).
Definition derive_pair_snd (f : R -> R * R) (pr : derivable_pair f) (x : R) : R :=
  derive_pt (fun t => snd (f t)) x (snd (pr x)).

Definition derivable_dydx_pt (f : R -> R * R) (t : R) (pr : derivable_pair f): Set :=
  derivable_pt (fun t1 => (derive_pair_snd f pr t1) / (derive_pair_fst f pr t1)) t.

Definition derivable_dydx (f : R -> R * R) (pr : derivable_pair f): Set :=
  forall t: R, derivable_dydx_pt f t pr. *)



Definition Segment := R -> R * R.
Parameter default_segment : Segment.

(* [0, 1]区間で連続かどうか，向きがPrimitiveSegmentの向きか，など *)
Parameter embed : PrimitiveSegment -> Segment -> Prop.

Definition init (seg: Segment) : R * R := seg 0.

Definition term (seg: Segment) : R * R := seg 1.

Definition init_x (s: Segment) : R := fst (init s).
Definition init_y (s: Segment) : R := snd (init s).
Definition term_x (s: Segment) : R := fst (term s).
Definition term_y (s: Segment) : R := snd (term s).

Definition head_seg (ls: list Segment) (def: Segment):= hd def ls.

(* セグメントの[0, 1]区間上にその座標があるかどうか *)
Definition onSegment (seg: Segment) (rr : R * R) := exists (t:R), 0 <= t <= 1 /\ seg t = rr.
Definition onHeadSegment (seg: Segment) (rr : R * R) := exists (t:R), t <= 1 /\ seg t = rr.
Definition onLastSegment (seg: Segment) (rr : R * R) := exists (t:R), 0 <= t /\ seg t = rr.
Inductive onExtendSegment : list Segment -> Segment -> R * R -> Prop :=
| OnSegHead : forall (hds: Segment) (ls: list Segment) (rr: R*R),
    onHeadSegment hds rr
    -> onExtendSegment (hds :: ls) hds rr
| OnSegMid : forall (ls: list Segment) (seg:Segment) (rr: R*R),
    ls <> []
    -> In seg ls
    -> onSegment seg rr
    -> onExtendSegment ls seg rr
| OnSegLast : forall (ls: list Segment) (rr: R*R),
    ls <> []
    -> onLastSegment (last ls default_segment) rr
    -> onExtendSegment ls (last ls default_segment) rr.

Lemma ex_exists : forall (ls: list Segment) (seg: Segment) (rr : R * R), onExtendSegment ls seg rr -> exists (t:R), seg t = rr.
Proof.
  intros ls seg rr Honex. inversion Honex.
    - unfold onHeadSegment in H0. destruct H0 as [t [_ Heq]]. exists t. exact Heq.
    - unfold onSegment in H1. destruct H2 as [t [_ Heq]]. exists t. exact Heq.
    - unfold onLastSegment in H1. destruct H1 as [t [_ Heq]]. exists t. exact Heq.
Qed.


Lemma onseg_onhead : forall (seg: Segment) (rr: R*R), onSegment seg rr -> onHeadSegment seg rr.
Proof.
intros seg rr HonSeg. unfold onSegment in HonSeg. destruct HonSeg as [t [[_ Hle1] Heqsegt]]. exists t. split. now auto. now auto.
Qed.

Lemma onseg_onlast : forall (seg: Segment) (rr: R*R), onSegment seg rr -> onLastSegment seg rr.
Proof.
  intros seg rr HonSeg. unfold onSegment in HonSeg. destruct HonSeg as [t [[Hge0 _] Heqsegt]]. exists t. split. now auto. now auto.
Qed.
Axiom onInit : forall s: Segment, onSegment s (init s).

Axiom onTerm : forall s: Segment, onSegment s (term s).

(* 始点と終点の位置関係を示す公理 *)
Axiom n_end_relation: forall (s: Segment) (h: H) (c: C),
    embed (n, h, c) s -> snd (init s) < snd (term s).
Axiom s_end_relation: forall (s1: Segment) (h: H) (c: C),
    embed (s, h, c) s1 -> snd (term s1) < snd (init s1).
Axiom e_end_relation: forall (s: Segment) (v: V) (c: C),
    embed (v, e, c) s -> fst (init s) < fst (term s).
Axiom w_end_relation: forall (s: Segment) (v: V) (c: C),
    embed (v, w, c) s -> fst (term s) < fst (init s).

(* セグメント上にある点と始点終点の位置関係 *)
Axiom s_onseg_relation: forall (s1: Segment) (h:H) (c:C) (x y: R),
    embed (s, h, c) s1 -> onSegment s1 (x, y) -> snd (term s1) <= y /\ y <= snd (init s1).

Axiom n_onseg_relation: forall (s1: Segment) (h:H) (c:C) (x y: R),
    embed (n, h, c) s1 -> onSegment s1 (x, y) -> snd (init s1) <= y /\ y <= snd (term s1).

Axiom e_onseg_relation: forall (s1: Segment) (v:V) (c:C) (x y: R),
    embed (v, e, c) s1 -> onSegment s1 (x, y) -> fst (init s1) <= x /\ x <= fst (term s1).

Axiom w_onseg_relation: forall (s1: Segment) (v:V) (c:C) (x y: R),
    embed (v, w, c) s1 -> onSegment s1 (x, y) -> fst (term s1) <= x /\ x <= fst (init s1).

(* 二点を通る時，その間にあるx座標を取ると，そのx座標の点がセグメント上に存在する（x(t)の連続性と中間値の定理で証明） *)
(* 二点を通る時，その間にあるx座標を取ると，そのx座標の点がセグメント上に存在する（x(t)の連続性と中間値の定理で証明） *)
Axiom exist_between_x_pos: forall (ls: list Segment) (seg: Segment) (x1 x2 y1 y2 x: R),
    onExtendSegment ls seg (x1, y1) -> onExtendSegment ls seg (x2, y2) -> y1 <= y2 -> x1 <= x -> x <= x2 -> exists y:R, onExtendSegment ls seg (x, y) /\ y1 <= y <= y2.

Axiom exist_between_x_neg: forall (ls: list Segment) (seg: Segment) (x1 x2 y1 y2 x: R),
    onExtendSegment ls seg (x1, y1) -> onExtendSegment ls seg (x2, y2) -> y2 <= y1 -> x1 <= x -> x <= x2 -> exists y:R, onExtendSegment ls seg (x, y) /\ y2 <= y <= y1.

(* 始点と終点の間にあるx座標を取ると，そのx座標の点がセグメント上にあることを示す公理 *)
Lemma e_exist_y: forall (ls: list Segment) (s':Segment) (v:V) (c:C) (x:R),
    embed (v, e, c) s' -> In s' ls -> ls <> [] -> fst (init s') <= x -> x <= fst (term s') -> exists y:R, onExtendSegment ls s' (x, y) /\ (match v with n => init_y s' <= y <= term_y s' | s => term_y  s' <= y <= init_y s' end).
Proof.
    intros ls s' v c x Hembed Hin Hnotnil Hge0 Hge1.
    assert(HonInitTerm: onExtendSegment ls s' (init_x s', init_y s') /\ onExtendSegment ls s' (term_x s', term_y s')).
    {
      split.
      - eapply OnSegMid. exact Hnotnil. exact Hin.
        unfold init_x, init_y. rewrite <- surjective_pairing. now eapply onInit.
      - eapply OnSegMid. exact Hnotnil. exact Hin.
        unfold term_x, term_y. rewrite <- surjective_pairing. now eapply onTerm.
    } destruct HonInitTerm as [HonInit HonTerm]. destruct v.
    - eapply exist_between_x_pos.
      + exact HonInit.
      + exact HonTerm.
      + apply Rlt_le. eapply n_end_relation. now eauto.
      + exact Hge0.
      + exact Hge1.
    - eapply exist_between_x_neg.
      + exact HonInit.
      + exact HonTerm.
      + apply Rlt_le. eapply s_end_relation. now eauto.
      + exact Hge0.
      + exact Hge1.
Qed.

Lemma w_exist_y: forall (ls: list Segment) (s':Segment) (v:V) (c:C) (x:R),
    embed (v, w, c) s' -> In s' ls -> ls <> [] -> fst (term s') <= x -> x <= fst (init s') -> exists y:R, onExtendSegment ls s' (x, y) /\ (match v with n => init_y s' <= y <= term_y s' | s => term_y  s' <= y <= init_y s' end).
Proof.
  intros ls s' v c x Hembed Hin Hnotnil Hge0 Hge1.
  assert(HonInitTerm: onExtendSegment ls s' (init_x s', init_y s') /\ onExtendSegment ls s' (term_x s', term_y s')).
  {
    split.
    - eapply OnSegMid. exact Hnotnil. exact Hin.
      unfold init_x, init_y. rewrite <- surjective_pairing. now eapply onInit.
    - eapply OnSegMid. exact Hnotnil. exact Hin.
      unfold term_x, term_y. rewrite <- surjective_pairing. now eapply onTerm.
  } destruct HonInitTerm as [HonInit HonTerm]. destruct v.
  - eapply exist_between_x_neg.
    + exact HonTerm.
    + exact HonInit.
    + apply Rlt_le. eapply n_end_relation. now eauto.
    + exact Hge0.
    + exact Hge1.
  - eapply exist_between_x_pos.
    + exact HonTerm.
    + exact HonInit.
    + apply Rlt_le. eapply s_end_relation. now eauto.
    + exact Hge0.
    + exact Hge1.
Qed.

(* direct connect, 直接連結可能 *)
Inductive dc : PrimitiveSegment -> PrimitiveSegment -> Prop :=
| DIfl v h c : dc (v, h, c) (v, h, i_c c)
| DXtrvN h: dc (n, h, cx) (s, h, cx)
| DXtrvS h: dc (s, h, cc) (n, h, cc)
| DXtrhN h: dc (n, h, cc) (n, i_h h, cx)
| DXtrhS h: dc (s, h, cx) (s, i_h h, cc)
.

(* 単位セグメントが単位セグメントのリストの先頭と連結可能かどうか *)
Inductive dc_pseg_hd: PrimitiveSegment -> list PrimitiveSegment -> Prop :=
| DcNil: forall (x:PrimitiveSegment), dc_pseg_hd x nil
| DcCons: forall (x y:PrimitiveSegment) (l:list PrimitiveSegment), dc x y -> dc_pseg_hd x (y::l)
.

(* scurveの条件 *)
Inductive is_scurve: list PrimitiveSegment -> Prop :=
| IsScurveNil: is_scurve nil
| IsScurveCons: forall (x:PrimitiveSegment) (xs:list PrimitiveSegment) , is_scurve xs -> dc_pseg_hd x xs -> is_scurve (x :: xs).

Definition scurve : Set := { l: list PrimitiveSegment | is_scurve l }.

(* 単位セグメントをscurveに連結 *)
Definition connect (s: PrimitiveSegment) (lp: scurve) (A: dc_pseg_hd s (proj1_sig lp)) : scurve :=
exist _ (s :: (proj1_sig lp)) (IsScurveCons s (proj1_sig lp) (proj2_sig lp) A).

(* scurveの埋め込み．scurveとSegmentのリストの述語．
lp: scurve にps: PrimitiveSegment をくっつけたものが (s2::ls): list Segment にs1: Segment をくっつけたものとして埋め込まれる関係　*)
Inductive embed_scurve : scurve -> list Segment -> Prop :=
| EmbedScurveNil : embed_scurve (exist _ nil IsScurveNil) nil
| EmbedScurveSigle : forall (ps:PrimitiveSegment) (s:Segment),
    embed ps s
    -> embed_scurve (connect ps (exist _ nil IsScurveNil) (DcNil ps)) (s::nil)
| EmbedScurveCons : forall (ps:PrimitiveSegment) (lp: scurve) (A: dc_pseg_hd ps (proj1_sig lp)) (s1 s2: Segment) (ls: list Segment),
    embed ps s1
    -> embed_scurve lp (s2::ls)
    -> term s1 = init s2
    -> embed_scurve (connect ps lp A) (s1 :: s2 :: ls).


Lemma nth_head: forall (l:list Segment) (d: Segment), nth 0 l d = head_seg l d.
  Proof.
    intros l d. destruct l. simpl; reflexivity. simpl;reflexivity.
  Qed.


Lemma consist_init_term : forall (sc: scurve) (ls1 ls2: list Segment),
  embed_scurve sc (ls1 ++ ls2)
  -> ls1 <> []
  -> ls2 <> []
  -> term (last ls1 default_segment) = init (List.hd default_segment ls2).
Proof.
  intros sc ls1. revert sc. induction ls1 as [|seg ls1']; [now idtac|].
  intros sc ls2 emb _. inversion emb.
  - (* EmbedScurveSingleの場合: ls2 <> [] だからありえん *)
    now apply eq_sym, app_eq_nil in H3.
  - (* EmbedScurveConsの場合 *)
    destruct ls1' as [|seg2 ls1''].
    + (* ls1' = [] のとき *)
      intros _. simpl in H1. now rewrite <- H1.
    + (* ls1' = _::_ のとき: 帰納法の仮定IHls1'を使う *)
      intros nemp_ls2. apply (IHls1' lp); [|now auto|now auto].
      simpl. injection H1 as _es1 _els. now subst s1 s2 ls.
Qed.

Lemma scurve_length_consis: forall (sc: scurve) (ls: list Segment),
  embed_scurve sc ls -> length (proj1_sig sc) = length ls.
Proof.
  intros sc ls. revert sc. induction ls as [|a ls IHls].
  - intros sc Hembed. inversion Hembed as [_Hex | | ]. reflexivity.
  - intros sc Hembed. inversion Hembed as [ | ps s0 Hembedps Hconnect [_HHH Hnil]| ps sctl Hdc a' s2 lstl Hembedps Hembedsctl _Hconsis [Heqsc Heqa Hls]].
    + reflexivity.
    + subst. simpl. apply IHls in Hembedsctl. rewrite Hembedsctl. reflexivity.
Qed.




Parameter extend : list Segment -> (R -> R * R).

Definition close_extended (c: Segment):=
  exists (t1 t2: R), t1 <> t2 /\ c t1 = c t2.

(* close, 閉 *)
Definition close (ls: list Segment) : Prop :=  close_extended (extend ls).

(* admissible, 許容可能 *)
Definition admissible (lp: scurve) : Prop :=
    exists ls: list Segment, (embed_scurve lp ls /\ ~ close ls).

(* リストlsに含まれてるセグメントが同じ水平方向を向いていることを表す命題 *)
Definition all_same_h (ls: list Segment) (h: H) :=
  ls <> [] /\ Forall (fun (s:Segment) => exists (v:V) (c:C), embed (v, h, c) s) ls.

(*  最初のセグメントや最後のセグメントについて，あるx/y座標より大きい/小さい任意の座標に対して，
    そのx/y座標を持つ点がセグメント上にある
    exist_between_pos/negで証明可能？ *)
Axiom extended_segment_init_n : forall (ls: list Segment) (h: H) (y x1 y1: R),
let head := head_seg ls default_segment in
embed (n, h, cx) head -> onExtendSegment ls head (x1, y1) -> y <= y1 -> exists (x: R), onExtendSegment ls head (x, y) /\ (match h with e => x <= x1 | w => x1 <= x end).

Axiom extended_segment_init_e_scx : forall (ls: list Segment) (x x1 y1: R),
let head := head_seg ls default_segment in
embed (s, e, cx) head -> onExtendSegment ls head (x1, y1) -> x <= x1 -> exists (y: R), onExtendSegment ls head (x, y) /\ y1 <= y.

Axiom extended_segment_init_e_ncc : forall (ls: list Segment) (x x1 y1: R),
let head := head_seg ls default_segment in
embed (n, e, cc) head -> onExtendSegment ls head (x1, y1) -> x <= x1 -> exists (y: R), onExtendSegment ls head (x, y) /\ y <= y1.

Axiom extended_segment_term_n : forall (ls: list Segment) (h: H) (y x1 y1: R),
let last_s := last ls default_segment in
embed (n, h, cc) last_s -> onExtendSegment ls last_s (x1, y1) ->  y1 <= y -> exists (x: R), onExtendSegment ls (last ls default_segment) (x, y) /\ (match h with e => x1 <= x | w => x <= x1 end).

Axiom extended_segment_term_w_ncx : forall (ls: list Segment) (x x1 y1: R),
let last_s := last ls default_segment in
embed (n, w, cx) last_s -> onExtendSegment ls last_s (x1, y1) ->  x <= x1 -> exists (y: R), onExtendSegment ls last_s (x, y) /\ y1 <= y.

Axiom x_cross_h:
    forall (ls: list Segment) (s1 s2: Segment) (xa xb y1a y1b y2a y2b: R),
    In s1 ls
    -> In s2 ls
    -> onExtendSegment ls s1 (xa, y1a)
    -> onExtendSegment ls s1 (xb, y1b)
    -> onExtendSegment ls s2 (xa, y2a)
    -> onExtendSegment ls s2 (xb, y2b)
    -> (y1a - y2a) * (y1b - y2b) < 0
    -> close ls.

Axiom x_cross_v:
    forall (ls: list Segment) (s1 s2: Segment) (ya yb x1a x1b x2a x2b: R),
    In s1 ls
    -> In s2 ls
    -> onExtendSegment ls s1 (x1a, ya)
    -> onExtendSegment ls s1 (x1b, yb)
    -> onExtendSegment ls s2 (x2a, ya)
    -> onExtendSegment ls s2 (x2b, yb)
    -> (x1a - x2a) * (x1b - x2b) < 0
    -> close ls.




(* (n,e,cx)から始まり右にいくらか伸びて、真ん中は自由で、最後は左に伸びたあと(n,w,_)で終わる場合
   右に行く往路と左に行く復路で共通のxに対して y復路<y往路の場合、このセグメントはどこかで交わる *)
(* s1とs2は往路と復路で共通のxをもつセグメント *)
Lemma end_nwcx_close: forall sc s_start s_end c x y1 y2 l s1 center s2 r,
  embed_scurve sc (l ++ [s1] ++ center ++ [s2] ++ r) ->
  head (l ++ [s1]) = Some s_start ->
  embed (n, e, cx) s_start ->
  last ([s2] ++ r) default_segment = s_end ->
  embed (n, w, c) s_end ->
  all_same_h (l ++ [s1]) e ->  (*往路は東に伸びる*)
  all_same_h ([s2] ++ r) w ->  (*復路は西に伸びる*)
  onSegment s1 (x, y1) ->
  onSegment s2 (x, y2) ->
  y2 < y1 ->
  close (l ++ [s1] ++ center ++ [s2] ++ r).
Proof.
Admitted.

(* n,e,cxから始まり，しばらく右に伸びている，(x1, y2)を通る．
最後のセグメントが左上で，(x1, y1)を通る．
y1<=y2の時に最後のセグメントはどこかで交わる*)
(* n,e,cxから始まり，しばらく右に伸びている，(x1, y2)を通る．
最後のセグメントが左上で，(x1, y1)を通る．
y1<=y2の時に最後のセグメントはどこかで交わる*)
Axiom end_cross_term_nw:
    forall (sc: scurve) (ls1 ls2: list Segment) (x1 y1 y2: R),
    let hd1 := head_seg ls1 default_segment in
    let tl1 := last ls1 default_segment in
    let tl2 := last ls2 default_segment in
    embed_scurve sc (ls1 ++ ls2)
    -> y1 < y2
    -> ls2 <> []
    -> embed (n, e, cx) hd1
    -> embed (n, w, cc) tl2 \/ embed (n, w, cx) tl2
    -> onExtendSegment (ls1 ++ ls2) tl2 (x1, y1)
    -> onExtendSegment (ls1 ++ ls2) tl1 (x1, y2)
    -> all_same_h ls1 e
    -> close (ls1 ++ ls2).


Axiom end_cross_init_ne:
    forall (sc: scurve) (ls1 ls2: list Segment) (x1 y1 y2: R),
    let hd2 := head_seg ls2 default_segment in
    let tl2 := last ls2 default_segment in
    let hd1 := head_seg ls1 hd2 in
    embed_scurve sc (ls1 ++ ls2)
    -> y2 < y1
    -> ls1 <> []
    -> embed (n, e, cc) hd1 \/ embed (n, e, cx) hd1
    -> embed (n, w, cc) tl2
    -> onSegment hd1 (x1, y1)
    -> onSegment hd2 (x1, y2)
    -> all_same_h (rev ls2) w
    -> close (ls1++ls2).


Lemma embed_scurve_inv_Cons sc p1 p2 ps ss:
  embed_scurve sc ss ->
  proj1_sig sc = (p1 :: p2 :: ps) ->
  exists s1 s2 rest sc',
    ss = s1 :: s2 :: rest /\ proj1_sig sc' = p2 :: ps /\ embed_scurve sc' (s2 :: rest)
    /\ embed p1 s1 /\ term s1 = init s2.
Proof.
  intros emb e_proj1. inversion emb as [esc _e| p1' s1 emb1 esc| p1' sc' A s1 s2 ss_tail emb1 emb' term_init conn e_ss] .
  - now rewrite <- esc in e_proj1.
  - now rewrite <- esc in e_proj1.
  - rewrite <- conn in e_proj1.
    injection e_proj1 as _p1' e_proj1'. subst p1'.
    now exists s1, s2, ss_tail, sc'.
Qed.

Lemma embed_scurve_inv_Single sc p ss:
  embed_scurve sc ss -> proj1_sig sc = [p] ->
  exists s, ss = [s] /\ embed p s.
Proof.
  intros emb e_proj1. inversion emb as [esc _e|p' s emb1 esc|p' sc' A s1 s2 ss' emb1 emb'].
  - now rewrite <- esc in e_proj1.
  - rewrite <- esc in e_proj1. injection e_proj1 as _ep'. subst. now exists s.
  - subst. simpl in e_proj1. inversion emb'; now subst.
Qed.


Definition example1: list PrimitiveSegment := [(n,e,cx);(s,e,cx);(s,w,cc);(n,w,cc)].
Lemma example1_is_scurve: is_scurve example1.
Proof. repeat constructor. Qed.

Lemma example1_is_close: forall lp: scurve, proj1_sig lp = example1 -> ~ admissible lp.
Proof.
    intros lp.
    destruct lp as [l p].
    simpl.
    unfold example1.
    intros Hl.
    unfold admissible, not.
    intros Hclose.
    destruct Hclose as [ls [Hembed_ls Hclose]].
    destruct ls as [| s0].
    - inversion Hembed_ls as [Hnil | |]. rewrite Hl in Hnil. discriminate.
    - destruct ls as [| s1].
     -- inversion Hembed_ls as [|ps s1 Hembed0 Hcontra Hs10|]. rewrite Hl in Hcontra. discriminate.
     -- destruct ls as [| s2].
      --- inversion Hembed_ls as [| | ps0 lp H s2 s3 ls Hembed0 Hembedsc1 Hconsis01 Hps [H1 H2 H3]]. subst. inversion Hembedsc1 as [|ps1 s2 Hembed1 Hconnect1 H1|]. rewrite <- Hconnect1 in Hps. simpl in Hps. discriminate.
      --- destruct ls as [| s3].
       ---- inversion Hembed_ls as [| | ps0 lp H s3 s4 ls Hembed0 Hembedsc1 Hconsis01 Hps [H1 H2 H3]]. subst. inversion Hembedsc1 as [| | ps1 lp1 Hdc1 s3 s4 ls1 Hembed1 Hembedsc2 Hconsis12 Hconnect2 [H1 H2 H3]]. subst. inversion Hembedsc2 as [| ps2 s3 Hembed2 Hconnect2 H0|]. subst. simpl in *. discriminate.
       ---- destruct ls as [| overseg].
            * inversion Hembed_ls as [| |p0 scurve13 H s0' s1' ls Hembed0 Hembedsc13 Hconsis01 Hlcons [H1 H2 H3]]. subst.
              inversion Hembedsc13 as [| |p1 scurve23 Hdcpseg123 s1' s2' ls3 Hembed1 Hembedsc23 Hconsis12 Hconnect1 [H1 H2 H3]]. subst.
              inversion Hembedsc23 as [| |p2 scurve3 Hdcpseg23 s2' s3' ls'' Hembed2 Hembedsc3 Hconsis23 Hconnect2 [H1 H2 H3]]. subst.
              inversion Hembedsc3 as [| p3 s3' Hembed3 Hconnect3 H1| ].
              apply Hclose. subst.
              inversion Hlcons as [[H0 H1 H2 H3]].
              subst p0 p1 p2 p3.
              destruct (Rle_or_lt (fst (init s1)) (fst (term s2))) as [Hge | Hlt].
              + set (x1 := fst (init s3)).
              set (y1 := snd (init s3)).
              assert (Hxins1:fst (term s2) < fst (term s1)).
                {rewrite Hconsis12. apply w_end_relation with (s:=s2) (v:=s) (c:=cc). exact Hembed2. }
              assert (Hyins1: exists y:R, onSegment s1 (x1, y)).
                {
                    eapply e_exist_y with (ls:= [s0;s1;s2;s3]) in Hembed1 as Hembed1'.
                        + destruct Hembed1' as [yy H']. exists yy. destruct H' as [HonEx _]. inversion HonEx as [headseg ls' rr _Hnotnil [_Hhead _Heqls'] Heqs1 _Hrr| ls s1' rr _Hnotnil _Hin HonSegs1 _Heq1 _Heq2 _Heq3 | ls' rr _Hnotnil _Hlast _Heq Heqs1 _Hrr]. simpl in Heqs1. eapply s_end_relation in Hembed1. rewrite <- Hconsis01 in Hembed1. rewrite Heqs1 in Hembed1. now lra. exact HonSegs1. simpl in Heqs1. eapply w_end_relation in Hembed3. eapply e_end_relation in Hembed1. rewrite Heqs1 in Hembed3. now lra.
                        + right; left; reflexivity.
                        + discriminate.
                        + unfold x1. rewrite <- Hconsis23. apply Hge.
                        + unfold x1. rewrite <- Hconsis23. apply Rlt_le. exact Hxins1.
                }
              destruct Hyins1 as [y2 HonSeg].
              eapply end_cross_term_nw with (ls1:=[s0;s1]) (x1:=x1) (y1:=y1).
                ++ simpl. exact Hembed_ls.
                ++ apply Rlt_le_trans with (r2 := snd (term s1)). unfold y1. rewrite <- Hconsis23. rewrite Hconsis12. apply s_end_relation with (s1:=s2) (h:=w) (c:=cc). apply Hembed2.
                    apply s_onseg_relation with (s1:=s1) (h:=e) (c:=cx) (x:=x1) (y:=y2). apply Hembed1. exact HonSeg.
                ++ unfold not.  intros Hcontra. discriminate.
                ++ simpl. exact Hembed0.
                ++ simpl. left. exact Hembed3.
                ++ simpl. unfold x1, y1. rewrite <- surjective_pairing with (p:=init s3). apply OnSegMid. discriminate. simpl. right;right;right;left. reflexivity. now apply onInit with (s:=s3).
                ++ simpl. apply OnSegMid. discriminate. right;left;reflexivity. exact HonSeg.
                ++ unfold all_same_h. split. unfold not; discriminate. econstructor 2. exists n,cx. exact Hembed0. econstructor 2. exists s,cx. exact Hembed1. now econstructor 1.

              + set (x1 := fst (init s1)).
              set (y1 := snd (init s1)).
              assert (Hxins1:fst (init s1) < fst (init s2)).
                {rewrite <- Hconsis12. apply e_end_relation with (s:=s1) (v:=s) (c:=cx). exact Hembed1. }
              assert (Hyins1: exists y:R, onSegment s2 (x1, y)).
                {
                    eapply w_exist_y with (ls:= [s0;s1;s2;s3]) in Hembed2 as Hembed2'.
                    + destruct Hembed2' as [yy H']. exists yy. destruct H' as [HonEx _]. inversion HonEx as [ls' rr _Hnotnil _Hhead _Heq Heqs1 _Hrr| ls s1' rr _Hnotnil _Hin HonSegs1 _Heq1 _Heq2 _Heq3 | ls' rr _Hnotnil _Hlast _Heq Heqs1 _Hrr].
                      - simpl in Heqs1. eapply w_end_relation in Hembed2. eapply e_end_relation in Hembed0. rewrite <- Heqs1 in Hembed2. now lra.
                      - exact HonSegs1.
                      - simpl in Heqs1. eapply s_end_relation in Hembed2. rewrite Hconsis23 in Hembed2. rewrite Heqs1 in Hembed2. now lra.
                    + right; right; left; reflexivity.
                    + discriminate.
                    + unfold x1. apply Rlt_le. apply Hlt.
                    + unfold x1. apply Rlt_le. exact Hxins1.
                 }
              destruct Hyins1 as [y2 HonSeg].
              eapply end_cross_init_ne with (ls1 := [s0;s1]) (x1:=x1) (y1:=y1).
                ++ simpl. exact Hembed_ls.
                ++ apply Rle_lt_trans with (r2:= snd (term s1)). unfold y1. rewrite Hconsis12. apply s_onseg_relation with (s1:=s2) (h:=w) (c:=cc) (x:= x1) (y:=y2). apply Hembed2. apply HonSeg.
                    unfold y1. apply s_end_relation with (s1:=s1) (h:=e) (c:=cx). exact Hembed1.
                ++ discriminate.
                ++ simpl. right. exact Hembed0.
                ++ simpl. exact Hembed3.
                ++ simpl. unfold x1, y1. rewrite <- surjective_pairing. rewrite <- Hconsis01. now eapply onTerm.
                ++ exact HonSeg.
                ++ simpl. unfold all_same_h. split. discriminate. econstructor. exists n,cc. exact Hembed3. econstructor. exists s,cc. exact Hembed2. now auto.
            * inversion Hembed_ls as [| | ps lp H s4 s5 ls0 Hembed0 Hembedsc1 Hconsis01 Hlcons [H1 H2 H3]]. subst.
              inversion Hembedsc1 as [| | ps1 scurve2 Hdc1 s1' s2' ls0 Hembed1 Hembedsc2 Hconsis12 Hconnect1 [H1 H2 H3]]. subst.
              inversion Hembedsc2 as [| | ps2 scurve3 Hdc2 s2' s3' ls1 Hembed2 Hembedsc3 Hconsis23 Hconnect2 [H1 H2 H3]]. subst.
              inversion Hembedsc3 as [| |ps3 scurve4 Hdc3 s3' s4' ls2 Hembed3 Hembedsc4 Hconsis34 Hconnect3 [H1 H2 H3]]. subst. simpl in *.
              inversion Hlcons as [[Hps0 Hps1 Hps2 Hps3 Hsc4nil]].
              inversion Hembedsc4 as [| psov sov Hembedov Hconnectov [Hsov Hnil]| psov scov Hdcov sov' s4 ls0 Hembedov Hembedscov Hconsisov Hconnectov [H1 H2]].
            ** subst. simpl in *. discriminate.
            ** subst. discriminate.
Qed.

(* initとtermは異なる点 *)
Axiom neq_init_term : forall seg, init seg <> term seg.

(*2つの異なる点を共有していたら延長考えなくともclose*)
Lemma have_two_same_point_close s1 s2 i j p1 p2 l :
  i <> j -> List.nth_error l i = Some s1 -> List.nth_error l j = Some s2 ->
  onSegment s1 p1 -> onSegment s1 p2 -> onSegment s2 p1 -> onSegment s2 p2 ->
  p1 <> p2 ->
  close l.
Admitted.
