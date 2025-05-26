
Require Import Stdlib.Reals.Reals.
Require Import Stdlib.Lists.List.
Open Scope R_scope.
Import ListNotations.

Inductive V : Set :=
| n : V
| s : V
.

Inductive H : Set :=
| e : H
| w : H
.

Inductive C : Set :=
| cx : C
| cc : C
.

Inductive Dir : Set :=
| Ver : V -> Dir
| Hor : H -> Dir
.

Definition i_v (v : V) : V :=
match v with
| n => s
| s => n
end.

Definition i_h (h : H) : H :=
match h with
| e => w
| w => e
end.

Definition i (d: Dir) : Dir :=
match d with
| Ver v => Ver (i_v v)
| Hor h => Hor (i_h h)
end.

Definition i_c (c: C) : C :=
match c with
| cx => cc
| cc => cx
end. 

(* PrimitiveSegment，単位セグメント *)
Definition PrimitiveSegment := (V * H * C)%type.
(* 各要素を取り出す *)
Definition V_of (x:PrimitiveSegment) := fst(fst x).
Definition H_of (x:PrimitiveSegment) := snd(fst x).
Definition C_of (x:PrimitiveSegment) := snd x.


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

(* [0, 1]区間で連続かどうか，向きがPrimitiveSegmentの向きか，など *)
Parameter embed : PrimitiveSegment -> Segment -> Prop.

Parameter init : Segment -> R * R.

Parameter term : Segment -> R * R.

Parameter init_lim : R.
Parameter term_lim : R.

Definition init_x (s: Segment) : R := fst (init s).
Definition init_y (s: Segment) : R := snd (init s).
Definition term_x (s: Segment) : R := fst (term s).
Definition term_y (s: Segment) : R := snd (term s).

(* セグメントの[0, 1]区間上にその座標があるかどうか *)
Parameter onSegment : Segment -> R * R -> Prop.

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

(* 二点を通る時，その間にあるx座標を取ると，そのx座標の点がセグメント上に存在する（x(t)の連続性と中間値の定理で証明） *)
Axiom exist_between_x_pos: forall (s: Segment) (x1 x2 y1 y2 x: R),
    onSegment s (x1, y1) -> onSegment s (x2, y2) -> y1 <= y2 -> x1 <= x -> x <= x2 -> exists y:R, onSegment s (x, y) /\ y1 <= y <= y2.

Axiom exist_between_x_neg: forall (s: Segment) (x1 x2 y1 y2 x: R),
    onSegment s (x1, y1) -> onSegment s (x2, y2) -> y2 <= y1 -> x1 <= x -> x <= x2 -> exists y:R, onSegment s (x, y) /\ y2 <= y <= y1.

(* 始点と終点の間にあるx座標を取ると，そのx座標の点がセグメント上にあることを示す公理 *)
Lemma e_exist_y: forall (s':Segment) (v:V) (c:C) (x:R),
    embed (v, e, c) s' -> fst (init s') <= x -> x <= fst (term s') -> exists y:R, onSegment s' (x, y) /\ (match v with n => init_y s' <= y <= term_y s' | s => term_y  s' <= y <= init_y s' end).
Proof.
    intros s' v c x H0 Hge0 Hge1. destruct v.
    - eapply exist_between_x_pos with (x1:=fst (init s')) (y1:= snd (init s')) (x2:=fst (term s')) (y2:= snd (term s')).
        + rewrite <- surjective_pairing. now eapply onInit.
        + rewrite <- surjective_pairing. now eapply onTerm.
        + apply Rlt_le. eapply n_end_relation. now eauto.
        + exact Hge0.
        + exact Hge1.
    - eapply exist_between_x_neg with (x1:=fst (init s')) (y1:= snd (init s')) (x2:=fst (term s')) (y2:= snd (term s')).
        + rewrite <- surjective_pairing. now eapply onInit.
        + rewrite <- surjective_pairing. now eapply onTerm.
        + apply Rlt_le. eapply s_end_relation. now eauto.
        + exact Hge0.
        + exact Hge1.
Qed.

Lemma w_exist_y: forall (s':Segment) (v:V) (c:C) (x:R),
    embed (v, w, c) s' -> fst (term s') <= x -> x <= fst (init s') -> exists y:R, onSegment s' (x, y) /\ (match v with n => init_y s' <= y <= term_y s' | s => term_y  s' <= y <= init_y s' end).
Proof.
    intros s' v c x H0 Hge0 Hge1. destruct v.
    - eapply exist_between_x_neg with (x2:=fst (init s')) (y2:= snd (init s')) (x1:=fst (term s')) (y1:= snd (term s')).
        + rewrite <- surjective_pairing. now eapply onTerm.
        + rewrite <- surjective_pairing. now eapply onInit.
        + apply Rlt_le. eapply n_end_relation. now eauto.
        + exact Hge0.
        + exact Hge1.
    - eapply exist_between_x_pos with (x2:=fst (init s')) (y2:= snd (init s')) (x1:=fst (term s')) (y1:= snd (term s')).
        + rewrite <- surjective_pairing. now eapply onTerm.
        + rewrite <- surjective_pairing. now eapply onInit.
        + apply Rlt_le. eapply s_end_relation. now eauto.
        + exact Hge0.
        + exact Hge1.
Qed.

Inductive ifl: PrimitiveSegment -> PrimitiveSegment -> Prop :=
| Ifl: forall (v: V) (h: H) (c_x c_y : C), 
    c_x = i_c c_y -> ifl (v, h, c_x) (v, h, c_y).

Inductive xtrv: PrimitiveSegment -> PrimitiveSegment -> Prop :=
| XtrvN: forall h: H, xtrv (n, h, cx) (s, h, cx)
| XtrvS: forall h: H, xtrv (s, h, cc) (n, h, cc)
.

Inductive xtrh: PrimitiveSegment -> PrimitiveSegment -> Prop :=
| XtrhN: forall h: H, xtrh (n, h, cc) (n, i_h h, cx)
| XtrhS: forall h: H, xtrh (s, h, cx) (s, i_h h, cc)
.

(* direct connect, 直接連結可能 *)
Definition dc (x y: PrimitiveSegment) : Prop :=
ifl x y \/ xtrv x y \/ xtrh x y.

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


Definition head_seg (ls: list Segment) (default: Segment) : Segment :=
  match ls with
  | [] => default
  | hd :: _ => hd
  end.
  
Lemma nth_head: forall (l:list Segment) (d: Segment), nth 0 l d = head_seg l d.
  Proof.
    intros l d. destruct l. simpl; reflexivity. simpl;reflexivity.
  Qed.
  
Parameter default_segment : Segment.

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

(* concat_segはセグメントをくっつけて一つの関数として扱ったもの
   extendは最初のセグメントと最後のセグメント以外は同じ，
    最初のセグメントsは
    (extend s)(0) := init_lim
    (extend s)(t) := 延長された直線(0<t<=1/2)
    (extend s)(t) := s(2t - 1) (1/2<=t<=1)
    最後のセグメントも同様 *)
Parameter concat_seg: list Segment -> Segment.

Parameter extend: list Segment -> list Segment.

Axiom len_equal_extended: forall (ls: list Segment), length ls = length (extend ls).
Axiom head_extend: forall (ls1 ls2: list Segment), head (extend ls1) = head (extend (ls1 ++ ls2)).
Axiom last_extend: forall (ls1 ls2: list Segment), last (extend ls1) = last (extend (ls2 ++ ls1)).



(* 元のセグメント上にあった座標は，延長された曲線上の[0,1]区間に存在する *)
Axiom is_on_extended: forall (ls: list Segment) (s: Segment) (x y: R),
  In s (extend ls)
  -> onSegment s (x, y)
  -> exists (t:R), 0 <= t <= 1 /\ (concat_seg (extend ls)) t = (x, y).

Axiom is_on_extended2: forall (ls: list Segment) (p: R*R) (m: nat) (default: Segment),
  onSegment (nth m ls default) p
  -> onSegment (nth m (extend ls) default) p.

Axiom is_on_extended_head: forall (ls: list Segment) (p: R*R) (default: Segment),
  onSegment (head_seg ls default) p
  -> onSegment (head_seg (extend ls) default) p.

Axiom is_on_extended_last: forall (ls: list Segment) (p: R*R) (default: Segment),
  onSegment (last ls default) p
  -> onSegment (last (extend ls) default) p.

Definition close_extended (c: Segment):=
  exists (t1 t2: R), t1 <> t2 /\ c t1 = c t2.

(* close, 閉 *)
Definition close (ls: list Segment) : Prop :=  close_extended (concat_seg (extend ls)).

(* admissible, 許容可能 *)
Definition admissible (lp: scurve) : Prop :=
    exists ls: list Segment, (embed_scurve lp ls /\ ~ close ls).

(* リストlsに含まれてるセグメントが同じ水平方向を向いていることを表す命題 *)
Definition all_same_h (ls: list Segment) (h: H) :=
  ls <> [] /\ Forall (fun (s:Segment) => exists (v:V) (c:C), embed (v, h, c) s) ls.

Axiom extended_segment_init_n : forall (ls ls2: list Segment) (h: H) (y x1 y1: R),
let head := head_seg (extend ls) default_segment in
embed (n, h, cx) (head_seg ls default_segment) -> onSegment head (x1, y1) -> y <= y1 -> exists (x: R), onSegment (head_seg (extend (ls ++ ls2)) default_segment) (x, y) /\ (match h with e => x <= x1 | w => x1 <= x end).

Axiom extended_segment_term_n : forall (ls ls2: list Segment) (h: H) (y x1 y1: R),
let last_s := last (extend ls) default_segment in
embed (n, h, cc) (last ls default_segment) -> onSegment last_s (x1, y1) ->  y1 <= y -> exists (x: R), onSegment (last (extend (ls2 ++ ls)) default_segment) (x, y) /\ (match h with e => x1 <= x | w => x <= x1 end).

Axiom extended_segment_term_w_ncx : forall (ls: list Segment) (x x1 y1: R),
let last_s := last (extend ls) default_segment in
embed (n, w, cx) (last ls default_segment) -> onSegment last_s (x1, y1) ->  x <= x1 -> exists (y: R), onSegment last_s (x, y) /\ y1 <= y.

Axiom extended_segment_term_w_scc : forall (ls: list Segment) (x x1 y1: R),
let last_s := last (extend ls) default_segment in
embed (s, w, cc) (last ls default_segment) -> onSegment last_s (x1, y1) ->  x <= x1 -> exists (y: R), onSegment last_s (x, y)  /\ y <= y1.

Axiom x_cross_h: 
    forall (ls: list Segment) (s1 s2: Segment) (xa xb y1a y1b y2a y2b: R),
    In s1 (extend ls)
    -> In s2 (extend ls)
    -> onSegment s1 (xa, y1a)
    -> onSegment s1 (xb, y1b)
    -> onSegment s2 (xa, y2a)
    -> onSegment s2 (xb, y2b)
    -> (y1a - y2a) * (y1b - y2b) < 0
    -> close ls.

Axiom x_cross_v: 
    forall (ls: list Segment) (s1 s2: Segment) (ya yb x1a x1b x2a x2b: R),
    In s1 (extend ls)
    -> In s2 (extend ls)
    -> onSegment s1 (x1a, ya)
    -> onSegment s1 (x1b, yb)
    -> onSegment s2 (x2a, ya)
    -> onSegment s2 (x2b, yb)
    -> (x1a - x2a) * (x1b - x2b) < 0
    -> close ls.




(* n,e,cxから始まり，しばらく右に伸びている，(x1, y2)を通る．
最後のセグメントが左上で，(x1, y1)を通る．
y1<=y2の時に最後のセグメントはどこかで交わる*)
Lemma end_cross_term_nw:
    forall (sc: scurve) (ls1 ls2: list Segment) (x1 y1 y2: R),
    let hd1 := head_seg ls1 default_segment in
    let tl1 := last ls1 default_segment in
    let tl2 := last ls2 default_segment in
    let tl2_ex := last (extend (ls1 ++ ls2)) default_segment in
    embed_scurve sc (ls1 ++ ls2)
    -> y1 < y2
    -> ls2 <> []
    -> embed (n, e, cx) hd1
    -> embed (n, w, cc) tl2 \/ embed (n, w, cx) tl2
    -> onSegment tl2_ex (x1, y1)
    -> onSegment tl1 (x1, y2)
    -> all_same_h ls1 e
    -> close (ls1 ++ ls2).
Proof.
    intros sc ls1. induction ls1 as [|a ls1 IHl] using rev_ind.
    - intros ls2 x1 y1 y2 _ _ _ _ _ _ _ _ _ _ _ Hcontra. now inversion Hcontra.
    - intros ls2 x1 y1 y2 hd1 tl1 tl2 tl2_ex Hsc H0 HnotNil Hembedhd1 Hembedtl2 HonSegtl2 HonSegtl1 Hallh.
      destruct ls1.
        (* ls1がシングルトンのとき *)
        + destruct Hembedtl2 as [Hembedtl2cc| Hembedtl2cx].
          (* tl2がcc *)
            * eapply extended_segment_init_n with (x1:=x1) (y:=y1) in Hembedhd1. 
                -- eapply extended_segment_term_n with (x1:=x1) (y:=y2) in Hembedtl2cc.
                    ++ destruct Hembedhd1 as [x0 [Honsegtl10 Hge]].
                       destruct Hembedtl2cc as [x0' [Honsegtl20 Hge0]].
                       destruct Hge as [Hgt | Heq].
                        ** destruct Hge0 as [Hgt0 | Heq0].
                            --- eapply x_cross_v with (s1:=nth 0 (extend (a::ls2)) default_segment) (s2:=tl2_ex).
                              (* In (nth 0 (extend l) d) (extend l) *)
                                +++ simpl. assert (H1: (0 < length (extend (a::ls2)))%nat). rewrite <- len_equal_extended. simpl. now eapply Nat.lt_0_succ. eapply nth_In. exact H1.
                              (* In (last (extend l) (extend l)) *)
                                +++ eapply exists_last in HnotNil. destruct HnotNil as [ls' s0]. destruct s0 as [ls'' e]. subst. unfold tl2_ex. 
                                    assert (H_not_0: (length (extend (([] ++ [a]) ++ ls' ++ [ls''])) <> 0)%nat). rewrite <- len_equal_extended. simpl. discriminate. 
                                    rewrite length_zero_iff_nil in H_not_0. eapply exists_last in H_not_0. destruct H_not_0 as [xl [x e]]. rewrite e. rewrite last_last. now eapply in_elt.
                                +++ unfold tl1 in HonSegtl1. simpl in HonSegtl1. eapply is_on_extended2. simpl. exact HonSegtl1.
                                +++ simpl in Honsegtl10. rewrite nth_head. eapply Honsegtl10.
                                +++ unfold tl2. exact Honsegtl20.
                                +++ exact HonSegtl2.
                                +++ eapply Rlt_gt in Hgt0. eapply Rlt_minus in Hgt. eapply Rgt_minus in Hgt0. eapply Rmult_pos_neg. exact Hgt0. exact Hgt.
                            --- subst. simpl. admit. 
                        ** subst. simpl. admit.
                    ++ unfold tl2_ex in HonSegtl2. rewrite <- last_extend in HonSegtl2. exact HonSegtl2.
                    ++ apply Rlt_le. exact H0. 
                -- simpl in *. unfold tl1 in HonSegtl1. eapply is_on_extended_head. exact HonSegtl1.
                -- apply Rlt_le. exact H0.
            * eapply extended_segment_init_n with (x1:=x1) (y:=y1) in Hembedhd1. 
                -- destruct Hembedhd1 as [x0 [Honsegtl10 Hge]]. eapply extended_segment_term_w_ncx with (y1:=y1) (x:=x0) in Hembedtl2cx.
                    ++ destruct Hembedtl2cx as [y [Honsegtl20 Hge0]].
                      destruct Hge as [Hgt | Heq].
                        ** destruct Hge0 as [Hgt0 | Heq0].
                            --- eapply x_cross_h with (s1:=nth 0 (extend (a::ls2)) default_segment) (s2:=tl2_ex).
                                +++ simpl. assert (H1: (0 < length (extend (a::ls2)))%nat). rewrite <- len_equal_extended. simpl. now eapply Nat.lt_0_succ. eapply nth_In. exact H1.
                                +++ eapply exists_last in HnotNil. destruct HnotNil as [ls' s0]. destruct s0 as [ls'' e]. subst. unfold tl2_ex.
                                    assert (H_not_0: (length (extend (([] ++ [a]) ++ ls' ++ [ls''])) <> 0)%nat). rewrite <- len_equal_extended. simpl. discriminate. 
                                    rewrite length_zero_iff_nil in H_not_0. eapply exists_last in H_not_0. destruct H_not_0 as [xl [x e]]. rewrite e. rewrite last_last. now eapply in_elt.
                                +++ unfold tl1 in HonSegtl1. simpl in HonSegtl1. eapply is_on_extended2. simpl. exact HonSegtl1.
                                +++ simpl in Honsegtl10. rewrite nth_head. eapply Honsegtl10.
                                +++ exact HonSegtl2.
                                +++ unfold tl2_ex. rewrite <- last_extend. exact Honsegtl20.
                                +++ eapply Rlt_gt in Hgt0. eapply Rlt_minus in Hgt0. eapply Rgt_minus in H0. eapply Rmult_pos_neg. exact H0. exact Hgt0.
                            --- subst. admit. 
                        ** subst. admit.
                    ++ unfold tl2_ex in HonSegtl2. rewrite <- last_extend in HonSegtl2. exact HonSegtl2.
                    ++ exact Hge. 
                -- simpl in *. unfold tl1 in HonSegtl1. eapply is_on_extended_head. exact HonSegtl1.
                -- apply Rlt_le. exact H0.
        (* ls1 = s0 :: ls1 のとき*)
        + unfold tl1 in HonSegtl1. rewrite last_last in HonSegtl1. clear tl1. 
          assert (Hgexax1: init_x a <= x1).
          {
            unfold all_same_h in Hallh. destruct Hallh as [_ Hforall]. rewrite Forall_app in Hforall. destruct Hforall as [_ Hae].
            inversion Hae. destruct H3 as [v [c Hae']]. eapply e_onseg_relation in Hae'. now apply Hae'. exact HonSegtl1.
          }
          destruct Hembedtl2 as [Hembedtl2cc| Hembedtl2cx].
            * destruct (Rlt_or_le (init_y a) y1) as [Hgtyay1 | Hleyay1].
            {
              admit.
            }
             eapply extended_segment_term_n with (x1:=x1) (y:=init_y a) in Hembedtl2cc as Hext. assert(Hexistsx: exists x: R, onSegment tl2_ex (x, init_y a)).
            {
              destruct Hext as [x H1]. unfold tl2_ex. exists x. destruct H1 as [H1 _]. exact H1.
            }
              -- clear Hext. destruct Hexistsx as [x2 Hembedtl2ex]. destruct (Rlt_or_le (init_x a) x2) as [Hgt | Hle]. 
                ++ eapply extended_segment_term_n with (x1:=x1) (y:=y2) in Hembedtl2cc as Hext.
                  ** destruct Hext as [x3 [HonSegtl2x3y2 [Hgt1|Heq1]]].
                    --- eapply x_cross_v with (s1:=nth (length (s0::ls1)) (extend (((s0 :: ls1) ++ [a]) ++ ls2)) default_segment) (s2:=tl2_ex).
                      +++ eapply nth_In. rewrite <- len_equal_extended. rewrite length_app. rewrite length_app. rewrite <- Nat.add_assoc. eapply Nat.lt_add_pos_r. simpl. now apply Nat.lt_0_succ.
                    (* In (last (extend l) (extend l)) *)
                      +++ eapply exists_last in HnotNil. destruct HnotNil as [ls' alast]. destruct alast as [ls'' e]. subst. unfold tl2_ex.
                          assert (H_not_0: (length (extend (((s0::ls1) ++ [a]) ++ ls' ++ [ls''])) <> 0)%nat). rewrite <- len_equal_extended. simpl. discriminate. 
                          rewrite length_zero_iff_nil in H_not_0. eapply exists_last in H_not_0. destruct H_not_0 as [xl [x e]]. rewrite e. rewrite last_last. now eapply in_elt.
                      +++ assert (HonSega: onSegment (nth (length (s0 :: ls1)) (((s0 :: ls1) ++ [a]) ++ ls2) default_segment) (x1, y2)).
                            {
                              simpl. rewrite <- app_assoc. simpl. rewrite nth_middle. exact HonSegtl1.
                            }
                            eapply is_on_extended2. exact HonSega.
                      +++ assert (HonSega: onSegment (nth (length (s0 :: ls1)) (((s0 :: ls1) ++ [a]) ++ ls2) default_segment) (init a)).
                            {
                              simpl. rewrite <- app_assoc. simpl. rewrite nth_middle. now apply onInit. 
                            }
                            eapply is_on_extended2. rewrite surjective_pairing in HonSega. exact HonSega.
                      +++ exact HonSegtl2x3y2.
                      +++ unfold init_y in Hembedtl2ex. exact Hembedtl2ex.
                      +++ eapply Rgt_minus in Hgt1. eapply Rlt_minus in Hgt. eapply Rmult_pos_neg. exact Hgt1. unfold init_x in Hgt. exact Hgt.
                    (* x1, y2をaとtl2_exが通る *)
                    --- admit.
                  ** unfold tl2_ex in HonSegtl2. rewrite <- last_extend in HonSegtl2. exact HonSegtl2.
                  ** apply Rlt_le. exact H0.
                ++ eapply exist_between_x_neg with (x:=init_x a) in HonSegtl2.
                  {
                    destruct HonSegtl2 as [y3 [HonSegtl2ex [_ [Hge1| Heq1]]]].
                      - rewrite <- app_assoc. eapply IHl with (y2:= init_y a).
                        + rewrite app_assoc. now auto.
                        + exact Hge1.
                        + discriminate.
                        + simpl. simpl in hd1. unfold hd1 in Hembedhd1. exact Hembedhd1.
                        + left. unfold tl2 in Hembedtl2cc. assert (last ([a]++ls2) default_segment = last ls2 default_segment). simpl. destruct ls2. contradiction. reflexivity. rewrite H1. now auto.
                        + rewrite app_assoc. exact HonSegtl2ex.
                        + rewrite <- app_assoc in Hsc. eapply consist_init_term in Hsc. unfold init_x, init_y. rewrite <- surjective_pairing. simpl in Hsc. rewrite <- Hsc. simpl. now eapply onTerm. discriminate. discriminate.
                        + unfold all_same_h in Hallh. destruct Hallh as [_ Hforall]. unfold all_same_h. split. discriminate. rewrite Forall_app in Hforall. now apply Hforall.
                      - admit. 
                  } 
                    ** exact Hembedtl2ex.
                    ** exact Hleyay1.
                    ** exact Hle.
                    ** exact Hgexax1.
              -- erewrite last_extend. exact HonSegtl2.
              -- exact Hleyay1.
            (* nwcxの場合 *)
            * eapply extended_segment_term_w_ncx with (x1:=x1) (y1:=y1) (x:=init_x a) in Hembedtl2cx as Hext.
              {
                destruct Hext as [y3 [HonSegtl2ex Hgtey1y3]]. destruct (Rtotal_order y3 (init_y a)) as [Hgt|[Heq|Hlt]].
                - rewrite <- app_assoc. eapply IHl.
                  + rewrite app_assoc. exact Hsc.
                  + exact Hgt.
                  + discriminate.
                  + simpl. simpl in hd1. unfold hd1 in Hembedhd1. exact Hembedhd1.
                  + right. unfold tl2 in Hembedtl2cx. assert (last ([a]++ls2) default_segment = last ls2 default_segment). simpl. destruct ls2. contradiction. reflexivity. rewrite H1. exact Hembedtl2cx.
                  + rewrite app_assoc. rewrite <- last_extend. exact HonSegtl2ex.
                  + rewrite <- app_assoc in Hsc. eapply consist_init_term in Hsc. unfold init_x, init_y. rewrite <- surjective_pairing. simpl in Hsc. rewrite <- Hsc. simpl. now eapply onTerm. discriminate. discriminate.
                  + unfold all_same_h in Hallh. destruct Hallh as [_ Hforall]. unfold all_same_h. split. discriminate. rewrite Forall_app in Hforall. now apply Hforall.
                
                - admit.

                - eapply x_cross_h with (s1:=nth (length (s0::ls1)) (extend (((s0 :: ls1) ++ [a]) ++ ls2)) default_segment) (s2:=tl2_ex).
                  * eapply nth_In. rewrite <- len_equal_extended. rewrite length_app. rewrite length_app. rewrite <- Nat.add_assoc. eapply Nat.lt_add_pos_r. simpl. now apply Nat.lt_0_succ.
                (* In (last (extend l) (extend l)) *)
                  * eapply exists_last in HnotNil. destruct HnotNil as [ls' alast]. destruct alast as [ls'' e]. subst. unfold tl2_ex.
                      assert (H_not_0: (length (extend (((s0::ls1) ++ [a]) ++ ls' ++ [ls''])) <> 0)%nat). rewrite <- len_equal_extended. simpl. discriminate. 
                      rewrite length_zero_iff_nil in H_not_0. eapply exists_last in H_not_0. destruct H_not_0 as [xl [x e]]. rewrite e. rewrite last_last. now eapply in_elt.
                  * assert (HonSega: onSegment (nth (length (s0 :: ls1)) (((s0 :: ls1) ++ [a]) ++ ls2) default_segment) (x1, y2)).
                        {
                          simpl. rewrite <- app_assoc. simpl. rewrite nth_middle. exact HonSegtl1.
                        }
                        eapply is_on_extended2. exact HonSega.
                  * assert (HonSega: onSegment (nth (length (s0 :: ls1)) (((s0 :: ls1) ++ [a]) ++ ls2) default_segment) (init a)).
                        {
                          simpl. rewrite <- app_assoc. simpl. rewrite nth_middle. now apply onInit. 
                        }
                        eapply is_on_extended2. rewrite surjective_pairing in HonSega. exact HonSega.
                  * exact HonSegtl2.
                  * unfold init_x in HonSegtl2ex. unfold tl2_ex. rewrite <- last_extend. exact HonSegtl2ex.
                  * eapply Rgt_minus in H0. eapply Rlt_minus in Hlt. eapply Rmult_pos_neg. exact H0. unfold init_y in Hlt. exact Hlt.
              }
              -- erewrite last_extend. exact HonSegtl2.
              -- exact Hgexax1.

Admitted.
    

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



Definition example1: list PrimitiveSegment := [(n,e,cx);(s,e,cx);(s,w,cc);(n,w,cc)].

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
                    eapply e_exist_y in Hembed1.
                        + destruct Hembed1 as [yy H']. exists yy. now apply H'.
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
                ++ simpl. unfold x1, y1. rewrite <- surjective_pairing with (p:=init s3). apply is_on_extended_last. now apply onInit with (s:=s3).
                ++ exact HonSeg.
                ++ unfold all_same_h. split. unfold not; discriminate. econstructor 2. exists n,cx. exact Hembed0. econstructor 2. exists s,cx. exact Hembed1. now econstructor 1.

              + set (x1 := fst (init s1)).
              set (y1 := snd (init s1)).
              assert (Hxins1:fst (init s1) < fst (init s2)).
                {rewrite <- Hconsis12. apply e_end_relation with (s:=s1) (v:=s) (c:=cx). exact Hembed1. }
              assert (Hyins1: exists y:R, onSegment s2 (x1, y)).
                {
                    eapply w_exist_y in Hembed2.
                    + destruct Hembed2 as [yy H']. exists yy. now apply H'.
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