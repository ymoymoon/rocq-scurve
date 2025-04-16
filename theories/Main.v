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


(*セグメントは[0,1]->R*Rの関数のうち次の条件を満たしたもの
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


Parameter Segment : Set.

Parameter embed : PrimitiveSegment -> Segment -> Prop.

Parameter init : Segment -> R * R.

Parameter term : Segment -> R * R.

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

(* 始点と終点の間にあるx座標を取ると，そのx座標の点がセグメント上にあることを示す公理 *)
Axiom e_exist_y: forall (s:Segment) (v:V) (c:C) (x:R),
    embed (v, e, c) s -> fst (init s) <= x -> x <= fst (term s) -> exists y:R, onSegment s (x, y).
Axiom w_exist_y: forall (s:Segment) (v:V) (c:C) (x:R),
    embed (v, w, c) s -> fst (term s) <= x -> x <= fst (init s) -> exists y:R, onSegment s (x, y).

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

(* 埋め込んだ曲線を延長する *)
Parameter extend: list Segment -> list Segment.

Parameter crossed: Segment -> Segment -> Prop.

Definition head_seg (ls: list Segment) (default: Segment) : Segment :=
    match ls with
    | [] => default
    | hd :: _ => hd
    end.

Fixpoint tail_seg (ls: list Segment) (default: Segment): Segment :=
    match ls with
    | [] => default
    | hd :: [] => hd
    | _ :: res => tail_seg res default
    end.

(* close, 閉 *)
Definition close (ls: list Segment) : Prop :=
    (exists (s1 s2: Segment), In s1 (extend ls) -> In s2 (extend ls) -> crossed s1 s2).

(* admissible, 許容可能 *)
Definition admissible (lp: scurve) : Prop :=
    exists ls: list Segment, (embed_scurve lp ls /\ ~ close ls).


Parameter default_segment : Segment.
(* 最初から特定のセグメントsまで同じ水平方向を向いていることを表す命題 *)
Inductive all_same_h: list Segment -> Segment -> H -> Prop :=
| AllSameHS : forall (ls: list Segment) (ps: PrimitiveSegment),
    let s := head_seg ls default_segment in 
    embed ps s
    -> all_same_h ls s (H_of ps)
| AllSameHNext : forall (ls: list Segment) (s hd: Segment) (ps: PrimitiveSegment),
    all_same_h ls s (H_of ps)
    ->  embed ps hd
    -> all_same_h (hd :: ls) s (H_of ps).

(* n,e,cxから始まり，しばらく右に伸びている，(x1, y2)を通る．
最後のセグメントが左上で，(x1, y1)を通る．
y1<=y2の時に最後のセグメントはどこかで交わる*)
Axiom end_cross_term_nw:
    forall (ls: list Segment) (x1 y1 y2: R) (s1: Segment),
    let hd := head_seg ls default_segment in
    let tl := tail_seg ls default_segment in
    y1 <= y2
    -> embed (n, e, cx) hd
    -> embed (n, w, cc) tl \/ embed (n, w, cx) tl
    -> onSegment tl (x1, y1)
    -> onSegment s1 (x1, y2)
    -> all_same_h ls s1 e
    -> close ls.
Axiom end_cross_init_ne:
    forall (ls: list Segment) (x1 y1 y2: R) (s1: Segment),
    let hd := head_seg ls default_segment in
    let tl := tail_seg ls default_segment in
    y2 <= y1
    -> embed (n, e, cc) hd \/ embed (n, e, cx) hd
    -> embed (n, w, cc) tl
    -> onSegment hd (x1, y1)
    -> onSegment s1 (x1, y2)
    -> all_same_h (rev ls) s1 w
    -> close ls.


Definition example1: list PrimitiveSegment := [(n,e,cx);(s,e,cx);(s,w,cc);(n,w,cc)].

Lemma example1_is_close: forall lp: scurve, proj1_sig lp = example1 -> ~ admissible lp.
Proof.
    intros lp.
    destruct lp as [l p].
    simpl.
    unfold example1.
    intros H0.
    unfold admissible, not.
    intros H1.
    destruct H1 as [ls [H2 H3]].
    destruct ls as [| s0].
    - inversion H2. rewrite H0 in H4. inversion H4.
    - destruct ls as [| s1].
     -- inversion H2. rewrite H0 in H1. inversion H1.
     -- destruct ls as [| s2].
      --- inversion H2. inversion H8. rewrite <- H11 in H1. simpl in H1. rewrite H0 in H1. inversion H1.
      --- destruct ls as [| s3].
       ---- inversion H2. inversion H8. inversion H15. rewrite <- H13 in H1. simpl in H1. rewrite <- H18 in H1. simpl in H1. rewrite H0 in H1. inversion H1.
       ---- destruct ls as [| overseg].
            * inversion H2 as [| |p0 scurve13 H s0' s1' ls Hembed0].
              inversion H1 as [| |p1 scurve23 Hdcpseg123 s1'' s2' ls' Hembed1].
              inversion H9 as [| |p2 scurve3 Hdcpseg23 s2'' s3' ls'' Hembed2].
              inversion H15 as [| p3 s3'' Hembed3| ].
              apply H3.
              rewrite <- H11 in H5. simpl in H5.
              rewrite <- H17 in H5. simpl in H5.
              rewrite <- H21 in H5. simpl in H5.
              rewrite H0 in H5.
              inversion H5.
              rewrite H24 in Hembed0.
              rewrite H25 in Hembed1.
              rewrite H26 in Hembed2.
              rewrite H27 in Hembed3.
              destruct (Rle_or_lt (fst (init s1)) (fst (term s2))) as [Hge | Hlt].
              + set (x1 := fst (init s3)).
              set (y1 := snd (init s3)).
              assert (Hxins1:fst (term s2) < fst (term s1)). 
                {rewrite H10. apply w_end_relation with (s:=s2) (v:=s) (c:=cc). apply Hembed2. }
              assert (Hyins1: exists y:R, onSegment s1 (x1, y)).
                {apply e_exist_y with (v:=s) (c:=cx). apply Hembed1. unfold x1. rewrite <- H16. apply Hge. unfold x1. rewrite <- H16.
                apply Rlt_le. apply Hxins1. }
              destruct Hyins1 as [y2 HonSeg].
              apply end_cross_term_nw with (ls := (s0::s1::s2::s3::[])) (x1:=x1) (y1:=y1) (y2:= y2) (s1:=s1).
                ++ apply Rle_trans with (r2 := snd (term s1)). apply Rlt_le. unfold y1. rewrite <- H16. rewrite H10. apply s_end_relation with (s1:=s2) (h:=w) (c:=cc). apply Hembed2.
                    apply s_onseg_relation with (s1:=s1) (h:=e) (c:=cx) (x:=x1) (y:=y2). apply Hembed1. apply HonSeg. 
                ++ simpl. apply Hembed0.
                ++ simpl. left. apply Hembed3.
                ++ simpl. unfold x1, y1. rewrite <- surjective_pairing with (p:=init s3). apply onInit with (s:=s3).
                ++ apply HonSeg.
                ++ constructor 2 with (ls:=[s1;s2;s3]) (s:=s1) (hd:=s0) (ps:=(n,e,cx)). constructor 1 with (ls:=[s1;s2;s3]) (ps:=(s,e,cx)). simpl. apply Hembed1. apply Hembed0.

              + set (x1 := fst (init s1)).
              set (y1 := snd (init s1)).
              assert (Hxins1:fst (init s1) < fst (init s2)).
                {rewrite <- H10. apply e_end_relation with (s:=s1) (v:=s) (c:=cx). apply Hembed1. }
              assert (Hyins1: exists y:R, onSegment s2 (x1, y)).
                {apply w_exist_y with (v:=s) (c:=cc). apply Hembed2. unfold x1. apply Rlt_le. apply Hlt. unfold x1. apply Rlt_le. apply Hxins1. }
              destruct Hyins1 as [y2 HonSeg].
              apply end_cross_init_ne with (ls := (s0::s1::s2::s3::[])) (x1:=x1) (y1:=y1) (y2:= y2) (s1:=s2).
                ++ apply Rle_trans with (r2:= snd (term s1)). unfold y1. rewrite H10. apply s_onseg_relation with (s1:=s2) (h:=w) (c:=cc) (x:= x1) (y:=y2). apply Hembed2. apply HonSeg. 
                    unfold y1. apply Rlt_le. apply s_end_relation with (s1:=s1) (h:=e) (c:=cx). apply Hembed1.
                ++ simpl. right. apply Hembed0.
                ++ simpl. apply Hembed3.
                ++ simpl. unfold x1, y1. rewrite <- surjective_pairing. rewrite <- H4. apply onTerm with (s:=s0).
                ++ apply HonSeg.
                ++ simpl. constructor 2 with (ls:=[s2;s1;s0]) (s:=s2) (hd:=s3) (ps:=(n,w,cc)). constructor 1 with (ls:=[s2;s1;s0]) (ps:=(s,w,cc)). simpl. apply Hembed2. apply Hembed3.
            * inversion H2. inversion H8. inversion H15. inversion H22. rewrite <- H13 in H1. simpl in H1. rewrite <- H20 in H1. simpl in H1. rewrite <- H27 in H1. simpl in H1. inversion H29. 
            ** rewrite <- H32 in H1. simpl in H1. rewrite H0 in H1. inversion H1.
            ** rewrite <- H34 in H1. simpl in H1. rewrite H0 in H1. inversion H1.
Qed. 



    
