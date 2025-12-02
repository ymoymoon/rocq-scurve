Require Import Admissible.
Require Import Reduction.
Require Import Stdlib.Reals.Reals.
Require Import ListExt.
Require Import Embed.
Require Import PrimitiveSegment.
Require Import Segment.
Import ListNotations.

(* 単方向 scurve *)
Parameter one_way_scurve : list Direction -> Prop.

(* scurve に直してから埋め込む． *)
Parameter embed_listDir : list Direction -> list Segment -> Prop.

(* TODO: 空リストは含まない．含めるなら，後の定理の必要な部分に not nil 制約を入れる *)
Parameter is_one_way_embedding : list Segment -> Prop.
Definition one_way_embedding := {ls : list Segment | is_one_way_embedding ls}.

(* 単方向曲線の始点と終点を結んだ線分を対角線にもつ矩形．部分曲線を含むとは限らない *)
Parameter rectangular_from_diagonal : R * R -> R * R -> (R * R -> Prop).
Definition rectangular_region (ls : one_way_embedding) : (R * R -> Prop) :=
	rectangular_from_diagonal (init (hd default_segment (proj1_sig ls))) (term (last (proj1_sig ls) default_segment)).
Definition in_rect ls rr := rectangular_region ls rr.

(* 疎：単方向曲線 sub_ls の周囲に全然関係ないセグメントが侵入してこない *)
Definition sparse (sub_ls : one_way_embedding) (ls : list Segment) : Prop :=
	sublist (proj1_sig sub_ls) ls
	/\ forall rr, 
		(exists seg, onExtendSegment ls seg rr) -> ~ in_rect sub_ls rr.


(* 許容可能ならば，疎な開埋め込みが存在する *)
Lemma embed_sparsely (dl dr : list Direction) (sub_ds : list Direction) :
	AdmissibleDirs (dl ++ sub_ds ++ dr)
	-> one_way_scurve sub_ds
	-> exists l r sub_ls, 
		embed_listDir dl l 
		/\ embed_listDir dr r 
		/\ embed_listDir sub_ds (proj1_sig sub_ls)
		/\ ~ close (l ++ (proj1_sig sub_ls) ++ r)
		/\ sparse sub_ls (l ++ (proj1_sig sub_ls) ++ r).
Proof. Admitted.

(* 矩形の中にピッタリ収まる1つのセグメントが描ける *)
Lemma embed_in_rectangle : forall (ls : one_way_embedding), 
	exists seg : Segment, 
		(forall rr, onSegment seg rr -> in_rect ls rr) 
		/\ init seg = init (hd default_segment (proj1_sig ls)) 
		/\ term seg = term (last (proj1_sig ls) default_segment).
Proof. Admitted.

(* 端点を含まない sub_ls の周りが疎な開埋め込みにおいて，sub_ls をその領域に収まるセグメントに置き換えても開のまま *)
Lemma seg_in_rectangle_keep_openness : forall sub_ls l ls r rs seg,
	~ close ((l :: ls) ++ (proj1_sig sub_ls) ++ (r :: rs))
	-> sparse sub_ls ((l :: ls) ++ (proj1_sig sub_ls) ++ (r :: rs))
	-> (forall rr, onSegment seg rr -> in_rect sub_ls rr) 
		/\ init seg = init (hd default_segment (proj1_sig sub_ls)) 
		/\ term seg = term (last (proj1_sig sub_ls) default_segment)
	-> ~ close ((l :: ls) ++ [seg] ++ (r :: rs)).
Proof. Admitted.

(* [+-+ => +] での簡約で許容可能性が保存される *)
Lemma AdmissibleDirs_r1_Plus: forall l r,
  AdmissibleDirs (l ++ [Plus; Minus; Plus] ++ r) -> AdmissibleDirs (l ++ [Plus] ++ r).
Proof.
	remember [Plus; Minus; Plus] as PMP eqn: HeqPMP.
	intros l r admds. destruct l as [ | l'].
	- (* 端点を含む簡約 *) admit.
	- destruct r as [ | r'].
		+ (* 端点を含む簡約 *) admit.
		+ (* 簡約にかかわった部分の両端に別のセグメントが存在する場合 *)
			assert (Honeway : one_way_scurve PMP). {
				admit.
			}
			apply (embed_sparsely _ _ _ admds) in Honeway as 
				[ll [lr [sub_ls [Hl [Hr [HPMP [Hopen Hsparse]]]]]]].
			unfold AdmissibleDirs. intros ps Hps. unfold admissible.
			destruct (embed_in_rectangle sub_ls) as 
				[seg [Hin_rect [Hinit Hterm]]].
			exists (ll ++ [seg] ++ lr). split.
			* (* 簡約後の向き列の埋め込みになっていること *) admit.
			* (* その埋め込みが開であること *) admit.
			(* apply seg_in_rectangle_keep_openness. *)
Admitted.
