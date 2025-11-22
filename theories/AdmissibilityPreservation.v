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

Definition one_way_embedding (ls : list Segment) : Prop :=
exists ds, embed_listDir ds ls /\ one_way_scurve ds.

(* (基本，単方向曲線の)始点と終点を結んだ線分を対角線にもつ矩形 *)
Parameter rectangular_region : list Segment -> (R * R -> Prop).
Definition in_rect ls rr := rectangular_region ls rr.

(* 疎：単方向曲線 sub_ls の周囲に全然関係ないセグメントが侵入してこない *)
Definition sparse (sub_ls ls : list Segment) : Prop :=
	sublist sub_ls ls
	/\ one_way_embedding sub_ls
	/\ forall rr, 
		(exists seg, onExtendSegment ls seg rr) -> ~ in_rect sub_ls rr.


(* 許容可能ならば，疎な開埋め込みが存在する *)
Lemma embed_sparsely (ds : list Direction) (sub_ds : list Direction) :
	AdmissibleDirs ds
	-> sublist sub_ds ds
	-> one_way_scurve sub_ds
	-> exists ls sub_ls, 
		embed_listDir ds ls 
		/\ ~ close ls
		/\ embed_listDir sub_ds sub_ls
		/\ sublist sub_ls ls
		/\ sparse sub_ls ls.
Proof. Admitted.

(* 矩形の中にピッタリ収まる1つのセグメントが描ける *)
Lemma embed_in_rectangle : forall (ls : list Segment), 
	ls <> [] -> exists seg : Segment, 
		(forall rr, onSegment seg rr -> in_rect ls rr) 
		/\ init seg = init (hd default_segment ls) 
		/\ term seg = term (last ls default_segment).

(* [+-+ => +] での簡約で許容可能性が保存される *)
Lemma AdmissibleDirs_r1_Plus: forall l r,
  AdmissibleDirs (l ++ [Plus; Minus; Plus] ++ r) -> AdmissibleDirs (l ++ [Plus] ++ r).
Proof.
	remember [Plus; Minus; Plus] as PMP eqn: HeqPMP.
	intros l r admds. destruct l as [ | l'].
	- admit.
	- destruct r as [ | r'].
		+ admit.
		+ (* 簡約にかかわった部分の両端に別のセグメントが存在する場合 *)
		assert (Hsub : sublist PMP ((l' :: l) ++ PMP ++ r' :: r)). {
			admit.
		} assert (Honeway : one_way_scurve PMP). {
			admit.
		}
		apply (embed_sparsely _ _ admds Hsub) in Honeway as 
			[sparse_embedding [PMP_embedding [Hembed [Hopen [Hsub1 [Hsub2 Hsparse]]]]]].