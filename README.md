# Formalization of Admissibility of Qualitatively Represented Curves using Rocq

This repository formalizes and proves the Admissibility condition in Takahashi's theory of Qualitatively Represented Curve using the formal verification tool Rocq Prover.

## Abstract

This project formalizes definitions and corollaries/theorems on Admissibility of trajectories in QRC in Rocq's proof environment.
This gives a mechanical justification guarantee to the theory of QRC, which is spoken geometrically.

## Correspondence with the Paper
| Paper (Japanese one) | Rocq Code |
| ---- | ---- |
| Def.2 | PrimitiveSegment.dc |
| Def.4 |  |
| Def.5 | Embed.embed, Embed.embed_scurve |
| Def.6 | Segment.close |
| Def.7 | Embed.admissible (used in examples), Admissible.AdmissibleDirs |
| Prop.1 |  |
| Def.8 | (Reduction.orn, Reduction.Reduce) |
| Def.11 | Admissible.reduced |
| Prop.2(1) | Reduction.termination |
| Prop.2(2) | Reduction.rotation_difference_preservation |
| Prop.2(3) | Reduction.reduced_form |
| NOT valid (Example.5) | Reduction.ReduceDir_local_confluence |
| Prop.3 |  |
| Prop.4 |  |
| Th.1(->) | Admissible.AdmissibleDirs_preserve |
| Th.1(<-) |  |
| Sec.4.1-4.7 | (Admissible.all_admissibles_quotient) |
| Th.2 |  |

## Requirement

- [opam](https://opam.ocaml.org/doc/Install.html)
- [Rocq prover](https://rocq-prover.org/install)

## How to Build

```
./configure.sh
make
```

## References

* Takahashi, K.: "[Reasoning about the Embedded Shape of a Qualitatively Represented Curve](https://ist.ksc.kwansei.ac.jp/~ktaka/LABO/DRAFTS/SCSS2024takahashi.pdf)," SCSS 2024 WIP: 10th International Symposium on Symbolic Computation in Software Science - Work in Progress Workshop, pp.113-118, ISSN: 1613-0073, CEUR Workshop Proceedings, August, 2024.
* 高橋和子: "[曲線の定性的扱いと自己交差性の判定](https://ist.ksc.kwansei.ac.jp/~ktaka/LABO/DRAFTS/PRO2024takahashi.pdf)," 情報処理学会第149回PRO研究会資料, June, 2024. 
