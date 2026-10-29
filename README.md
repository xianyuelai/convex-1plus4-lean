# Convex central configurations in the planar (1+4)-body problem

**Author: Kaitai Xiao**

Paper: [Uniqueness of convex central configurations in the planar (1+4)-body problem — arXiv:2610.04563](https://arxiv.org/abs/2610.04563).

This repository publishes the paper and its accompanying Lean formalization.

## GPT-6 disclosure

**This paper and its accompanying Lean formalization were developed by the author with GPT-6.**

本论文及配套 Lean 形式化由作者使用 **GPT-6** 完成。

## Version status: v1 now; v2 will be the final version

**The current release is v1, an initial archived version. A revised v2 will be uploaded as the final version.** The v1 paper, code and verification records will remain archived; v2 will have its own source correspondence and verification record.

**当前为初始归档版本 v1；未来将上传修订版 v2，作为最终版本。** v1 将继续保留，v2 将有独立的原文对应审查与形式化验收记录。

## Paper, code and verified archive

- [v1 paper PDF](dominant-five-body-lean-v1/source/convex_1plus4.pdf)
- [v1 paper TeX](dominant-five-body-lean-v1/source/convex_1plus4.tex)
- [Browse the complete v1 Lean project](dominant-five-body-lean-v1/)
- [Download the verified v1 archive](downloads/dominant-five-body-lean-v1.zip)
- [Archive SHA-256](downloads/dominant-five-body-lean-v1.zip.sha256)
- [Verification and reproduction instructions](dominant-five-body-lean-v1/README.md)
- [v1 acceptance record](dominant-five-body-lean-v1/logs/PAPER_ACCEPTANCE.json)
- [Source-to-Lean correspondence review](dominant-five-body-lean-v1/docs/V1_CORRESPONDENCE_REVIEW.md)
- [Verification scope](dominant-five-body-lean-v1/docs/VERIFICATION_SCOPE.md)

The frozen v1 acceptance record reports **280 mathematical modules, 349 source-ledger records, 622 checked declaration-type bindings and 57 checked definition-value bindings**. The clean project rebuild, axiom audit and fresh kernel replays succeeded. The observed axioms are `propext`, `Classical.choice` and `Quot.sound`.

Source correspondence is documented separately from Lean kernel checking. PDF/TeX correspondence was checked by rebuilding the TeX and comparing the complete extracted layout text. Fresh replay uses the same Lean kernel; it is not a second independent kernel implementation.

The accepted project is preserved byte-for-byte under `dominant-five-body-lean-v1/`. This repository-level README records publication information and does not alter the frozen v1 project or its acceptance receipt. Dependency caches are excluded.

```powershell
cd dominant-five-body-lean-v1
pwsh -NoProfile -File scripts/verify_paper.ps1 -Clean
```

Use the locked Lean 4.33.1 and dependency revisions described in the project README; do not run `lake update` when reproducing v1.

Archive SHA-256:

```text
5003AB7A1CCECEC1BFEA668044BB21028D8C58998AE0669B6B9A044BD8783CDD
```
