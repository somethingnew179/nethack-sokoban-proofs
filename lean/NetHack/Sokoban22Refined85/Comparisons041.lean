/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons040
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare5740 (p : Pattern) (guard : d4476 p = 1) : d717 p ≤ (0 : Int) + d4481 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5673 p hg
    simpa only [d4476, d717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5739 p hg
    simpa only [d4476, d717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5741 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d4488 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5742 (p : Pattern) (guard : d4476 p = 1) : d714 p ≤ (0 : Int) + d4488 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5694 p hg
    simpa only [d4476, d714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5741 p hg
    simpa only [d4476, d714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5743 (p : Pattern) (guard : d4476 p = 1) : d718 p ≤ (0 : Int) + d4489 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d718, d4489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5740 p hg
    simpa only [d718, d4489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d718, d4489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5742 p hg
    simpa only [d718, d4489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5744 (p : Pattern) (guard : d4476 p = 1) : d738 p ≤ (0 : Int) + d4499 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d738, d4499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5743 p hg
    simpa only [d738, d4499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d738, d4499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5725 p hg
    simpa only [d738, d4499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5745 (p : Pattern) (guard : d4476 p = 1) : d739 p ≤ (0 : Int) + d4511 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d739, d4511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5744 p hg
    simpa only [d739, d4511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d739, d4511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5728 p hg
    simpa only [d739, d4511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5746 (p : Pattern) (guard : d4476 p = 1) : d740 p ≤ (0 : Int) + d4512 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d740, d4512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5738 p hg
    simpa only [d740, d4512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d740, d4512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5745 p hg
    simpa only [d740, d4512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5747 (p : Pattern) (guard : d4476 p = 1) : d741 p ≤ (0 : Int) + d4512 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5730 p hg
    simpa only [d741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5746 p hg
    simpa only [d741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5748 (p : Pattern) (guard : d0 p = 1) : d103 p ≤ (0 : Int) + d103 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5749 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d103 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5750 (p : Pattern) (guard : d4474 p = 1) : d104 p ≤ (0 : Int) + d103 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d4474, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5749 p hg
    simpa only [d4474, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5751 (p : Pattern) (guard : d4475 p = 1) : d105 p ≤ (0 : Int) + d103 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5748 p hg
    simpa only [d4475, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5750 p hg
    simpa only [d4475, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5752 (p : Pattern) (guard : d0 p = 1) : d107 p ≤ (0 : Int) + d107 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5753 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d107 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5754 (p : Pattern) (guard : d4474 p = 1) : d108 p ≤ (0 : Int) + d107 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2051 p hg
    simpa only [d4474, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5753 p hg
    simpa only [d4474, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5755 (p : Pattern) (guard : d4475 p = 1) : d109 p ≤ (0 : Int) + d107 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5752 p hg
    simpa only [d4475, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5754 p hg
    simpa only [d4475, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5756 (p : Pattern) (guard : d4475 p = 1) : d110 p ≤ (0 : Int) + d4513 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d110, d4513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5751 p hg
    simpa only [d110, d4513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d110, d4513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5755 p hg
    simpa only [d110, d4513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5757 (p : Pattern) (guard : d4475 p = 1) : d111 p ≤ (0 : Int) + d4514 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d111, d4514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5751 p hg
    simpa only [d111, d4514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d111, d4514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5756 p hg
    simpa only [d111, d4514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5758 (p : Pattern) (guard : d4475 p = 1) : d112 p ≤ (0 : Int) + d4515 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d112, d4515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5686 p hg
    simpa only [d112, d4515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d112, d4515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5670 p hg
    simpa only [d112, d4515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5759 (p : Pattern) (guard : d4475 p = 1) : d113 p ≤ (0 : Int) + d4516 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d113, d4516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5756 p hg
    simpa only [d113, d4516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d113, d4516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5758 p hg
    simpa only [d113, d4516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5760 (p : Pattern) (guard : d4475 p = 1) : d114 p ≤ (0 : Int) + d4517 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d114, d4517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5757 p hg
    simpa only [d114, d4517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d114, d4517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5759 p hg
    simpa only [d114, d4517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5761 (p : Pattern) (guard : d0 p = 1) : d398 p ≤ (0 : Int) + d4517 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5762 (p : Pattern) (guard : d4476 p = 1) : d742 p ≤ (0 : Int) + d4517 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5760 p hg
    simpa only [d4476, d742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5761 p hg
    simpa only [d4476, d742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5763 (p : Pattern) (guard : d0 p = 1) : d116 p ≤ (0 : Int) + d116 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5764 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d116 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5765 (p : Pattern) (guard : d4474 p = 1) : d117 p ≤ (0 : Int) + d116 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d4474, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5764 p hg
    simpa only [d4474, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5766 (p : Pattern) (guard : d4475 p = 1) : d132 p ≤ (0 : Int) + d116 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5763 p hg
    simpa only [d4475, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5765 p hg
    simpa only [d4475, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5767 (p : Pattern) (guard : d4475 p = 1) : d133 p ≤ (0 : Int) + d4518 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d133, d4518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5751 p hg
    simpa only [d133, d4518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d133, d4518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5766 p hg
    simpa only [d133, d4518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5768 (p : Pattern) (guard : d4475 p = 1) : d134 p ≤ (0 : Int) + d4519 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d134, d4519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5755 p hg
    simpa only [d134, d4519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d134, d4519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5686 p hg
    simpa only [d134, d4519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5769 (p : Pattern) (guard : d4475 p = 1) : d135 p ≤ (0 : Int) + d4520 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d135, d4520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5767 p hg
    simpa only [d135, d4520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d135, d4520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5768 p hg
    simpa only [d135, d4520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5770 (p : Pattern) (guard : d4475 p = 1) : d136 p ≤ (0 : Int) + d4521 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d136, d4521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5755 p hg
    simpa only [d136, d4521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d136, d4521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5691 p hg
    simpa only [d136, d4521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5771 (p : Pattern) (guard : d4475 p = 1) : d137 p ≤ (0 : Int) + d4522 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d137, d4522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5770 p hg
    simpa only [d137, d4522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d137, d4522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5670 p hg
    simpa only [d137, d4522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5772 (p : Pattern) (guard : d4475 p = 1) : d138 p ≤ (0 : Int) + d4523 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d138, d4523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5769 p hg
    simpa only [d138, d4523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d138, d4523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5771 p hg
    simpa only [d138, d4523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5773 (p : Pattern) (guard : d0 p = 1) : d409 p ≤ (0 : Int) + d4523 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5774 (p : Pattern) (guard : d4476 p = 1) : d743 p ≤ (0 : Int) + d4523 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5772 p hg
    simpa only [d4476, d743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5773 p hg
    simpa only [d4476, d743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5775 (p : Pattern) (guard : d4476 p = 1) : d744 p ≤ (0 : Int) + d4524 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d744, d4524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5762 p hg
    simpa only [d744, d4524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d744, d4524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5774 p hg
    simpa only [d744, d4524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5776 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d4527 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5777 (p : Pattern) (guard : d4476 p = 1) : d745 p ≤ (0 : Int) + d4528 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d745, d4528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5760 p hg
    simpa only [d4476, d745, d4528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d745, d4528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5776 p hg
    simpa only [d4476, d745, d4528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5778 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d4531 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5779 (p : Pattern) (guard : d4476 p = 1) : d746 p ≤ (0 : Int) + d4532 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d746, d4532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5772 p hg
    simpa only [d4476, d746, d4532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d746, d4532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5778 p hg
    simpa only [d4476, d746, d4532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5780 (p : Pattern) (guard : d4476 p = 1) : d747 p ≤ (0 : Int) + d4533 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d747, d4533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5777 p hg
    simpa only [d747, d4533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d747, d4533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5779 p hg
    simpa only [d747, d4533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5781 (p : Pattern) (guard : d4476 p = 1) : d748 p ≤ (0 : Int) + d4534 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d748, d4534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5775 p hg
    simpa only [d748, d4534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d748, d4534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5780 p hg
    simpa only [d748, d4534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5782 (p : Pattern) (guard : d0 p = 1) : d396 p ≤ (0 : Int) + d4527 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5783 (p : Pattern) (guard : d4476 p = 1) : d749 p ≤ (0 : Int) + d4528 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d749, d4528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5760 p hg
    simpa only [d4476, d749, d4528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d749, d4528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5782 p hg
    simpa only [d4476, d749, d4528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5784 (p : Pattern) (guard : d4476 p = 1) : d750 p ≤ (0 : Int) + d4533 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d750, d4533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5783 p hg
    simpa only [d750, d4533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d750, d4533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5779 p hg
    simpa only [d750, d4533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5785 (p : Pattern) (guard : d4475 p = 1) : d159 p ≤ (0 : Int) + d4535 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d159, d4535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5758 p hg
    simpa only [d159, d4535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d159, d4535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5670 p hg
    simpa only [d159, d4535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5786 (p : Pattern) (guard : d4475 p = 1) : d160 p ≤ (0 : Int) + d4536 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d160, d4536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5785 p hg
    simpa only [d160, d4536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d160, d4536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5670 p hg
    simpa only [d160, d4536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5787 (p : Pattern) (guard : d4476 p = 1) : d161 p ≤ (0 : Int) + d4537 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d161, d4537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5786 p hg
    simpa only [d4476, d161, d4537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d161, d4537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4476, d161, d4537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5788 (p : Pattern) (guard : d4476 p = 1) : d162 p ≤ (0 : Int) + d4538 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d162, d4538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5787 p hg
    simpa only [d162, d4538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d162, d4538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5727 p hg
    simpa only [d162, d4538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5789 (p : Pattern) (guard : d4476 p = 1) : d751 p ≤ (0 : Int) + d4539 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d751, d4539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5784 p hg
    simpa only [d751, d4539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d751, d4539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5788 p hg
    simpa only [d751, d4539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5790 (p : Pattern) (guard : d4476 p = 1) : d752 p ≤ (0 : Int) + d4540 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d752, d4540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5781 p hg
    simpa only [d752, d4540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d752, d4540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5789 p hg
    simpa only [d752, d4540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5791 (p : Pattern) (guard : d0 p = 1) : d405 p ≤ (0 : Int) + d4517 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5792 (p : Pattern) (guard : d4476 p = 1) : d753 p ≤ (0 : Int) + d4517 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5760 p hg
    simpa only [d4476, d753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5791 p hg
    simpa only [d4476, d753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5793 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d4523 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5794 (p : Pattern) (guard : d4476 p = 1) : d746 p ≤ (0 : Int) + d4523 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5772 p hg
    simpa only [d4476, d746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5793 p hg
    simpa only [d4476, d746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5795 (p : Pattern) (guard : d4476 p = 1) : d754 p ≤ (0 : Int) + d4524 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d754, d4524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5792 p hg
    simpa only [d754, d4524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d754, d4524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5794 p hg
    simpa only [d754, d4524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5796 (p : Pattern) (guard : d4476 p = 1) : d755 p ≤ (0 : Int) + d4534 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d755, d4534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5795 p hg
    simpa only [d755, d4534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d755, d4534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5780 p hg
    simpa only [d755, d4534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5797 (p : Pattern) (guard : d4476 p = 1) : d756 p ≤ (0 : Int) + d4541 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d756, d4541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5780 p hg
    simpa only [d756, d4541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d756, d4541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5727 p hg
    simpa only [d756, d4541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5798 (p : Pattern) (guard : d4476 p = 1) : d757 p ≤ (0 : Int) + d4542 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d757, d4542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5796 p hg
    simpa only [d757, d4542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d757, d4542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5797 p hg
    simpa only [d757, d4542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5799 (p : Pattern) (guard : d4476 p = 1) : d758 p ≤ (0 : Int) + d4543 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d758, d4543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5790 p hg
    simpa only [d758, d4543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d758, d4543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5798 p hg
    simpa only [d758, d4543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5800 (p : Pattern) (guard : d4476 p = 1) : d759 p ≤ (0 : Int) + d4544 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d759, d4544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5730 p hg
    simpa only [d759, d4544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d759, d4544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5799 p hg
    simpa only [d759, d4544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5801 (p : Pattern) (guard : d4476 p = 1) : d760 p ≤ (0 : Int) + d4545 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d760, d4545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5747 p hg
    simpa only [d760, d4545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d760, d4545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5800 p hg
    simpa only [d760, d4545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5802 (p : Pattern) (guard : d0 p = 1) : d405 p ≤ (0 : Int) + d4547 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5803 (p : Pattern) (guard : d4476 p = 1) : d717 p ≤ (0 : Int) + d4548 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d717, d4548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5673 p hg
    simpa only [d4476, d717, d4548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d717, d4548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5802 p hg
    simpa only [d4476, d717, d4548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5804 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d4552 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5805 (p : Pattern) (guard : d4476 p = 1) : d714 p ≤ (0 : Int) + d4553 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d714, d4553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5694 p hg
    simpa only [d4476, d714, d4553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d714, d4553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5804 p hg
    simpa only [d4476, d714, d4553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5806 (p : Pattern) (guard : d4476 p = 1) : d718 p ≤ (0 : Int) + d4554 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d718, d4554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5803 p hg
    simpa only [d718, d4554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d718, d4554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5805 p hg
    simpa only [d718, d4554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5807 (p : Pattern) (guard : d0 p = 1) : d35 p ≤ (0 : Int) + d35 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5808 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d35 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5809 (p : Pattern) (guard : d4474 p = 1) : d36 p ≤ (0 : Int) + d35 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3072 p hg
    simpa only [d4474, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5808 p hg
    simpa only [d4474, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5810 (p : Pattern) (guard : d4475 p = 1) : d78 p ≤ (0 : Int) + d35 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5807 p hg
    simpa only [d4475, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5809 p hg
    simpa only [d4475, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5811 (p : Pattern) (guard : d4475 p = 1) : d79 p ≤ (0 : Int) + d4490 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d79, d4490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5679 p hg
    simpa only [d79, d4490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d79, d4490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5810 p hg
    simpa only [d79, d4490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5812 (p : Pattern) (guard : d4475 p = 1) : d188 p ≤ (0 : Int) + d4555 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d188, d4555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5659 p hg
    simpa only [d188, d4555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d188, d4555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5811 p hg
    simpa only [d188, d4555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5813 (p : Pattern) (guard : d4475 p = 1) : d80 p ≤ (0 : Int) + d4491 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d80, d4491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5811 p hg
    simpa only [d80, d4491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d80, d4491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5692 p hg
    simpa only [d80, d4491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5814 (p : Pattern) (guard : d4475 p = 1) : d189 p ≤ (0 : Int) + d4556 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d189, d4556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5812 p hg
    simpa only [d189, d4556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d189, d4556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5813 p hg
    simpa only [d189, d4556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5815 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d4559 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5816 (p : Pattern) (guard : d4476 p = 1) : d761 p ≤ (0 : Int) + d4560 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d761, d4560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5814 p hg
    simpa only [d4476, d761, d4560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d761, d4560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5815 p hg
    simpa only [d4476, d761, d4560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5817 (p : Pattern) (guard : d4475 p = 1) : d198 p ≤ (0 : Int) + d4561 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d198, d4561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5663 p hg
    simpa only [d198, d4561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d198, d4561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5691 p hg
    simpa only [d198, d4561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5818 (p : Pattern) (guard : d4475 p = 1) : d199 p ≤ (0 : Int) + d4562 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d199, d4562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5679 p hg
    simpa only [d199, d4562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d199, d4562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5817 p hg
    simpa only [d199, d4562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5819 (p : Pattern) (guard : d4475 p = 1) : d83 p ≤ (0 : Int) + d4494 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d83, d4494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5810 p hg
    simpa only [d83, d4494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d83, d4494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5670 p hg
    simpa only [d83, d4494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5820 (p : Pattern) (guard : d4475 p = 1) : d84 p ≤ (0 : Int) + d4495 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d84, d4495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5819 p hg
    simpa only [d84, d4495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d84, d4495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5670 p hg
    simpa only [d84, d4495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5821 (p : Pattern) (guard : d4475 p = 1) : d200 p ≤ (0 : Int) + d4563 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d200, d4563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5818 p hg
    simpa only [d200, d4563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d200, d4563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5820 p hg
    simpa only [d200, d4563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5822 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d4566 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5823 (p : Pattern) (guard : d4476 p = 1) : d762 p ≤ (0 : Int) + d4567 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d762, d4567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5821 p hg
    simpa only [d4476, d762, d4567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d762, d4567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5822 p hg
    simpa only [d4476, d762, d4567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5824 (p : Pattern) (guard : d4476 p = 1) : d763 p ≤ (0 : Int) + d4568 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d763, d4568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5816 p hg
    simpa only [d763, d4568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d763, d4568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5823 p hg
    simpa only [d763, d4568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5825 (p : Pattern) (guard : d4476 p = 1) : d764 p ≤ (0 : Int) + d4569 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d764, d4569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5806 p hg
    simpa only [d764, d4569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d764, d4569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5824 p hg
    simpa only [d764, d4569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5826 (p : Pattern) (guard : d4476 p = 1) : d765 p ≤ (0 : Int) + d4570 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d765, d4570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5824 p hg
    simpa only [d765, d4570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d765, d4570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5727 p hg
    simpa only [d765, d4570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5827 (p : Pattern) (guard : d4476 p = 1) : d766 p ≤ (0 : Int) + d4571 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d766, d4571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5825 p hg
    simpa only [d766, d4571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d766, d4571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5826 p hg
    simpa only [d766, d4571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5828 (p : Pattern) (guard : d4476 p = 1) : d767 p ≤ (0 : Int) + d4572 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d767, d4572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5738 p hg
    simpa only [d767, d4572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d767, d4572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5827 p hg
    simpa only [d767, d4572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5829 (p : Pattern) (guard : d4476 p = 1) : d768 p ≤ (0 : Int) + d4573 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d768, d4573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5730 p hg
    simpa only [d768, d4573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d768, d4573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5828 p hg
    simpa only [d768, d4573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5830 (p : Pattern) (guard : d4475 p = 1) : d211 p ≤ (0 : Int) + d4574 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d211, d4574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5755 p hg
    simpa only [d211, d4574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d211, d4574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5670 p hg
    simpa only [d211, d4574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5831 (p : Pattern) (guard : d4475 p = 1) : d212 p ≤ (0 : Int) + d4575 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d212, d4575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5767 p hg
    simpa only [d212, d4575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d212, d4575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5830 p hg
    simpa only [d212, d4575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5832 (p : Pattern) (guard : d4475 p = 1) : d213 p ≤ (0 : Int) + d4576 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d213, d4576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5830 p hg
    simpa only [d213, d4576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d213, d4576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5670 p hg
    simpa only [d213, d4576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5833 (p : Pattern) (guard : d4475 p = 1) : d214 p ≤ (0 : Int) + d4577 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d214, d4577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5831 p hg
    simpa only [d214, d4577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d214, d4577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5832 p hg
    simpa only [d214, d4577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5834 (p : Pattern) (guard : d0 p = 1) : d409 p ≤ (0 : Int) + d4577 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5835 (p : Pattern) (guard : d4476 p = 1) : d769 p ≤ (0 : Int) + d4577 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5833 p hg
    simpa only [d4476, d769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5834 p hg
    simpa only [d4476, d769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5836 (p : Pattern) (guard : d4476 p = 1) : d770 p ≤ (0 : Int) + d4578 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d770, d4578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5762 p hg
    simpa only [d770, d4578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d770, d4578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5835 p hg
    simpa only [d770, d4578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5837 (p : Pattern) (guard : d4476 p = 1) : d771 p ≤ (0 : Int) + d4579 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d771, d4579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5833 p hg
    simpa only [d4476, d771, d4579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d771, d4579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5778 p hg
    simpa only [d4476, d771, d4579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5838 (p : Pattern) (guard : d4476 p = 1) : d772 p ≤ (0 : Int) + d4580 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d772, d4580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5777 p hg
    simpa only [d772, d4580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d772, d4580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5837 p hg
    simpa only [d772, d4580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5839 (p : Pattern) (guard : d4476 p = 1) : d773 p ≤ (0 : Int) + d4581 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d773, d4581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5836 p hg
    simpa only [d773, d4581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d773, d4581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5838 p hg
    simpa only [d773, d4581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5840 (p : Pattern) (guard : d4476 p = 1) : d774 p ≤ (0 : Int) + d4580 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d774, d4580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5783 p hg
    simpa only [d774, d4580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d774, d4580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5837 p hg
    simpa only [d774, d4580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5841 (p : Pattern) (guard : d4476 p = 1) : d775 p ≤ (0 : Int) + d4582 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d775, d4582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5840 p hg
    simpa only [d775, d4582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d775, d4582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5788 p hg
    simpa only [d775, d4582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5842 (p : Pattern) (guard : d4476 p = 1) : d776 p ≤ (0 : Int) + d4583 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d776, d4583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5839 p hg
    simpa only [d776, d4583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d776, d4583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5841 p hg
    simpa only [d776, d4583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5843 (p : Pattern) (guard : d0 p = 1) : d405 p ≤ (0 : Int) + d4585 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5844 (p : Pattern) (guard : d4476 p = 1) : d753 p ≤ (0 : Int) + d4586 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d753, d4586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5760 p hg
    simpa only [d4476, d753, d4586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d753, d4586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5843 p hg
    simpa only [d4476, d753, d4586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5845 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d4589 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5846 (p : Pattern) (guard : d4476 p = 1) : d771 p ≤ (0 : Int) + d4590 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d771, d4590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5833 p hg
    simpa only [d4476, d771, d4590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d771, d4590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5845 p hg
    simpa only [d4476, d771, d4590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5847 (p : Pattern) (guard : d4476 p = 1) : d777 p ≤ (0 : Int) + d4591 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d777, d4591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5844 p hg
    simpa only [d777, d4591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d777, d4591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5846 p hg
    simpa only [d777, d4591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5848 (p : Pattern) (guard : d4475 p = 1) : d241 p ≤ (0 : Int) + d4592 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d241, d4592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5766 p hg
    simpa only [d241, d4592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d241, d4592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5691 p hg
    simpa only [d241, d4592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5849 (p : Pattern) (guard : d4475 p = 1) : d242 p ≤ (0 : Int) + d4593 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d242, d4593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5751 p hg
    simpa only [d242, d4593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d242, d4593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5848 p hg
    simpa only [d242, d4593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5850 (p : Pattern) (guard : d4475 p = 1) : d243 p ≤ (0 : Int) + d4594 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d243, d4594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5849 p hg
    simpa only [d243, d4594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d243, d4594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5771 p hg
    simpa only [d243, d4594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5851 (p : Pattern) (guard : d4476 p = 1) : d778 p ≤ (0 : Int) + d4595 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d778, d4595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5850 p hg
    simpa only [d4476, d778, d4595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d778, d4595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5778 p hg
    simpa only [d4476, d778, d4595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5852 (p : Pattern) (guard : d4475 p = 1) : d245 p ≤ (0 : Int) + d4584 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d245, d4584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5766 p hg
    simpa only [d245, d4584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d245, d4584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5830 p hg
    simpa only [d245, d4584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5853 (p : Pattern) (guard : d0 p = 1) : d120 p ≤ (0 : Int) + d120 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5854 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d120 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5855 (p : Pattern) (guard : d4474 p = 1) : d121 p ≤ (0 : Int) + d120 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3159 p hg
    simpa only [d4474, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5854 p hg
    simpa only [d4474, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5856 (p : Pattern) (guard : d4475 p = 1) : d148 p ≤ (0 : Int) + d120 p := by
  cases selected : p 182 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4475, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5853 p hg
    simpa only [d4475, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4474 p = 1 := by simpa only [d4475, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5855 p hg
    simpa only [d4475, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5857 (p : Pattern) (guard : d4475 p = 1) : d153 p ≤ (0 : Int) + d4529 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d153, d4529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5856 p hg
    simpa only [d153, d4529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d153, d4529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5670 p hg
    simpa only [d153, d4529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5858 (p : Pattern) (guard : d4475 p = 1) : d154 p ≤ (0 : Int) + d4530 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d154, d4530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5857 p hg
    simpa only [d154, d4530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d154, d4530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5670 p hg
    simpa only [d154, d4530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5859 (p : Pattern) (guard : d4475 p = 1) : d246 p ≤ (0 : Int) + d4585 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d246, d4585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5852 p hg
    simpa only [d246, d4585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d246, d4585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5858 p hg
    simpa only [d246, d4585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5860 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d4596 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5861 (p : Pattern) (guard : d4476 p = 1) : d779 p ≤ (0 : Int) + d4597 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d779, d4597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5859 p hg
    simpa only [d4476, d779, d4597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d779, d4597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5860 p hg
    simpa only [d4476, d779, d4597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5862 (p : Pattern) (guard : d4476 p = 1) : d780 p ≤ (0 : Int) + d4598 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d780, d4598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5851 p hg
    simpa only [d780, d4598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d780, d4598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5861 p hg
    simpa only [d780, d4598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5863 (p : Pattern) (guard : d4476 p = 1) : d781 p ≤ (0 : Int) + d4599 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d781, d4599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5847 p hg
    simpa only [d781, d4599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d781, d4599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5862 p hg
    simpa only [d781, d4599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5864 (p : Pattern) (guard : d4475 p = 1) : d252 p ≤ (0 : Int) + d4600 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d252, d4600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5766 p hg
    simpa only [d252, d4600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d252, d4600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5669 p hg
    simpa only [d252, d4600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5865 (p : Pattern) (guard : d4475 p = 1) : d253 p ≤ (0 : Int) + d4601 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d253, d4601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5751 p hg
    simpa only [d253, d4601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d253, d4601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5864 p hg
    simpa only [d253, d4601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5866 (p : Pattern) (guard : d4475 p = 1) : d254 p ≤ (0 : Int) + d4602 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d254, d4602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5755 p hg
    simpa only [d254, d4602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d254, d4602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5669 p hg
    simpa only [d254, d4602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5867 (p : Pattern) (guard : d4475 p = 1) : d255 p ≤ (0 : Int) + d4603 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d255, d4603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5866 p hg
    simpa only [d255, d4603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d255, d4603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5670 p hg
    simpa only [d255, d4603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5868 (p : Pattern) (guard : d4475 p = 1) : d256 p ≤ (0 : Int) + d4604 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d256, d4604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5865 p hg
    simpa only [d256, d4604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4475 p = 1 := by simpa only [d256, d4604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5867 p hg
    simpa only [d256, d4604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5869 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d4607 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5870 (p : Pattern) (guard : d4476 p = 1) : d782 p ≤ (0 : Int) + d4608 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4475 p = 1 := by simpa only [d4476, d782, d4608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5868 p hg
    simpa only [d4476, d782, d4608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4476, d782, d4608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5869 p hg
    simpa only [d4476, d782, d4608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5871 (p : Pattern) (guard : d4476 p = 1) : d783 p ≤ (0 : Int) + d4609 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d783, d4609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5870 p hg
    simpa only [d783, d4609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d783, d4609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5861 p hg
    simpa only [d783, d4609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5872 (p : Pattern) (guard : d4476 p = 1) : d784 p ≤ (0 : Int) + d4610 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d784, d4610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5871 p hg
    simpa only [d784, d4610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d784, d4610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5727 p hg
    simpa only [d784, d4610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5873 (p : Pattern) (guard : d4476 p = 1) : d785 p ≤ (0 : Int) + d4611 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d785, d4611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5863 p hg
    simpa only [d785, d4611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d785, d4611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5872 p hg
    simpa only [d785, d4611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5874 (p : Pattern) (guard : d4476 p = 1) : d786 p ≤ (0 : Int) + d4612 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d786, d4612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5842 p hg
    simpa only [d786, d4612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d786, d4612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5873 p hg
    simpa only [d786, d4612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5875 (p : Pattern) (guard : d4476 p = 1) : d787 p ≤ (0 : Int) + d4613 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d787, d4613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5730 p hg
    simpa only [d787, d4613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d787, d4613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5874 p hg
    simpa only [d787, d4613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5876 (p : Pattern) (guard : d4476 p = 1) : d788 p ≤ (0 : Int) + d4614 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d788, d4614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5829 p hg
    simpa only [d788, d4614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d788, d4614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5875 p hg
    simpa only [d788, d4614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5877 (p : Pattern) (guard : d4476 p = 1) : d789 p ≤ (0 : Int) + d4615 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4476 p = 1 := by simpa only [d789, d4615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5801 p hg
    simpa only [d789, d4615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4476 p = 1 := by simpa only [d789, d4615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5876 p hg
    simpa only [d789, d4615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5878 (p : Pattern) (guard : d0 p = 1) : d376 p ≤ (0 : Int) + d792 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5879 (p : Pattern) (guard : d4301 p = 1) : d710 p ≤ (0 : Int) + d793 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4299 p = 1 := by simpa only [d4301, d710, d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3201 p hg
    simpa only [d4301, d710, d793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4301, d710, d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5878 p hg
    simpa only [d4301, d710, d793, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
