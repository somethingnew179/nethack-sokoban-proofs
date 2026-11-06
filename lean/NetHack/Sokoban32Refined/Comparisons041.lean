/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons040
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare5740 (p : Pattern) (guard : d1095 p = 1) : d488 p ≤ (0 : Int) + d231 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d488, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5738 p hg
    simpa only [d1095, d488, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d488, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5739 p hg
    simpa only [d1095, d488, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5741 (p : Pattern) (guard : d1088 p = 1) : d461 p ≤ (0 : Int) + d46 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d461, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5719 p hg
    simpa only [d461, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d461, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5698 p hg
    simpa only [d461, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5742 (p : Pattern) (guard : d1088 p = 1) : d489 p ≤ (0 : Int) + d79 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d489, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5741 p hg
    simpa only [d489, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d489, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1677 p hg
    simpa only [d489, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5743 (p : Pattern) (guard : d1088 p = 1) : d490 p ≤ (0 : Int) + d80 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d490, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5722 p hg
    simpa only [d490, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d490, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5742 p hg
    simpa only [d490, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5744 (p : Pattern) (guard : d0 p = 1) : d492 p ≤ (0 : Int) + d154 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5745 (p : Pattern) (guard : d1095 p = 1) : d493 p ≤ (0 : Int) + d232 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d493, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5743 p hg
    simpa only [d1095, d493, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d493, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5744 p hg
    simpa only [d1095, d493, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5746 (p : Pattern) (guard : d1095 p = 1) : d494 p ≤ (0 : Int) + d233 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d494, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5740 p hg
    simpa only [d494, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d494, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5745 p hg
    simpa only [d494, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5747 (p : Pattern) (guard : d1095 p = 1) : d495 p ≤ (0 : Int) + d234 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d495, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5729 p hg
    simpa only [d495, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d495, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5746 p hg
    simpa only [d495, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5748 (p : Pattern) (guard : d0 p = 1) : d498 p ≤ (0 : Int) + d150 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5749 (p : Pattern) (guard : d1095 p = 1) : d499 p ≤ (0 : Int) + d235 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d499, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5714 p hg
    simpa only [d1095, d499, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d499, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5748 p hg
    simpa only [d1095, d499, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5750 (p : Pattern) (guard : d1088 p = 1) : d500 p ≤ (0 : Int) + d14 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1816 p hg
    simpa only [d1088, d500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5717 p hg
    simpa only [d1088, d500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5751 (p : Pattern) (guard : d1088 p = 1) : d501 p ≤ (0 : Int) + d98 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d501, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5750 p hg
    simpa only [d501, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d501, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1818 p hg
    simpa only [d501, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5752 (p : Pattern) (guard : d1088 p = 1) : d97 p ≤ (0 : Int) + d14 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1816 p hg
    simpa only [d1088, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5685 p hg
    simpa only [d1088, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5753 (p : Pattern) (guard : d1088 p = 1) : d97 p ≤ (0 : Int) + d98 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5752 p hg
    simpa only [d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1818 p hg
    simpa only [d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5754 (p : Pattern) (guard : d1088 p = 1) : d502 p ≤ (0 : Int) + d98 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5751 p hg
    simpa only [d502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5753 p hg
    simpa only [d502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5755 (p : Pattern) (guard : d1088 p = 1) : d109 p ≤ (0 : Int) + d99 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d109, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5753 p hg
    simpa only [d109, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d109, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5735 p hg
    simpa only [d109, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5756 (p : Pattern) (guard : d1088 p = 1) : d503 p ≤ (0 : Int) + d100 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d503, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5754 p hg
    simpa only [d503, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d503, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5755 p hg
    simpa only [d503, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5757 (p : Pattern) (guard : d1088 p = 1) : d504 p ≤ (0 : Int) + d99 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d504, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5751 p hg
    simpa only [d504, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d504, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5735 p hg
    simpa only [d504, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5758 (p : Pattern) (guard : d1088 p = 1) : d68 p ≤ (0 : Int) + d40 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1450 p hg
    simpa only [d1088, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5709 p hg
    simpa only [d1088, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5759 (p : Pattern) (guard : d1088 p = 1) : d68 p ≤ (0 : Int) + d69 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5758 p hg
    simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1633 p hg
    simpa only [d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5760 (p : Pattern) (guard : d1088 p = 1) : d75 p ≤ (0 : Int) + d72 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d75, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5759 p hg
    simpa only [d75, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d75, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5735 p hg
    simpa only [d75, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5761 (p : Pattern) (guard : d1088 p = 1) : d505 p ≤ (0 : Int) + d101 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d505, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5757 p hg
    simpa only [d505, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d505, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5760 p hg
    simpa only [d505, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5762 (p : Pattern) (guard : d1088 p = 1) : d506 p ≤ (0 : Int) + d102 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d506, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5756 p hg
    simpa only [d506, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d506, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5761 p hg
    simpa only [d506, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5763 (p : Pattern) (guard : d0 p = 1) : d507 p ≤ (0 : Int) + d154 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5764 (p : Pattern) (guard : d1095 p = 1) : d508 p ≤ (0 : Int) + d236 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d508, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5762 p hg
    simpa only [d1095, d508, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d508, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5763 p hg
    simpa only [d1095, d508, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5765 (p : Pattern) (guard : d1095 p = 1) : d509 p ≤ (0 : Int) + d237 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d509, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5749 p hg
    simpa only [d509, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d509, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5764 p hg
    simpa only [d509, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5766 (p : Pattern) (guard : d0 p = 1) : d142 p ≤ (0 : Int) + d8 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5767 (p : Pattern) (guard : d1088 p = 1) : d483 p ≤ (0 : Int) + d8 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare199 p hg
    simpa only [d1088, d483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5766 p hg
    simpa only [d1088, d483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5768 (p : Pattern) (guard : d1088 p = 1) : d484 p ≤ (0 : Int) + d16 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d484, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5767 p hg
    simpa only [d484, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d484, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5686 p hg
    simpa only [d484, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5769 (p : Pattern) (guard : d1088 p = 1) : d485 p ≤ (0 : Int) + d27 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d485, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5768 p hg
    simpa only [d485, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d485, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5699 p hg
    simpa only [d485, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5770 (p : Pattern) (guard : d1088 p = 1) : d486 p ≤ (0 : Int) + d76 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d486, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5769 p hg
    simpa only [d486, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d486, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1677 p hg
    simpa only [d486, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5771 (p : Pattern) (guard : d1088 p = 1) : d487 p ≤ (0 : Int) + d77 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d487, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5701 p hg
    simpa only [d487, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d487, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5770 p hg
    simpa only [d487, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5772 (p : Pattern) (guard : d0 p = 1) : d512 p ≤ (0 : Int) + d161 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5773 (p : Pattern) (guard : d1095 p = 1) : d513 p ≤ (0 : Int) + d238 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d513, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5771 p hg
    simpa only [d1095, d513, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d513, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5772 p hg
    simpa only [d1095, d513, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5774 (p : Pattern) (guard : d1088 p = 1) : d111 p ≤ (0 : Int) + d107 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d111, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5755 p hg
    simpa only [d111, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d111, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1836 p hg
    simpa only [d111, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5775 (p : Pattern) (guard : d1088 p = 1) : d514 p ≤ (0 : Int) + d108 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d514, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5756 p hg
    simpa only [d514, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d514, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5774 p hg
    simpa only [d514, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5776 (p : Pattern) (guard : d1095 p = 1) : d515 p ≤ (0 : Int) + d239 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d515, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5775 p hg
    simpa only [d1095, d515, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d515, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare512 p hg
    simpa only [d1095, d515, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5777 (p : Pattern) (guard : d1095 p = 1) : d516 p ≤ (0 : Int) + d240 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d516, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5773 p hg
    simpa only [d516, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d516, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5776 p hg
    simpa only [d516, d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5778 (p : Pattern) (guard : d1095 p = 1) : d517 p ≤ (0 : Int) + d241 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d517, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5765 p hg
    simpa only [d517, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d517, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5777 p hg
    simpa only [d517, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5779 (p : Pattern) (guard : d1095 p = 1) : d518 p ≤ (0 : Int) + d242 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d518, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5747 p hg
    simpa only [d518, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d518, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5778 p hg
    simpa only [d518, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5780 (p : Pattern) (guard : d0 p = 1) : d521 p ≤ (0 : Int) + d154 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5781 (p : Pattern) (guard : d1095 p = 1) : d522 p ≤ (0 : Int) + d243 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d522, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5726 p hg
    simpa only [d1095, d522, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d522, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5780 p hg
    simpa only [d1095, d522, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5782 (p : Pattern) (guard : d1095 p = 1) : d523 p ≤ (0 : Int) + d244 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d523, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5749 p hg
    simpa only [d523, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d523, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5781 p hg
    simpa only [d523, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5783 (p : Pattern) (guard : d1088 p = 1) : d491 p ≤ (0 : Int) + d79 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d491, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5721 p hg
    simpa only [d491, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d491, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1677 p hg
    simpa only [d491, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5784 (p : Pattern) (guard : d1088 p = 1) : d492 p ≤ (0 : Int) + d80 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d492, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5722 p hg
    simpa only [d492, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d492, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5783 p hg
    simpa only [d492, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5785 (p : Pattern) (guard : d0 p = 1) : d525 p ≤ (0 : Int) + d163 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5786 (p : Pattern) (guard : d1095 p = 1) : d526 p ≤ (0 : Int) + d245 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d526, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5784 p hg
    simpa only [d1095, d526, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d526, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5785 p hg
    simpa only [d1095, d526, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5787 (p : Pattern) (guard : d1095 p = 1) : d527 p ≤ (0 : Int) + d246 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d527, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5773 p hg
    simpa only [d527, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d527, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5786 p hg
    simpa only [d527, d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5788 (p : Pattern) (guard : d1095 p = 1) : d528 p ≤ (0 : Int) + d247 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d528, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5782 p hg
    simpa only [d528, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d528, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5787 p hg
    simpa only [d528, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5789 (p : Pattern) (guard : d1088 p = 1) : d496 p ≤ (0 : Int) + d36 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d496, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5768 p hg
    simpa only [d496, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d496, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5705 p hg
    simpa only [d496, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5790 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d38 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5791 (p : Pattern) (guard : d1088 p = 1) : d61 p ≤ (0 : Int) + d38 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare232 p hg
    simpa only [d1088, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5790 p hg
    simpa only [d1088, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5792 (p : Pattern) (guard : d1088 p = 1) : d61 p ≤ (0 : Int) + d42 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5791 p hg
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5710 p hg
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5793 (p : Pattern) (guard : d1088 p = 1) : d473 p ≤ (0 : Int) + d43 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d473, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5792 p hg
    simpa only [d473, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d473, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5699 p hg
    simpa only [d473, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5794 (p : Pattern) (guard : d1088 p = 1) : d497 p ≤ (0 : Int) + d44 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d497, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5789 p hg
    simpa only [d497, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d497, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5793 p hg
    simpa only [d497, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5795 (p : Pattern) (guard : d1088 p = 1) : d498 p ≤ (0 : Int) + d45 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d498, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5701 p hg
    simpa only [d498, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d498, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5794 p hg
    simpa only [d498, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5796 (p : Pattern) (guard : d0 p = 1) : d529 p ≤ (0 : Int) + d161 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5797 (p : Pattern) (guard : d1095 p = 1) : d530 p ≤ (0 : Int) + d248 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d530, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5795 p hg
    simpa only [d1095, d530, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d530, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5796 p hg
    simpa only [d1095, d530, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5798 (p : Pattern) (guard : d1088 p = 1) : d125 p ≤ (0 : Int) + d101 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d125, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5755 p hg
    simpa only [d125, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d125, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5760 p hg
    simpa only [d125, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5799 (p : Pattern) (guard : d1088 p = 1) : d507 p ≤ (0 : Int) + d102 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d507, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5756 p hg
    simpa only [d507, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d507, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5798 p hg
    simpa only [d507, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5800 (p : Pattern) (guard : d1095 p = 1) : d531 p ≤ (0 : Int) + d249 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d531, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5799 p hg
    simpa only [d1095, d531, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d531, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare526 p hg
    simpa only [d1095, d531, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5801 (p : Pattern) (guard : d1095 p = 1) : d532 p ≤ (0 : Int) + d250 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d532, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5797 p hg
    simpa only [d532, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d532, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5800 p hg
    simpa only [d532, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5802 (p : Pattern) (guard : d1088 p = 1) : d510 p ≤ (0 : Int) + d16 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5768 p hg
    simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5690 p hg
    simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5803 (p : Pattern) (guard : d1088 p = 1) : d470 p ≤ (0 : Int) + d27 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d470, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5690 p hg
    simpa only [d470, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d470, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5699 p hg
    simpa only [d470, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5804 (p : Pattern) (guard : d1088 p = 1) : d511 p ≤ (0 : Int) + d28 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d511, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5802 p hg
    simpa only [d511, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d511, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5803 p hg
    simpa only [d511, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5805 (p : Pattern) (guard : d1088 p = 1) : d491 p ≤ (0 : Int) + d76 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d491, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5803 p hg
    simpa only [d491, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d491, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1677 p hg
    simpa only [d491, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5806 (p : Pattern) (guard : d1088 p = 1) : d512 p ≤ (0 : Int) + d77 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d512, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5804 p hg
    simpa only [d512, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d512, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5805 p hg
    simpa only [d512, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5807 (p : Pattern) (guard : d0 p = 1) : d525 p ≤ (0 : Int) + d167 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5808 (p : Pattern) (guard : d1095 p = 1) : d533 p ≤ (0 : Int) + d251 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d533, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5806 p hg
    simpa only [d1095, d533, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d533, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5807 p hg
    simpa only [d1095, d533, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5809 (p : Pattern) (guard : d1095 p = 1) : d534 p ≤ (0 : Int) + d252 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d534, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5808 p hg
    simpa only [d534, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d534, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1862 p hg
    simpa only [d534, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5810 (p : Pattern) (guard : d1095 p = 1) : d535 p ≤ (0 : Int) + d253 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d535, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5801 p hg
    simpa only [d535, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d535, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5809 p hg
    simpa only [d535, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5811 (p : Pattern) (guard : d1095 p = 1) : d536 p ≤ (0 : Int) + d254 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d536, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5788 p hg
    simpa only [d536, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d536, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5810 p hg
    simpa only [d536, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5812 (p : Pattern) (guard : d1095 p = 1) : d537 p ≤ (0 : Int) + d255 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d537, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5779 p hg
    simpa only [d537, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d537, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5811 p hg
    simpa only [d537, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5813 (p : Pattern) (guard : d1088 p = 1) : d52 p ≤ (0 : Int) + d52 p := by
  omega
theorem compare5814 (p : Pattern) (guard : d1088 p = 1) : d460 p ≤ (0 : Int) + d53 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d460, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5718 p hg
    simpa only [d460, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d460, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5813 p hg
    simpa only [d460, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5815 (p : Pattern) (guard : d1088 p = 1) : d52 p ≤ (0 : Int) + d53 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5686 p hg
    simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5813 p hg
    simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5816 (p : Pattern) (guard : d1088 p = 1) : d469 p ≤ (0 : Int) + d53 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5814 p hg
    simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5815 p hg
    simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5817 (p : Pattern) (guard : d1088 p = 1) : d54 p ≤ (0 : Int) + d54 p := by
  omega
theorem compare5818 (p : Pattern) (guard : d1088 p = 1) : d54 p ≤ (0 : Int) + d55 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5698 p hg
    simpa only [d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5817 p hg
    simpa only [d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5819 (p : Pattern) (guard : d1088 p = 1) : d470 p ≤ (0 : Int) + d56 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d470, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5815 p hg
    simpa only [d470, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d470, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5818 p hg
    simpa only [d470, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5820 (p : Pattern) (guard : d1088 p = 1) : d471 p ≤ (0 : Int) + d57 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d471, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5816 p hg
    simpa only [d471, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d471, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5819 p hg
    simpa only [d471, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5821 (p : Pattern) (guard : d1088 p = 1) : d58 p ≤ (0 : Int) + d58 p := by
  omega
theorem compare5822 (p : Pattern) (guard : d1088 p = 1) : d58 p ≤ (0 : Int) + d59 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5704 p hg
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5821 p hg
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5823 (p : Pattern) (guard : d1088 p = 1) : d472 p ≤ (0 : Int) + d60 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d472, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5814 p hg
    simpa only [d472, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d472, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5822 p hg
    simpa only [d472, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5824 (p : Pattern) (guard : d1088 p = 1) : d61 p ≤ (0 : Int) + d61 p := by
  omega
theorem compare5825 (p : Pattern) (guard : d1088 p = 1) : d61 p ≤ (0 : Int) + d62 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5710 p hg
    simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5824 p hg
    simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5826 (p : Pattern) (guard : d1088 p = 1) : d473 p ≤ (0 : Int) + d63 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d473, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5825 p hg
    simpa only [d473, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d473, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5818 p hg
    simpa only [d473, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5827 (p : Pattern) (guard : d1088 p = 1) : d474 p ≤ (0 : Int) + d64 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d474, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5823 p hg
    simpa only [d474, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d474, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5826 p hg
    simpa only [d474, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5828 (p : Pattern) (guard : d1088 p = 1) : d475 p ≤ (0 : Int) + d65 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d475, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5820 p hg
    simpa only [d475, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d475, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5827 p hg
    simpa only [d475, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5829 (p : Pattern) (guard : d1088 p = 1) : d475 p ≤ (0 : Int) + d66 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5726 p hg
    simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5828 p hg
    simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5830 (p : Pattern) (guard : d1088 p = 1) : d476 p ≤ (0 : Int) + d67 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d476, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5714 p hg
    simpa only [d476, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d476, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5829 p hg
    simpa only [d476, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5831 (p : Pattern) (guard : d1088 p = 1) : d488 p ≤ (0 : Int) + d78 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d488, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5738 p hg
    simpa only [d488, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d488, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5771 p hg
    simpa only [d488, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5832 (p : Pattern) (guard : d1088 p = 1) : d491 p ≤ (0 : Int) + d81 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d491, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5819 p hg
    simpa only [d491, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d491, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1677 p hg
    simpa only [d491, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5833 (p : Pattern) (guard : d1088 p = 1) : d492 p ≤ (0 : Int) + d82 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d492, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5820 p hg
    simpa only [d492, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d492, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5832 p hg
    simpa only [d492, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5834 (p : Pattern) (guard : d1088 p = 1) : d493 p ≤ (0 : Int) + d83 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d493, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5743 p hg
    simpa only [d493, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d493, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5833 p hg
    simpa only [d493, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5835 (p : Pattern) (guard : d1088 p = 1) : d494 p ≤ (0 : Int) + d84 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d494, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5831 p hg
    simpa only [d494, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d494, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5834 p hg
    simpa only [d494, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5836 (p : Pattern) (guard : d1088 p = 1) : d495 p ≤ (0 : Int) + d85 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d495, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5830 p hg
    simpa only [d495, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d495, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5835 p hg
    simpa only [d495, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5837 (p : Pattern) (guard : d1088 p = 1) : d457 p ≤ (0 : Int) + d86 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d457, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5684 p hg
    simpa only [d457, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d457, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5813 p hg
    simpa only [d457, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5838 (p : Pattern) (guard : d1088 p = 1) : d52 p ≤ (0 : Int) + d86 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5689 p hg
    simpa only [d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5813 p hg
    simpa only [d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5839 (p : Pattern) (guard : d1088 p = 1) : d458 p ≤ (0 : Int) + d86 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5837 p hg
    simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5838 p hg
    simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5840 (p : Pattern) (guard : d1088 p = 1) : d460 p ≤ (0 : Int) + d86 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d460, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5693 p hg
    simpa only [d460, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d460, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5813 p hg
    simpa only [d460, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5841 (p : Pattern) (guard : d1088 p = 1) : d54 p ≤ (0 : Int) + d87 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5696 p hg
    simpa only [d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5817 p hg
    simpa only [d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5842 (p : Pattern) (guard : d1088 p = 1) : d461 p ≤ (0 : Int) + d88 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d461, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5840 p hg
    simpa only [d461, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d461, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5841 p hg
    simpa only [d461, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5843 (p : Pattern) (guard : d1088 p = 1) : d462 p ≤ (0 : Int) + d89 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d462, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5839 p hg
    simpa only [d462, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d462, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5842 p hg
    simpa only [d462, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5844 (p : Pattern) (guard : d1088 p = 1) : d484 p ≤ (0 : Int) + d86 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d484, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5767 p hg
    simpa only [d484, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d484, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5813 p hg
    simpa only [d484, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5845 (p : Pattern) (guard : d1088 p = 1) : d58 p ≤ (0 : Int) + d90 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5703 p hg
    simpa only [d90, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5821 p hg
    simpa only [d90, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5846 (p : Pattern) (guard : d1088 p = 1) : d496 p ≤ (0 : Int) + d91 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d496, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5844 p hg
    simpa only [d496, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d496, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5845 p hg
    simpa only [d496, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5847 (p : Pattern) (guard : d1088 p = 1) : d61 p ≤ (0 : Int) + d92 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5791 p hg
    simpa only [d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5824 p hg
    simpa only [d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5848 (p : Pattern) (guard : d1088 p = 1) : d473 p ≤ (0 : Int) + d93 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d473, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5847 p hg
    simpa only [d473, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d473, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5841 p hg
    simpa only [d473, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5849 (p : Pattern) (guard : d1088 p = 1) : d497 p ≤ (0 : Int) + d94 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d497, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5846 p hg
    simpa only [d497, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d497, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5848 p hg
    simpa only [d497, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5850 (p : Pattern) (guard : d1088 p = 1) : d498 p ≤ (0 : Int) + d95 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d498, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5843 p hg
    simpa only [d498, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d498, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5849 p hg
    simpa only [d498, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5851 (p : Pattern) (guard : d1088 p = 1) : d499 p ≤ (0 : Int) + d96 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d499, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5714 p hg
    simpa only [d499, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d499, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5850 p hg
    simpa only [d499, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5852 (p : Pattern) (guard : d1088 p = 1) : d508 p ≤ (0 : Int) + d102 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5762 p hg
    simpa only [d508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5799 p hg
    simpa only [d508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5853 (p : Pattern) (guard : d1088 p = 1) : d509 p ≤ (0 : Int) + d103 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d509, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5851 p hg
    simpa only [d509, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d509, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5852 p hg
    simpa only [d509, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5854 (p : Pattern) (guard : d1088 p = 1) : d510 p ≤ (0 : Int) + d86 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5844 p hg
    simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5838 p hg
    simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5855 (p : Pattern) (guard : d1088 p = 1) : d470 p ≤ (0 : Int) + d88 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d470, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5838 p hg
    simpa only [d470, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d470, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5841 p hg
    simpa only [d470, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5856 (p : Pattern) (guard : d1088 p = 1) : d511 p ≤ (0 : Int) + d89 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d511, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5854 p hg
    simpa only [d511, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d511, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5855 p hg
    simpa only [d511, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5857 (p : Pattern) (guard : d1088 p = 1) : d491 p ≤ (0 : Int) + d104 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d491, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5855 p hg
    simpa only [d491, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d491, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1677 p hg
    simpa only [d491, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5858 (p : Pattern) (guard : d1088 p = 1) : d512 p ≤ (0 : Int) + d105 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d512, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5856 p hg
    simpa only [d512, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d512, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5857 p hg
    simpa only [d512, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5859 (p : Pattern) (guard : d1088 p = 1) : d513 p ≤ (0 : Int) + d106 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d513, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5771 p hg
    simpa only [d513, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d513, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5858 p hg
    simpa only [d513, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5860 (p : Pattern) (guard : d1088 p = 1) : d112 p ≤ (0 : Int) + d112 p := by
  omega
theorem compare5861 (p : Pattern) (guard : d1088 p = 1) : d515 p ≤ (0 : Int) + d113 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d515, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5775 p hg
    simpa only [d515, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d515, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5860 p hg
    simpa only [d515, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5862 (p : Pattern) (guard : d1088 p = 1) : d516 p ≤ (0 : Int) + d114 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d516, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5859 p hg
    simpa only [d516, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d516, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5861 p hg
    simpa only [d516, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5863 (p : Pattern) (guard : d1088 p = 1) : d517 p ≤ (0 : Int) + d115 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d517, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5853 p hg
    simpa only [d517, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d517, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5862 p hg
    simpa only [d517, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5864 (p : Pattern) (guard : d1088 p = 1) : d518 p ≤ (0 : Int) + d116 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d518, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5836 p hg
    simpa only [d518, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d518, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5863 p hg
    simpa only [d518, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5865 (p : Pattern) (guard : d1088 p = 1) : d499 p ≤ (0 : Int) + d45 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5714 p hg
    simpa only [d499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5795 p hg
    simpa only [d499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5866 (p : Pattern) (guard : d1088 p = 1) : d519 p ≤ (0 : Int) + d60 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d519, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5815 p hg
    simpa only [d519, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d519, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5822 p hg
    simpa only [d519, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5867 (p : Pattern) (guard : d1088 p = 1) : d520 p ≤ (0 : Int) + d64 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d520, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5866 p hg
    simpa only [d520, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d520, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5826 p hg
    simpa only [d520, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5868 (p : Pattern) (guard : d1088 p = 1) : d521 p ≤ (0 : Int) + d65 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d521, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5820 p hg
    simpa only [d521, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d521, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5867 p hg
    simpa only [d521, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5869 (p : Pattern) (guard : d1088 p = 1) : d522 p ≤ (0 : Int) + d66 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d522, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5726 p hg
    simpa only [d522, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d522, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5868 p hg
    simpa only [d522, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5870 (p : Pattern) (guard : d1088 p = 1) : d523 p ≤ (0 : Int) + d67 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d523, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5865 p hg
    simpa only [d523, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d523, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5869 p hg
    simpa only [d523, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5871 (p : Pattern) (guard : d1088 p = 1) : d513 p ≤ (0 : Int) + d77 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5771 p hg
    simpa only [d513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5806 p hg
    simpa only [d513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5872 (p : Pattern) (guard : d1088 p = 1) : d524 p ≤ (0 : Int) + d57 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d524, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5815 p hg
    simpa only [d524, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d524, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5819 p hg
    simpa only [d524, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5873 (p : Pattern) (guard : d1088 p = 1) : d525 p ≤ (0 : Int) + d82 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d525, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5872 p hg
    simpa only [d525, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d525, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5832 p hg
    simpa only [d525, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5874 (p : Pattern) (guard : d1088 p = 1) : d526 p ≤ (0 : Int) + d83 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d526, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5784 p hg
    simpa only [d526, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d526, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5873 p hg
    simpa only [d526, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5875 (p : Pattern) (guard : d1088 p = 1) : d527 p ≤ (0 : Int) + d117 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d527, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5871 p hg
    simpa only [d527, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d527, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5874 p hg
    simpa only [d527, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5876 (p : Pattern) (guard : d1088 p = 1) : d528 p ≤ (0 : Int) + d118 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d528, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5870 p hg
    simpa only [d528, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d528, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5875 p hg
    simpa only [d528, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5877 (p : Pattern) (guard : d1088 p = 1) : d58 p ≤ (0 : Int) + d119 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1088, d58, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare221 p hg
    simpa only [d1088, d58, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1088, d58, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5695 p hg
    simpa only [d1088, d58, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5878 (p : Pattern) (guard : d1088 p = 1) : d58 p ≤ (0 : Int) + d120 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5877 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5821 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5879 (p : Pattern) (guard : d1088 p = 1) : d519 p ≤ (0 : Int) + d121 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d519, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5838 p hg
    simpa only [d519, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d519, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5878 p hg
    simpa only [d519, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
