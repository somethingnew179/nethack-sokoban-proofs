/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons040
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare5740 (p : Pattern) (guard : d850 p = 1) : d11 p ≤ (2 : Int) + d11 p := by
  omega
theorem compare5741 (p : Pattern) (guard : d850 p = 1) : d125 p ≤ (2 : Int) + d11 p := by
  cases selected : p 187 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d850, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2724 p hg
    simpa only [d850, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d850, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare88 p hg
    simpa only [d850, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5742 (p : Pattern) (guard : d850 p = 1) : d126 p ≤ (2 : Int) + d11 p := by
  cases selected : p 186 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5740 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5741 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5743 (p : Pattern) (guard : d850 p = 1) : d127 p ≤ (2 : Int) + d12 p := by
  cases selected : p 168 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d127, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5734 p hg
    simpa only [d127, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d127, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5742 p hg
    simpa only [d127, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5744 (p : Pattern) (guard : d850 p = 1) : d65 p ≤ (2 : Int) + d65 p := by
  omega
theorem compare5745 (p : Pattern) (guard : d850 p = 1) : d128 p ≤ (2 : Int) + d109 p := by
  cases selected : p 160 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d128, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5743 p hg
    simpa only [d128, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d128, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5744 p hg
    simpa only [d128, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5746 (p : Pattern) (guard : d850 p = 1) : d129 p ≤ (2 : Int) + d109 p := by
  cases selected : p 159 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5739 p hg
    simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5745 p hg
    simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5747 (p : Pattern) (guard : d850 p = 1) : d237 p ≤ (2 : Int) + d109 p := by
  cases selected : p 158 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5739 p hg
    simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5746 p hg
    simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5748 (p : Pattern) (guard : d850 p = 1) : d238 p ≤ (2 : Int) + d227 p := by
  cases selected : p 141 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d238, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5738 p hg
    simpa only [d238, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d238, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5747 p hg
    simpa only [d238, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5749 (p : Pattern) (guard : d850 p = 1) : d239 p ≤ (2 : Int) + d228 p := by
  cases selected : p 134 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d239, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5730 p hg
    simpa only [d239, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d239, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5748 p hg
    simpa only [d239, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5750 (p : Pattern) (guard : d850 p = 1) : d70 p ≤ (2 : Int) + d70 p := by
  omega
theorem compare5751 (p : Pattern) (guard : d850 p = 1) : d181 p ≤ (2 : Int) + d229 p := by
  cases selected : p 158 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d181, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5737 p hg
    simpa only [d181, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d181, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5735 p hg
    simpa only [d181, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5752 (p : Pattern) (guard : d850 p = 1) : d240 p ≤ (2 : Int) + d230 p := by
  cases selected : p 158 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d240, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5746 p hg
    simpa only [d240, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d240, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5744 p hg
    simpa only [d240, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5753 (p : Pattern) (guard : d850 p = 1) : d241 p ≤ (2 : Int) + d231 p := by
  cases selected : p 141 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d241, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5751 p hg
    simpa only [d241, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d241, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5752 p hg
    simpa only [d241, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5754 (p : Pattern) (guard : d850 p = 1) : d242 p ≤ (2 : Int) + d232 p := by
  cases selected : p 134 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d242, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5750 p hg
    simpa only [d242, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d242, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5753 p hg
    simpa only [d242, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5755 (p : Pattern) (guard : d850 p = 1) : d243 p ≤ (2 : Int) + d233 p := by
  cases selected : p 133 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d243, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5749 p hg
    simpa only [d243, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d243, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5754 p hg
    simpa only [d243, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5756 (p : Pattern) (guard : d850 p = 1) : d66 p ≤ (2 : Int) + d66 p := by
  omega
theorem compare5757 (p : Pattern) (guard : d850 p = 1) : d244 p ≤ (2 : Int) + d234 p := by
  cases selected : p 133 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d244, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5754 p hg
    simpa only [d244, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d244, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5756 p hg
    simpa only [d244, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5758 (p : Pattern) (guard : d850 p = 1) : d245 p ≤ (2 : Int) + d235 p := by
  cases selected : p 132 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d245, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5755 p hg
    simpa only [d245, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d245, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5757 p hg
    simpa only [d245, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5759 (p : Pattern) (guard : d850 p = 1) : d57 p ≤ (2 : Int) + d57 p := by
  omega
theorem compare5760 (p : Pattern) (guard : d850 p = 1) : d137 p ≤ (2 : Int) + d56 p := by
  cases selected : p 186 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d137, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5733 p hg
    simpa only [d137, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d137, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5735 p hg
    simpa only [d137, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5761 (p : Pattern) (guard : d850 p = 1) : d139 p ≤ (2 : Int) + d57 p := by
  cases selected : p 160 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d139, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5734 p hg
    simpa only [d139, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d139, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5760 p hg
    simpa only [d139, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5762 (p : Pattern) (guard : d850 p = 1) : d153 p ≤ (2 : Int) + d57 p := by
  cases selected : p 159 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5759 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5761 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5763 (p : Pattern) (guard : d850 p = 1) : d186 p ≤ (2 : Int) + d57 p := by
  cases selected : p 158 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5759 p hg
    simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5762 p hg
    simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5764 (p : Pattern) (guard : d850 p = 1) : d63 p ≤ (2 : Int) + d63 p := by
  omega
theorem compare5765 (p : Pattern) (guard : d850 p = 1) : d60 p ≤ (2 : Int) + d60 p := by
  omega
theorem compare5766 (p : Pattern) (guard : d850 p = 1) : d143 p ≤ (2 : Int) + d61 p := by
  cases selected : p 186 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d143, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5741 p hg
    simpa only [d143, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d143, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5765 p hg
    simpa only [d143, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5767 (p : Pattern) (guard : d850 p = 1) : d144 p ≤ (2 : Int) + d62 p := by
  cases selected : p 168 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d144, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5760 p hg
    simpa only [d144, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d144, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5766 p hg
    simpa only [d144, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5768 (p : Pattern) (guard : d850 p = 1) : d146 p ≤ (2 : Int) + d63 p := by
  cases selected : p 160 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d146, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5743 p hg
    simpa only [d146, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d146, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5767 p hg
    simpa only [d146, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5769 (p : Pattern) (guard : d850 p = 1) : d155 p ≤ (2 : Int) + d63 p := by
  cases selected : p 159 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5764 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5768 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5770 (p : Pattern) (guard : d850 p = 1) : d246 p ≤ (2 : Int) + d63 p := by
  cases selected : p 158 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5764 p hg
    simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5769 p hg
    simpa only [d246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5771 (p : Pattern) (guard : d850 p = 1) : d247 p ≤ (2 : Int) + d64 p := by
  cases selected : p 141 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d247, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5763 p hg
    simpa only [d247, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d247, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5770 p hg
    simpa only [d247, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5772 (p : Pattern) (guard : d850 p = 1) : d248 p ≤ (2 : Int) + d67 p := by
  cases selected : p 134 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d248, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5771 p hg
    simpa only [d248, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d248, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5756 p hg
    simpa only [d248, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5773 (p : Pattern) (guard : d850 p = 1) : d138 p ≤ (2 : Int) + d57 p := by
  cases selected : p 160 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d138, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5732 p hg
    simpa only [d138, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d138, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5760 p hg
    simpa only [d138, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5774 (p : Pattern) (guard : d850 p = 1) : d140 p ≤ (2 : Int) + d57 p := by
  cases selected : p 159 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5773 p hg
    simpa only [d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5761 p hg
    simpa only [d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5775 (p : Pattern) (guard : d850 p = 1) : d188 p ≤ (2 : Int) + d68 p := by
  cases selected : p 158 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d188, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5774 p hg
    simpa only [d188, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d188, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5735 p hg
    simpa only [d188, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5776 (p : Pattern) (guard : d850 p = 1) : d12 p ≤ (2 : Int) + d12 p := by
  omega
theorem compare5777 (p : Pattern) (guard : d850 p = 1) : d145 p ≤ (2 : Int) + d63 p := by
  cases selected : p 160 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d145, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5776 p hg
    simpa only [d145, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d145, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5767 p hg
    simpa only [d145, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5778 (p : Pattern) (guard : d850 p = 1) : d147 p ≤ (2 : Int) + d63 p := by
  cases selected : p 159 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5777 p hg
    simpa only [d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5768 p hg
    simpa only [d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5779 (p : Pattern) (guard : d850 p = 1) : d249 p ≤ (2 : Int) + d69 p := by
  cases selected : p 158 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d249, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5778 p hg
    simpa only [d249, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d249, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5744 p hg
    simpa only [d249, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5780 (p : Pattern) (guard : d850 p = 1) : d250 p ≤ (2 : Int) + d70 p := by
  cases selected : p 141 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d250, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5775 p hg
    simpa only [d250, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d250, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5779 p hg
    simpa only [d250, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5781 (p : Pattern) (guard : d850 p = 1) : d251 p ≤ (2 : Int) + d71 p := by
  cases selected : p 134 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d251, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5780 p hg
    simpa only [d251, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d251, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5756 p hg
    simpa only [d251, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5782 (p : Pattern) (guard : d850 p = 1) : d252 p ≤ (2 : Int) + d72 p := by
  cases selected : p 133 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d252, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5772 p hg
    simpa only [d252, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d252, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5781 p hg
    simpa only [d252, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5783 (p : Pattern) (guard : d850 p = 1) : d191 p ≤ (2 : Int) + d68 p := by
  cases selected : p 158 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d191, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5762 p hg
    simpa only [d191, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d191, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5735 p hg
    simpa only [d191, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5784 (p : Pattern) (guard : d850 p = 1) : d253 p ≤ (2 : Int) + d69 p := by
  cases selected : p 158 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d253, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5769 p hg
    simpa only [d253, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d253, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5744 p hg
    simpa only [d253, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5785 (p : Pattern) (guard : d850 p = 1) : d254 p ≤ (2 : Int) + d70 p := by
  cases selected : p 141 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d254, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5783 p hg
    simpa only [d254, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d254, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5784 p hg
    simpa only [d254, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5786 (p : Pattern) (guard : d850 p = 1) : d255 p ≤ (2 : Int) + d71 p := by
  cases selected : p 134 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d255, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5785 p hg
    simpa only [d255, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d255, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5756 p hg
    simpa only [d255, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5787 (p : Pattern) (guard : d850 p = 1) : d256 p ≤ (2 : Int) + d73 p := by
  cases selected : p 133 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d256, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5786 p hg
    simpa only [d256, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d256, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5756 p hg
    simpa only [d256, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5788 (p : Pattern) (guard : d850 p = 1) : d257 p ≤ (2 : Int) + d74 p := by
  cases selected : p 132 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d257, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5782 p hg
    simpa only [d257, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d257, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5787 p hg
    simpa only [d257, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5789 (p : Pattern) (guard : d850 p = 1) : d258 p ≤ (2 : Int) + d236 p := by
  cases selected : p 108 with
  | false =>
    have hg : d850 p = 1 := by simpa only [d258, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5758 p hg
    simpa only [d258, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d850 p = 1 := by simpa only [d258, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5788 p hg
    simpa only [d258, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5790 (p : Pattern) (guard : d1 p = 1) : d258 p ≤ (4 : Int) + d258 p := by
  omega
theorem compare5791 (p : Pattern) (guard : d1 p = 1) : d258 p ≤ (7 : Int) + d258 p := by
  omega
theorem compare5792 (p : Pattern) (guard : d1 p = 1) : d258 p ≤ (6 : Int) + d258 p := by
  omega
theorem compare5793 (p : Pattern) (guard : d1233 p = 1) : d57 p ≤ (1 : Int) + d57 p := by
  omega
theorem compare5794 (p : Pattern) (guard : d1233 p = 1) : d7 p ≤ (1 : Int) + d7 p := by
  omega
theorem compare5795 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (1 : Int) + d1 p := by
  change (0 : Int) ≤ (1 : Int) + 1
  decide
theorem compare5796 (p : Pattern) (guard : d0 p = 1) : d1 p ≤ (1 : Int) + d1 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5797 (p : Pattern) (guard : d1233 p = 1) : d8 p ≤ (1 : Int) + d1 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1233, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5795 p hg
    simpa only [d1233, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1233, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5796 p hg
    simpa only [d1233, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5798 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (1 : Int) + d3 p := by
  change (2 : Int) ≤ (1 : Int) + 3
  decide
theorem compare5799 (p : Pattern) (guard : d0 p = 1) : d3 p ≤ (1 : Int) + d3 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5800 (p : Pattern) (guard : d1233 p = 1) : d9 p ≤ (1 : Int) + d3 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1233, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5798 p hg
    simpa only [d1233, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1233, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5799 p hg
    simpa only [d1233, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5801 (p : Pattern) (guard : d1233 p = 1) : d10 p ≤ (1 : Int) + d1234 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d10, d1234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5797 p hg
    simpa only [d10, d1234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d10, d1234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5800 p hg
    simpa only [d10, d1234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5802 (p : Pattern) (guard : d1233 p = 1) : d11 p ≤ (1 : Int) + d1235 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d11, d1235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5797 p hg
    simpa only [d11, d1235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d11, d1235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5801 p hg
    simpa only [d11, d1235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5803 (p : Pattern) (guard : d1233 p = 1) : d12 p ≤ (1 : Int) + d1236 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d12, d1236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5794 p hg
    simpa only [d12, d1236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d12, d1236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5802 p hg
    simpa only [d12, d1236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5804 (p : Pattern) (guard : d1233 p = 1) : d56 p ≤ (1 : Int) + d56 p := by
  omega
theorem compare5805 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (1 : Int) + d5 p := by
  change (4 : Int) ≤ (1 : Int) + 5
  decide
theorem compare5806 (p : Pattern) (guard : d0 p = 1) : d5 p ≤ (1 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5807 (p : Pattern) (guard : d1233 p = 1) : d58 p ≤ (1 : Int) + d5 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1233, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5805 p hg
    simpa only [d1233, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1233, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5806 p hg
    simpa only [d1233, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5808 (p : Pattern) (guard : d1233 p = 1) : d59 p ≤ (1 : Int) + d1237 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d59, d1237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5800 p hg
    simpa only [d59, d1237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d59, d1237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5807 p hg
    simpa only [d59, d1237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5809 (p : Pattern) (guard : d1233 p = 1) : d60 p ≤ (1 : Int) + d1238 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d60, d1238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5800 p hg
    simpa only [d60, d1238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d60, d1238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5808 p hg
    simpa only [d60, d1238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5810 (p : Pattern) (guard : d1233 p = 1) : d61 p ≤ (1 : Int) + d1239 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d61, d1239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5802 p hg
    simpa only [d61, d1239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d61, d1239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5809 p hg
    simpa only [d61, d1239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5811 (p : Pattern) (guard : d1233 p = 1) : d62 p ≤ (1 : Int) + d1240 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d62, d1240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5804 p hg
    simpa only [d62, d1240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d62, d1240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5810 p hg
    simpa only [d62, d1240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5812 (p : Pattern) (guard : d1233 p = 1) : d63 p ≤ (1 : Int) + d1241 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d63, d1241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5803 p hg
    simpa only [d63, d1241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d63, d1241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5811 p hg
    simpa only [d63, d1241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5813 (p : Pattern) (guard : d1233 p = 1) : d64 p ≤ (1 : Int) + d1242 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d64, d1242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5793 p hg
    simpa only [d64, d1242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d64, d1242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5812 p hg
    simpa only [d64, d1242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5814 (p : Pattern) (guard : d1233 p = 1) : d179 p ≤ (1 : Int) + d179 p := by
  omega
theorem compare5815 (p : Pattern) (guard : d1233 p = 1) : d55 p ≤ (1 : Int) + d55 p := by
  omega
theorem compare5816 (p : Pattern) (guard : d1233 p = 1) : d65 p ≤ (1 : Int) + d1243 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d65, d1243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5815 p hg
    simpa only [d65, d1243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d65, d1243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5809 p hg
    simpa only [d65, d1243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5817 (p : Pattern) (guard : d1233 p = 1) : d109 p ≤ (1 : Int) + d1244 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d109, d1244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5803 p hg
    simpa only [d109, d1244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d109, d1244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5816 p hg
    simpa only [d109, d1244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5818 (p : Pattern) (guard : d1233 p = 1) : d120 p ≤ (1 : Int) + d120 p := by
  omega
theorem compare5819 (p : Pattern) (guard : d1233 p = 1) : d125 p ≤ (1 : Int) + d1245 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d125, d1245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5802 p hg
    simpa only [d125, d1245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d125, d1245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5809 p hg
    simpa only [d125, d1245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5820 (p : Pattern) (guard : d1233 p = 1) : d126 p ≤ (1 : Int) + d1246 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d126, d1246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5802 p hg
    simpa only [d126, d1246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d126, d1246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5819 p hg
    simpa only [d126, d1246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5821 (p : Pattern) (guard : d1233 p = 1) : d127 p ≤ (1 : Int) + d1247 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d127, d1247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5818 p hg
    simpa only [d127, d1247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d127, d1247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5820 p hg
    simpa only [d127, d1247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5822 (p : Pattern) (guard : d1233 p = 1) : d128 p ≤ (1 : Int) + d1248 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d128, d1248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5821 p hg
    simpa only [d128, d1248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d128, d1248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5816 p hg
    simpa only [d128, d1248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5823 (p : Pattern) (guard : d1233 p = 1) : d129 p ≤ (1 : Int) + d1249 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d129, d1249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5817 p hg
    simpa only [d129, d1249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d129, d1249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5822 p hg
    simpa only [d129, d1249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5824 (p : Pattern) (guard : d1233 p = 1) : d237 p ≤ (1 : Int) + d1250 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d237, d1250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5817 p hg
    simpa only [d237, d1250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d237, d1250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5823 p hg
    simpa only [d237, d1250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5825 (p : Pattern) (guard : d1233 p = 1) : d238 p ≤ (1 : Int) + d1251 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d238, d1251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5814 p hg
    simpa only [d238, d1251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d238, d1251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5824 p hg
    simpa only [d238, d1251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5826 (p : Pattern) (guard : d1233 p = 1) : d239 p ≤ (1 : Int) + d1252 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d239, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5813 p hg
    simpa only [d239, d1252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d239, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5825 p hg
    simpa only [d239, d1252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5827 (p : Pattern) (guard : d1233 p = 1) : d68 p ≤ (1 : Int) + d68 p := by
  omega
theorem compare5828 (p : Pattern) (guard : d1233 p = 1) : d69 p ≤ (1 : Int) + d1253 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d69, d1253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5812 p hg
    simpa only [d69, d1253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d69, d1253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5816 p hg
    simpa only [d69, d1253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5829 (p : Pattern) (guard : d1233 p = 1) : d70 p ≤ (1 : Int) + d1254 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d70, d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5827 p hg
    simpa only [d70, d1254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d70, d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5828 p hg
    simpa only [d70, d1254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5830 (p : Pattern) (guard : d1233 p = 1) : d181 p ≤ (1 : Int) + d181 p := by
  omega
theorem compare5831 (p : Pattern) (guard : d1233 p = 1) : d240 p ≤ (1 : Int) + d1255 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d240, d1255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5823 p hg
    simpa only [d240, d1255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d240, d1255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5816 p hg
    simpa only [d240, d1255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5832 (p : Pattern) (guard : d1233 p = 1) : d241 p ≤ (1 : Int) + d1256 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d241, d1256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5830 p hg
    simpa only [d241, d1256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d241, d1256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5831 p hg
    simpa only [d241, d1256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5833 (p : Pattern) (guard : d1233 p = 1) : d242 p ≤ (1 : Int) + d1257 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d242, d1257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5829 p hg
    simpa only [d242, d1257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d242, d1257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5832 p hg
    simpa only [d242, d1257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5834 (p : Pattern) (guard : d1233 p = 1) : d243 p ≤ (1 : Int) + d1258 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d243, d1258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5826 p hg
    simpa only [d243, d1258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d243, d1258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5833 p hg
    simpa only [d243, d1258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5835 (p : Pattern) (guard : d1233 p = 1) : d66 p ≤ (1 : Int) + d1259 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d66, d1259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5815 p hg
    simpa only [d66, d1259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d66, d1259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5816 p hg
    simpa only [d66, d1259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5836 (p : Pattern) (guard : d1233 p = 1) : d244 p ≤ (1 : Int) + d1260 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d244, d1260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5833 p hg
    simpa only [d244, d1260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d244, d1260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5835 p hg
    simpa only [d244, d1260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5837 (p : Pattern) (guard : d1233 p = 1) : d245 p ≤ (1 : Int) + d1261 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d245, d1261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5834 p hg
    simpa only [d245, d1261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d245, d1261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5836 p hg
    simpa only [d245, d1261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5838 (p : Pattern) (guard : d1233 p = 1) : d186 p ≤ (1 : Int) + d186 p := by
  omega
theorem compare5839 (p : Pattern) (guard : d1233 p = 1) : d137 p ≤ (1 : Int) + d137 p := by
  omega
theorem compare5840 (p : Pattern) (guard : d1233 p = 1) : d143 p ≤ (1 : Int) + d1262 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d143, d1262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5819 p hg
    simpa only [d143, d1262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d143, d1262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5809 p hg
    simpa only [d143, d1262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5841 (p : Pattern) (guard : d1233 p = 1) : d144 p ≤ (1 : Int) + d1263 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d144, d1263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5839 p hg
    simpa only [d144, d1263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d144, d1263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5840 p hg
    simpa only [d144, d1263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5842 (p : Pattern) (guard : d1233 p = 1) : d146 p ≤ (1 : Int) + d1264 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d146, d1264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5821 p hg
    simpa only [d146, d1264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d146, d1264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5841 p hg
    simpa only [d146, d1264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5843 (p : Pattern) (guard : d1233 p = 1) : d155 p ≤ (1 : Int) + d1265 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d155, d1265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5812 p hg
    simpa only [d155, d1265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d155, d1265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5842 p hg
    simpa only [d155, d1265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5844 (p : Pattern) (guard : d1233 p = 1) : d246 p ≤ (1 : Int) + d1266 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d246, d1266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5812 p hg
    simpa only [d246, d1266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d246, d1266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5843 p hg
    simpa only [d246, d1266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5845 (p : Pattern) (guard : d1233 p = 1) : d247 p ≤ (1 : Int) + d1267 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d247, d1267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5838 p hg
    simpa only [d247, d1267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d247, d1267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5844 p hg
    simpa only [d247, d1267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5846 (p : Pattern) (guard : d1233 p = 1) : d248 p ≤ (1 : Int) + d1268 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d248, d1268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5845 p hg
    simpa only [d248, d1268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d248, d1268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5835 p hg
    simpa only [d248, d1268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5847 (p : Pattern) (guard : d1233 p = 1) : d188 p ≤ (1 : Int) + d188 p := by
  omega
theorem compare5848 (p : Pattern) (guard : d1233 p = 1) : d145 p ≤ (1 : Int) + d1269 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d145, d1269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5803 p hg
    simpa only [d145, d1269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d145, d1269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5841 p hg
    simpa only [d145, d1269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5849 (p : Pattern) (guard : d1233 p = 1) : d147 p ≤ (1 : Int) + d1270 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d147, d1270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5848 p hg
    simpa only [d147, d1270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d147, d1270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5842 p hg
    simpa only [d147, d1270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5850 (p : Pattern) (guard : d1233 p = 1) : d249 p ≤ (1 : Int) + d1271 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d249, d1271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5849 p hg
    simpa only [d249, d1271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d249, d1271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5816 p hg
    simpa only [d249, d1271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5851 (p : Pattern) (guard : d1233 p = 1) : d250 p ≤ (1 : Int) + d1272 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d250, d1272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5847 p hg
    simpa only [d250, d1272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d250, d1272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5850 p hg
    simpa only [d250, d1272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5852 (p : Pattern) (guard : d1233 p = 1) : d251 p ≤ (1 : Int) + d1273 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d251, d1273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5851 p hg
    simpa only [d251, d1273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d251, d1273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5835 p hg
    simpa only [d251, d1273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5853 (p : Pattern) (guard : d1233 p = 1) : d252 p ≤ (1 : Int) + d1274 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d252, d1274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5846 p hg
    simpa only [d252, d1274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d252, d1274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5852 p hg
    simpa only [d252, d1274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5854 (p : Pattern) (guard : d1233 p = 1) : d191 p ≤ (1 : Int) + d191 p := by
  omega
theorem compare5855 (p : Pattern) (guard : d1233 p = 1) : d253 p ≤ (1 : Int) + d1275 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d253, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5843 p hg
    simpa only [d253, d1275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d253, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5816 p hg
    simpa only [d253, d1275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5856 (p : Pattern) (guard : d1233 p = 1) : d254 p ≤ (1 : Int) + d1276 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d254, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5854 p hg
    simpa only [d254, d1276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d254, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5855 p hg
    simpa only [d254, d1276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5857 (p : Pattern) (guard : d1233 p = 1) : d255 p ≤ (1 : Int) + d1277 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d255, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5856 p hg
    simpa only [d255, d1277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d255, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5835 p hg
    simpa only [d255, d1277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5858 (p : Pattern) (guard : d1233 p = 1) : d256 p ≤ (1 : Int) + d1278 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d256, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5857 p hg
    simpa only [d256, d1278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d256, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5835 p hg
    simpa only [d256, d1278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5859 (p : Pattern) (guard : d1233 p = 1) : d257 p ≤ (1 : Int) + d1279 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d257, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5853 p hg
    simpa only [d257, d1279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d257, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5858 p hg
    simpa only [d257, d1279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5860 (p : Pattern) (guard : d1233 p = 1) : d258 p ≤ (1 : Int) + d1280 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1233 p = 1 := by simpa only [d258, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5837 p hg
    simpa only [d258, d1280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1233 p = 1 := by simpa only [d258, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5859 p hg
    simpa only [d258, d1280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5861 (p : Pattern) (guard : d770 p = 1) : d57 p ≤ (1 : Int) + d57 p := by
  omega
theorem compare5862 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (1 : Int) + d8 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1005 p hg
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5795 p hg
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5863 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (1 : Int) + d9 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1008 p hg
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5798 p hg
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5864 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (1 : Int) + d10 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d6, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5862 p hg
    simpa only [d6, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d6, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5863 p hg
    simpa only [d6, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5865 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (1 : Int) + d11 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5862 p hg
    simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5864 p hg
    simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5866 (p : Pattern) (guard : d0 p = 1) : d11 p ≤ (1 : Int) + d11 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5867 (p : Pattern) (guard : d770 p = 1) : d12 p ≤ (1 : Int) + d11 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5865 p hg
    simpa only [d770, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5866 p hg
    simpa only [d770, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5868 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (1 : Int) + d58 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1015 p hg
    simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5805 p hg
    simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5869 (p : Pattern) (guard : d1 p = 1) : d54 p ≤ (1 : Int) + d59 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d54, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5863 p hg
    simpa only [d54, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d54, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5868 p hg
    simpa only [d54, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5870 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (1 : Int) + d60 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d55, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5863 p hg
    simpa only [d55, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d55, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5869 p hg
    simpa only [d55, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5871 (p : Pattern) (guard : d1 p = 1) : d56 p ≤ (1 : Int) + d61 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d56, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5865 p hg
    simpa only [d56, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d56, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5870 p hg
    simpa only [d56, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5872 (p : Pattern) (guard : d0 p = 1) : d61 p ≤ (1 : Int) + d61 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5873 (p : Pattern) (guard : d770 p = 1) : d62 p ≤ (1 : Int) + d61 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5871 p hg
    simpa only [d770, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5872 p hg
    simpa only [d770, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5874 (p : Pattern) (guard : d770 p = 1) : d63 p ≤ (1 : Int) + d1098 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d63, d1098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5867 p hg
    simpa only [d63, d1098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d63, d1098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5873 p hg
    simpa only [d63, d1098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5875 (p : Pattern) (guard : d770 p = 1) : d64 p ≤ (1 : Int) + d1099 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d64, d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5861 p hg
    simpa only [d64, d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d64, d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5874 p hg
    simpa only [d64, d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5876 (p : Pattern) (guard : d770 p = 1) : d179 p ≤ (1 : Int) + d179 p := by
  omega
theorem compare5877 (p : Pattern) (guard : d0 p = 1) : d60 p ≤ (1 : Int) + d60 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5878 (p : Pattern) (guard : d770 p = 1) : d65 p ≤ (1 : Int) + d60 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5870 p hg
    simpa only [d770, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5877 p hg
    simpa only [d770, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5879 (p : Pattern) (guard : d770 p = 1) : d109 p ≤ (1 : Int) + d1100 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d109, d1100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5867 p hg
    simpa only [d109, d1100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d109, d1100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5878 p hg
    simpa only [d109, d1100, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
