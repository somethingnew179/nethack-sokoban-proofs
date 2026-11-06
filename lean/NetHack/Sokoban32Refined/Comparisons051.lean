/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons050
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare7140 (p : Pattern) (guard : d1174 p = 1) : d686 p ≤ (0 : Int) + d316 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d686, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7116 p hg
    simpa only [d686, d316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d686, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7139 p hg
    simpa only [d686, d316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7141 (p : Pattern) (guard : d0 p = 1) : d654 p ≤ (0 : Int) + d148 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7142 (p : Pattern) (guard : d1174 p = 1) : d654 p ≤ (0 : Int) + d298 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1174, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7091 p hg
    simpa only [d1174, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1174, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7141 p hg
    simpa only [d1174, d298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7143 (p : Pattern) (guard : d1174 p = 1) : d654 p ≤ (0 : Int) + d299 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7093 p hg
    simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7142 p hg
    simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7144 (p : Pattern) (guard : d1174 p = 1) : d654 p ≤ (0 : Int) + d300 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7093 p hg
    simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7143 p hg
    simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7145 (p : Pattern) (guard : d1174 p = 1) : d658 p ≤ (0 : Int) + d301 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d658, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7144 p hg
    simpa only [d658, d301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d658, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7100 p hg
    simpa only [d658, d301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7146 (p : Pattern) (guard : d1174 p = 1) : d663 p ≤ (0 : Int) + d317 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1174, d663, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7091 p hg
    simpa only [d1174, d663, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1174, d663, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7109 p hg
    simpa only [d1174, d663, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7147 (p : Pattern) (guard : d1174 p = 1) : d664 p ≤ (0 : Int) + d318 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d664, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7142 p hg
    simpa only [d664, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d664, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7146 p hg
    simpa only [d664, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7148 (p : Pattern) (guard : d1174 p = 1) : d664 p ≤ (0 : Int) + d319 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7107 p hg
    simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7147 p hg
    simpa only [d319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7149 (p : Pattern) (guard : d1174 p = 1) : d687 p ≤ (0 : Int) + d320 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d687, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7148 p hg
    simpa only [d687, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d687, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7114 p hg
    simpa only [d687, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7150 (p : Pattern) (guard : d1174 p = 1) : d688 p ≤ (0 : Int) + d321 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d688, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7145 p hg
    simpa only [d688, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d688, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7149 p hg
    simpa only [d688, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7151 (p : Pattern) (guard : d0 p = 1) : d673 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7152 (p : Pattern) (guard : d1174 p = 1) : d673 p ≤ (0 : Int) + d309 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1174, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7117 p hg
    simpa only [d1174, d309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1174, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7151 p hg
    simpa only [d1174, d309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7153 (p : Pattern) (guard : d1174 p = 1) : d673 p ≤ (0 : Int) + d310 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7121 p hg
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7152 p hg
    simpa only [d310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7154 (p : Pattern) (guard : d1174 p = 1) : d674 p ≤ (0 : Int) + d311 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d674, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7143 p hg
    simpa only [d674, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d674, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7153 p hg
    simpa only [d674, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7155 (p : Pattern) (guard : d1174 p = 1) : d689 p ≤ (0 : Int) + d313 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d689, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7127 p hg
    simpa only [d689, d313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d689, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7134 p hg
    simpa only [d689, d313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7156 (p : Pattern) (guard : d1174 p = 1) : d690 p ≤ (0 : Int) + d314 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d690, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7154 p hg
    simpa only [d690, d314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d690, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7155 p hg
    simpa only [d690, d314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7157 (p : Pattern) (guard : d1174 p = 1) : d691 p ≤ (0 : Int) + d322 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d691, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7147 p hg
    simpa only [d691, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d691, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7113 p hg
    simpa only [d691, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7158 (p : Pattern) (guard : d1174 p = 1) : d692 p ≤ (0 : Int) + d323 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d692, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7136 p hg
    simpa only [d692, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d692, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2968 p hg
    simpa only [d692, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7159 (p : Pattern) (guard : d1174 p = 1) : d693 p ≤ (0 : Int) + d324 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d693, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7157 p hg
    simpa only [d693, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d693, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7158 p hg
    simpa only [d693, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7160 (p : Pattern) (guard : d1174 p = 1) : d694 p ≤ (0 : Int) + d325 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d694, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7156 p hg
    simpa only [d694, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d694, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7159 p hg
    simpa only [d694, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7161 (p : Pattern) (guard : d1174 p = 1) : d695 p ≤ (0 : Int) + d326 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d695, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7150 p hg
    simpa only [d695, d326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d695, d326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7160 p hg
    simpa only [d695, d326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7162 (p : Pattern) (guard : d1174 p = 1) : d696 p ≤ (0 : Int) + d327 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d696, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7140 p hg
    simpa only [d696, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1174 p = 1 := by simpa only [d696, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7161 p hg
    simpa only [d696, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7163 (p : Pattern) (guard : d1240 p = 1) : d7 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1240, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3405 p hg
    simpa only [d1240, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1240, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6242 p hg
    simpa only [d1240, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7164 (p : Pattern) (guard : d1240 p = 1) : d7 p ≤ (0 : Int) + d697 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7163 p hg
    simpa only [d697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3420 p hg
    simpa only [d697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7165 (p : Pattern) (guard : d1240 p = 1) : d13 p ≤ (0 : Int) + d11 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1240, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3411 p hg
    simpa only [d1240, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1240, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6247 p hg
    simpa only [d1240, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7166 (p : Pattern) (guard : d1240 p = 1) : d13 p ≤ (0 : Int) + d698 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7165 p hg
    simpa only [d698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3424 p hg
    simpa only [d698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7167 (p : Pattern) (guard : d1240 p = 1) : d653 p ≤ (0 : Int) + d699 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d653, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7164 p hg
    simpa only [d653, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d653, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7166 p hg
    simpa only [d653, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7168 (p : Pattern) (guard : d1240 p = 1) : d654 p ≤ (0 : Int) + d700 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d654, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7164 p hg
    simpa only [d654, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d654, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7167 p hg
    simpa only [d654, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7169 (p : Pattern) (guard : d1240 p = 1) : d655 p ≤ (0 : Int) + d701 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d655, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7164 p hg
    simpa only [d655, d701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d655, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3436 p hg
    simpa only [d655, d701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7170 (p : Pattern) (guard : d1240 p = 1) : d656 p ≤ (0 : Int) + d702 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d656, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7167 p hg
    simpa only [d656, d702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d656, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7169 p hg
    simpa only [d656, d702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7171 (p : Pattern) (guard : d1240 p = 1) : d657 p ≤ (0 : Int) + d703 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d657, d703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7167 p hg
    simpa only [d657, d703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d657, d703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7170 p hg
    simpa only [d657, d703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7172 (p : Pattern) (guard : d1240 p = 1) : d658 p ≤ (0 : Int) + d704 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d658, d704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7168 p hg
    simpa only [d658, d704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d658, d704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7171 p hg
    simpa only [d658, d704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7173 (p : Pattern) (guard : d1240 p = 1) : d659 p ≤ (0 : Int) + d705 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d659, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7166 p hg
    simpa only [d659, d705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d659, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3436 p hg
    simpa only [d659, d705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7174 (p : Pattern) (guard : d1240 p = 1) : d660 p ≤ (0 : Int) + d706 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d660, d706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7166 p hg
    simpa only [d660, d706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d660, d706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7173 p hg
    simpa only [d660, d706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7175 (p : Pattern) (guard : d1240 p = 1) : d661 p ≤ (0 : Int) + d707 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d661, d707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7168 p hg
    simpa only [d661, d707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d661, d707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7174 p hg
    simpa only [d661, d707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7176 (p : Pattern) (guard : d1240 p = 1) : d662 p ≤ (0 : Int) + d708 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d662, d708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7168 p hg
    simpa only [d662, d708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d662, d708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7175 p hg
    simpa only [d662, d708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7177 (p : Pattern) (guard : d1240 p = 1) : d663 p ≤ (0 : Int) + d709 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d663, d709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7168 p hg
    simpa only [d663, d709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d663, d709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7173 p hg
    simpa only [d663, d709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7178 (p : Pattern) (guard : d1240 p = 1) : d664 p ≤ (0 : Int) + d710 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d664, d710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7168 p hg
    simpa only [d664, d710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d664, d710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7177 p hg
    simpa only [d664, d710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7179 (p : Pattern) (guard : d1240 p = 1) : d665 p ≤ (0 : Int) + d711 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d665, d711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7176 p hg
    simpa only [d665, d711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d665, d711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7178 p hg
    simpa only [d665, d711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7180 (p : Pattern) (guard : d1240 p = 1) : d666 p ≤ (0 : Int) + d712 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d666, d712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7167 p hg
    simpa only [d666, d712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d666, d712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7173 p hg
    simpa only [d666, d712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7181 (p : Pattern) (guard : d1240 p = 1) : d667 p ≤ (0 : Int) + d713 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d667, d713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7167 p hg
    simpa only [d667, d713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d667, d713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7180 p hg
    simpa only [d667, d713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7182 (p : Pattern) (guard : d1240 p = 1) : d668 p ≤ (0 : Int) + d714 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d668, d714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7170 p hg
    simpa only [d668, d714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d668, d714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7173 p hg
    simpa only [d668, d714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7183 (p : Pattern) (guard : d1240 p = 1) : d669 p ≤ (0 : Int) + d715 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d669, d715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7170 p hg
    simpa only [d669, d715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d669, d715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7182 p hg
    simpa only [d669, d715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7184 (p : Pattern) (guard : d1240 p = 1) : d670 p ≤ (0 : Int) + d716 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d670, d716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7181 p hg
    simpa only [d670, d716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d670, d716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7183 p hg
    simpa only [d670, d716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7185 (p : Pattern) (guard : d1240 p = 1) : d671 p ≤ (0 : Int) + d717 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d671, d717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7179 p hg
    simpa only [d671, d717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d671, d717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7184 p hg
    simpa only [d671, d717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7186 (p : Pattern) (guard : d1240 p = 1) : d672 p ≤ (0 : Int) + d718 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d672, d718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7172 p hg
    simpa only [d672, d718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d672, d718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7185 p hg
    simpa only [d672, d718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7187 (p : Pattern) (guard : d1240 p = 1) : d673 p ≤ (0 : Int) + d719 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d673, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7164 p hg
    simpa only [d673, d719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d673, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7169 p hg
    simpa only [d673, d719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7188 (p : Pattern) (guard : d1240 p = 1) : d674 p ≤ (0 : Int) + d720 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d674, d720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7168 p hg
    simpa only [d674, d720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d674, d720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7187 p hg
    simpa only [d674, d720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7189 (p : Pattern) (guard : d1240 p = 1) : d675 p ≤ (0 : Int) + d721 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d675, d721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7188 p hg
    simpa only [d675, d721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d675, d721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7174 p hg
    simpa only [d675, d721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7190 (p : Pattern) (guard : d1240 p = 1) : d676 p ≤ (0 : Int) + d722 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d676, d722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7187 p hg
    simpa only [d676, d722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d676, d722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7173 p hg
    simpa only [d676, d722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7191 (p : Pattern) (guard : d1240 p = 1) : d677 p ≤ (0 : Int) + d723 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d677, d723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7187 p hg
    simpa only [d677, d723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d677, d723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7190 p hg
    simpa only [d677, d723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7192 (p : Pattern) (guard : d1240 p = 1) : d678 p ≤ (0 : Int) + d724 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d678, d724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7178 p hg
    simpa only [d678, d724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d678, d724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7191 p hg
    simpa only [d678, d724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7193 (p : Pattern) (guard : d1240 p = 1) : d679 p ≤ (0 : Int) + d725 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d679, d725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7174 p hg
    simpa only [d679, d725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d679, d725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3436 p hg
    simpa only [d679, d725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7194 (p : Pattern) (guard : d1240 p = 1) : d680 p ≤ (0 : Int) + d726 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d680, d726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7174 p hg
    simpa only [d680, d726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d680, d726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7193 p hg
    simpa only [d680, d726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7195 (p : Pattern) (guard : d1240 p = 1) : d681 p ≤ (0 : Int) + d727 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d681, d727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7173 p hg
    simpa only [d681, d727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d681, d727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3436 p hg
    simpa only [d681, d727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7196 (p : Pattern) (guard : d1240 p = 1) : d682 p ≤ (0 : Int) + d728 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d682, d728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7173 p hg
    simpa only [d682, d728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d682, d728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7195 p hg
    simpa only [d682, d728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7197 (p : Pattern) (guard : d1240 p = 1) : d683 p ≤ (0 : Int) + d729 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d683, d729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7194 p hg
    simpa only [d683, d729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d683, d729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7196 p hg
    simpa only [d683, d729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7198 (p : Pattern) (guard : d1240 p = 1) : d684 p ≤ (0 : Int) + d730 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d684, d730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7192 p hg
    simpa only [d684, d730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d684, d730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7197 p hg
    simpa only [d684, d730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7199 (p : Pattern) (guard : d1240 p = 1) : d685 p ≤ (0 : Int) + d731 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d685, d731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7189 p hg
    simpa only [d685, d731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d685, d731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7198 p hg
    simpa only [d685, d731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7200 (p : Pattern) (guard : d1240 p = 1) : d686 p ≤ (0 : Int) + d732 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d686, d732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7186 p hg
    simpa only [d686, d732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d686, d732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7199 p hg
    simpa only [d686, d732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7201 (p : Pattern) (guard : d1240 p = 1) : d687 p ≤ (0 : Int) + d733 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d687, d733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7178 p hg
    simpa only [d687, d733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d687, d733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7184 p hg
    simpa only [d687, d733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7202 (p : Pattern) (guard : d1240 p = 1) : d688 p ≤ (0 : Int) + d734 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d688, d734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7172 p hg
    simpa only [d688, d734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d688, d734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7201 p hg
    simpa only [d688, d734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7203 (p : Pattern) (guard : d1240 p = 1) : d689 p ≤ (0 : Int) + d735 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d689, d735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7174 p hg
    simpa only [d689, d735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d689, d735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7173 p hg
    simpa only [d689, d735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7204 (p : Pattern) (guard : d1240 p = 1) : d690 p ≤ (0 : Int) + d736 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d690, d736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7188 p hg
    simpa only [d690, d736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d690, d736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7203 p hg
    simpa only [d690, d736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7205 (p : Pattern) (guard : d1240 p = 1) : d691 p ≤ (0 : Int) + d737 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d691, d737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7178 p hg
    simpa only [d691, d737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d691, d737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7183 p hg
    simpa only [d691, d737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7206 (p : Pattern) (guard : d1240 p = 1) : d692 p ≤ (0 : Int) + d738 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d692, d738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7196 p hg
    simpa only [d692, d738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d692, d738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3436 p hg
    simpa only [d692, d738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7207 (p : Pattern) (guard : d1240 p = 1) : d693 p ≤ (0 : Int) + d739 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d693, d739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7205 p hg
    simpa only [d693, d739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d693, d739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7206 p hg
    simpa only [d693, d739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7208 (p : Pattern) (guard : d1240 p = 1) : d694 p ≤ (0 : Int) + d740 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d694, d740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7204 p hg
    simpa only [d694, d740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d694, d740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7207 p hg
    simpa only [d694, d740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7209 (p : Pattern) (guard : d1240 p = 1) : d695 p ≤ (0 : Int) + d741 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d695, d741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7202 p hg
    simpa only [d695, d741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d695, d741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7208 p hg
    simpa only [d695, d741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7210 (p : Pattern) (guard : d1240 p = 1) : d696 p ≤ (0 : Int) + d742 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d696, d742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7200 p hg
    simpa only [d696, d742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d696, d742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7209 p hg
    simpa only [d696, d742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7211 (p : Pattern) (guard : d0 p = 1) : d0 p ≤ (0 : Int) + d0 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7212 (p : Pattern) (guard : d1552 p = 1) : d4 p ≤ (0 : Int) + d0 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1552, d4, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7211 p hg
    simpa only [d1552, d4, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d1552, d4, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4485 p hg
    simpa only [d1552, d4, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7213 (p : Pattern) (guard : d1553 p = 1) : d7 p ≤ (0 : Int) + d0 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1552 p = 1 := by simpa only [d1553, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7212 p hg
    simpa only [d1553, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1553, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4484 p hg
    simpa only [d1553, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7214 (p : Pattern) (guard : d1553 p = 1) : d7 p ≤ (0 : Int) + d1554 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1552 p = 1 := by simpa only [d1553, d7, d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7212 p hg
    simpa only [d1553, d7, d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1553, d7, d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1553, d7, d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7215 (p : Pattern) (guard : d1553 p = 1) : d7 p ≤ (0 : Int) + d1555 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d1555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7213 p hg
    simpa only [d1555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d1555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7214 p hg
    simpa only [d1555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7216 (p : Pattern) (guard : d1552 p = 1) : d10 p ≤ (0 : Int) + d1 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1552, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1242 p hg
    simpa only [d1552, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d1552, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4491 p hg
    simpa only [d1552, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7217 (p : Pattern) (guard : d1553 p = 1) : d13 p ≤ (0 : Int) + d1 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1552 p = 1 := by simpa only [d1553, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7216 p hg
    simpa only [d1553, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1553, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4490 p hg
    simpa only [d1553, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7218 (p : Pattern) (guard : d1553 p = 1) : d13 p ≤ (0 : Int) + d1556 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1552 p = 1 := by simpa only [d1553, d13, d1556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7216 p hg
    simpa only [d1553, d13, d1556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1553, d13, d1556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1553, d13, d1556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7219 (p : Pattern) (guard : d1553 p = 1) : d13 p ≤ (0 : Int) + d1557 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d1557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7217 p hg
    simpa only [d1557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d1557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7218 p hg
    simpa only [d1557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7220 (p : Pattern) (guard : d1553 p = 1) : d653 p ≤ (0 : Int) + d1558 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d653, d1558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7215 p hg
    simpa only [d653, d1558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d653, d1558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7219 p hg
    simpa only [d653, d1558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7221 (p : Pattern) (guard : d1553 p = 1) : d654 p ≤ (0 : Int) + d1559 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d654, d1559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7215 p hg
    simpa only [d654, d1559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d654, d1559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7220 p hg
    simpa only [d654, d1559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7222 (p : Pattern) (guard : d1553 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare7223 (p : Pattern) (guard : d1553 p = 1) : d655 p ≤ (0 : Int) + d1560 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d655, d1560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7215 p hg
    simpa only [d655, d1560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d655, d1560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7222 p hg
    simpa only [d655, d1560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7224 (p : Pattern) (guard : d1553 p = 1) : d656 p ≤ (0 : Int) + d1561 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d656, d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7220 p hg
    simpa only [d656, d1561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d656, d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7223 p hg
    simpa only [d656, d1561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7225 (p : Pattern) (guard : d1553 p = 1) : d657 p ≤ (0 : Int) + d1562 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d657, d1562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7220 p hg
    simpa only [d657, d1562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d657, d1562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7224 p hg
    simpa only [d657, d1562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7226 (p : Pattern) (guard : d1553 p = 1) : d658 p ≤ (0 : Int) + d1563 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d658, d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7221 p hg
    simpa only [d658, d1563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d658, d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7225 p hg
    simpa only [d658, d1563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7227 (p : Pattern) (guard : d1553 p = 1) : d659 p ≤ (0 : Int) + d1564 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d659, d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7219 p hg
    simpa only [d659, d1564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d659, d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7222 p hg
    simpa only [d659, d1564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7228 (p : Pattern) (guard : d1553 p = 1) : d660 p ≤ (0 : Int) + d1565 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d660, d1565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7219 p hg
    simpa only [d660, d1565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d660, d1565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7227 p hg
    simpa only [d660, d1565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7229 (p : Pattern) (guard : d1553 p = 1) : d661 p ≤ (0 : Int) + d1566 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d661, d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7221 p hg
    simpa only [d661, d1566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d661, d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7228 p hg
    simpa only [d661, d1566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7230 (p : Pattern) (guard : d1553 p = 1) : d662 p ≤ (0 : Int) + d1567 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d662, d1567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7221 p hg
    simpa only [d662, d1567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d662, d1567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7229 p hg
    simpa only [d662, d1567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7231 (p : Pattern) (guard : d1553 p = 1) : d663 p ≤ (0 : Int) + d1568 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d663, d1568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7221 p hg
    simpa only [d663, d1568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d663, d1568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7227 p hg
    simpa only [d663, d1568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7232 (p : Pattern) (guard : d1553 p = 1) : d664 p ≤ (0 : Int) + d1569 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d664, d1569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7221 p hg
    simpa only [d664, d1569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d664, d1569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7231 p hg
    simpa only [d664, d1569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7233 (p : Pattern) (guard : d1553 p = 1) : d665 p ≤ (0 : Int) + d1570 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d665, d1570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7230 p hg
    simpa only [d665, d1570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d665, d1570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7232 p hg
    simpa only [d665, d1570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7234 (p : Pattern) (guard : d1553 p = 1) : d666 p ≤ (0 : Int) + d1571 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d666, d1571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7220 p hg
    simpa only [d666, d1571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d666, d1571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7227 p hg
    simpa only [d666, d1571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7235 (p : Pattern) (guard : d1553 p = 1) : d667 p ≤ (0 : Int) + d1572 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d667, d1572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7220 p hg
    simpa only [d667, d1572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d667, d1572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7234 p hg
    simpa only [d667, d1572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7236 (p : Pattern) (guard : d1553 p = 1) : d668 p ≤ (0 : Int) + d1573 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d668, d1573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7224 p hg
    simpa only [d668, d1573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d668, d1573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7227 p hg
    simpa only [d668, d1573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7237 (p : Pattern) (guard : d1553 p = 1) : d669 p ≤ (0 : Int) + d1574 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d669, d1574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7224 p hg
    simpa only [d669, d1574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d669, d1574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7236 p hg
    simpa only [d669, d1574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7238 (p : Pattern) (guard : d1553 p = 1) : d670 p ≤ (0 : Int) + d1575 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d670, d1575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7235 p hg
    simpa only [d670, d1575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d670, d1575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7237 p hg
    simpa only [d670, d1575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7239 (p : Pattern) (guard : d1553 p = 1) : d671 p ≤ (0 : Int) + d1576 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d671, d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7233 p hg
    simpa only [d671, d1576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d671, d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7238 p hg
    simpa only [d671, d1576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7240 (p : Pattern) (guard : d1553 p = 1) : d672 p ≤ (0 : Int) + d1577 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d672, d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7226 p hg
    simpa only [d672, d1577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d672, d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7239 p hg
    simpa only [d672, d1577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7241 (p : Pattern) (guard : d1553 p = 1) : d673 p ≤ (0 : Int) + d1578 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d673, d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7215 p hg
    simpa only [d673, d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d673, d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7223 p hg
    simpa only [d673, d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7242 (p : Pattern) (guard : d1553 p = 1) : d674 p ≤ (0 : Int) + d1579 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d674, d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7221 p hg
    simpa only [d674, d1579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d674, d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7241 p hg
    simpa only [d674, d1579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7243 (p : Pattern) (guard : d1553 p = 1) : d675 p ≤ (0 : Int) + d1580 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d675, d1580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7242 p hg
    simpa only [d675, d1580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d675, d1580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7228 p hg
    simpa only [d675, d1580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7244 (p : Pattern) (guard : d1553 p = 1) : d676 p ≤ (0 : Int) + d1581 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d676, d1581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7241 p hg
    simpa only [d676, d1581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d676, d1581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7227 p hg
    simpa only [d676, d1581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7245 (p : Pattern) (guard : d1553 p = 1) : d677 p ≤ (0 : Int) + d1582 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d677, d1582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7241 p hg
    simpa only [d677, d1582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d677, d1582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7244 p hg
    simpa only [d677, d1582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7246 (p : Pattern) (guard : d1553 p = 1) : d678 p ≤ (0 : Int) + d1583 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d678, d1583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7232 p hg
    simpa only [d678, d1583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d678, d1583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7245 p hg
    simpa only [d678, d1583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7247 (p : Pattern) (guard : d1553 p = 1) : d679 p ≤ (0 : Int) + d1584 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d679, d1584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7228 p hg
    simpa only [d679, d1584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d679, d1584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7222 p hg
    simpa only [d679, d1584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7248 (p : Pattern) (guard : d1553 p = 1) : d680 p ≤ (0 : Int) + d1585 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d680, d1585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7228 p hg
    simpa only [d680, d1585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d680, d1585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7247 p hg
    simpa only [d680, d1585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7249 (p : Pattern) (guard : d1553 p = 1) : d681 p ≤ (0 : Int) + d1586 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d681, d1586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7227 p hg
    simpa only [d681, d1586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d681, d1586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7222 p hg
    simpa only [d681, d1586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7250 (p : Pattern) (guard : d1553 p = 1) : d682 p ≤ (0 : Int) + d1587 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d682, d1587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7227 p hg
    simpa only [d682, d1587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d682, d1587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7249 p hg
    simpa only [d682, d1587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7251 (p : Pattern) (guard : d1553 p = 1) : d683 p ≤ (0 : Int) + d1588 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d683, d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7248 p hg
    simpa only [d683, d1588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d683, d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7250 p hg
    simpa only [d683, d1588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7252 (p : Pattern) (guard : d1553 p = 1) : d684 p ≤ (0 : Int) + d1589 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d684, d1589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7246 p hg
    simpa only [d684, d1589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d684, d1589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7251 p hg
    simpa only [d684, d1589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7253 (p : Pattern) (guard : d1553 p = 1) : d685 p ≤ (0 : Int) + d1590 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d685, d1590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7243 p hg
    simpa only [d685, d1590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d685, d1590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7252 p hg
    simpa only [d685, d1590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7254 (p : Pattern) (guard : d1553 p = 1) : d686 p ≤ (0 : Int) + d1591 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d686, d1591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7240 p hg
    simpa only [d686, d1591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d686, d1591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7253 p hg
    simpa only [d686, d1591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7255 (p : Pattern) (guard : d1553 p = 1) : d687 p ≤ (0 : Int) + d1592 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d687, d1592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7232 p hg
    simpa only [d687, d1592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d687, d1592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7238 p hg
    simpa only [d687, d1592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7256 (p : Pattern) (guard : d1553 p = 1) : d688 p ≤ (0 : Int) + d1593 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d688, d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7226 p hg
    simpa only [d688, d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d688, d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7255 p hg
    simpa only [d688, d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7257 (p : Pattern) (guard : d1553 p = 1) : d689 p ≤ (0 : Int) + d1594 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d689, d1594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7228 p hg
    simpa only [d689, d1594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d689, d1594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7227 p hg
    simpa only [d689, d1594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7258 (p : Pattern) (guard : d1553 p = 1) : d690 p ≤ (0 : Int) + d1595 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d690, d1595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7242 p hg
    simpa only [d690, d1595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d690, d1595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7257 p hg
    simpa only [d690, d1595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7259 (p : Pattern) (guard : d1553 p = 1) : d691 p ≤ (0 : Int) + d1596 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d691, d1596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7232 p hg
    simpa only [d691, d1596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d691, d1596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7237 p hg
    simpa only [d691, d1596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7260 (p : Pattern) (guard : d1553 p = 1) : d692 p ≤ (0 : Int) + d1597 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d692, d1597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7250 p hg
    simpa only [d692, d1597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d692, d1597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7222 p hg
    simpa only [d692, d1597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7261 (p : Pattern) (guard : d1553 p = 1) : d693 p ≤ (0 : Int) + d1598 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d693, d1598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7259 p hg
    simpa only [d693, d1598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d693, d1598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7260 p hg
    simpa only [d693, d1598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7262 (p : Pattern) (guard : d1553 p = 1) : d694 p ≤ (0 : Int) + d1599 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d694, d1599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7258 p hg
    simpa only [d694, d1599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d694, d1599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7261 p hg
    simpa only [d694, d1599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7263 (p : Pattern) (guard : d1553 p = 1) : d695 p ≤ (0 : Int) + d1600 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d695, d1600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7256 p hg
    simpa only [d695, d1600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d695, d1600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7262 p hg
    simpa only [d695, d1600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7264 (p : Pattern) (guard : d1553 p = 1) : d696 p ≤ (0 : Int) + d1601 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d696, d1601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7254 p hg
    simpa only [d696, d1601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d696, d1601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7263 p hg
    simpa only [d696, d1601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7265 (p : Pattern) (guard : d1171 p = 1) : d7 p ≤ (0 : Int) + d538 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1171, d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7086 p hg
    simpa only [d1171, d538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1171, d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d1171, d538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7266 (p : Pattern) (guard : d1171 p = 1) : d7 p ≤ (0 : Int) + d539 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1171, d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7086 p hg
    simpa only [d1171, d539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1171, d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2350 p hg
    simpa only [d1171, d539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7267 (p : Pattern) (guard : d1171 p = 1) : d13 p ≤ (0 : Int) + d540 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1171, d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7088 p hg
    simpa only [d1171, d540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1171, d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2353 p hg
    simpa only [d1171, d540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7268 (p : Pattern) (guard : d1171 p = 1) : d653 p ≤ (0 : Int) + d541 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d653, d541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7266 p hg
    simpa only [d653, d541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d653, d541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7267 p hg
    simpa only [d653, d541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7269 (p : Pattern) (guard : d1171 p = 1) : d654 p ≤ (0 : Int) + d542 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d654, d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7265 p hg
    simpa only [d654, d542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d654, d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7268 p hg
    simpa only [d654, d542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7270 (p : Pattern) (guard : d1171 p = 1) : d654 p ≤ (0 : Int) + d543 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d654, d543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7266 p hg
    simpa only [d654, d543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d654, d543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7268 p hg
    simpa only [d654, d543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7271 (p : Pattern) (guard : d1171 p = 1) : d654 p ≤ (0 : Int) + d544 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7269 p hg
    simpa only [d544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7270 p hg
    simpa only [d544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7272 (p : Pattern) (guard : d1167 p = 1) : d7 p ≤ (0 : Int) + d18 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1167, d7, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare659 p hg
    simpa only [d1167, d7, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1167, d7, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6254 p hg
    simpa only [d1167, d7, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7273 (p : Pattern) (guard : d1171 p = 1) : d7 p ≤ (0 : Int) + d545 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1171, d545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7272 p hg
    simpa only [d1171, d545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1171, d545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2350 p hg
    simpa only [d1171, d545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7274 (p : Pattern) (guard : d1167 p = 1) : d13 p ≤ (0 : Int) + d22 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1167, d13, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare665 p hg
    simpa only [d1167, d13, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1167, d13, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6259 p hg
    simpa only [d1167, d13, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7275 (p : Pattern) (guard : d1171 p = 1) : d13 p ≤ (0 : Int) + d546 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1171, d546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7274 p hg
    simpa only [d1171, d546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1171, d546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2353 p hg
    simpa only [d1171, d546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7276 (p : Pattern) (guard : d1171 p = 1) : d653 p ≤ (0 : Int) + d547 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d653, d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7273 p hg
    simpa only [d653, d547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d653, d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7275 p hg
    simpa only [d653, d547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7277 (p : Pattern) (guard : d1171 p = 1) : d654 p ≤ (0 : Int) + d548 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d654, d548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7273 p hg
    simpa only [d654, d548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d654, d548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7276 p hg
    simpa only [d654, d548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7278 (p : Pattern) (guard : d1171 p = 1) : d654 p ≤ (0 : Int) + d549 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7270 p hg
    simpa only [d549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7277 p hg
    simpa only [d549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7279 (p : Pattern) (guard : d1171 p = 1) : d654 p ≤ (0 : Int) + d550 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7271 p hg
    simpa only [d550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7278 p hg
    simpa only [d550, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
