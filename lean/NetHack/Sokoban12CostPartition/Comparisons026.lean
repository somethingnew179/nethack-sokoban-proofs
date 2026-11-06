/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons025
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare3640 (p : Pattern) (guard : d793 p = 1) : d191 p ≤ (0 : Int) + d55 p := by
  cases selected : p 158 with
  | false =>
    have hg : d793 p = 1 := by simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3629 p hg
    simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d793 p = 1 := by simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3616 p hg
    simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3641 (p : Pattern) (guard : d793 p = 1) : d253 p ≤ (0 : Int) + d65 p := by
  cases selected : p 158 with
  | false =>
    have hg : d793 p = 1 := by simpa only [d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3633 p hg
    simpa only [d253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d793 p = 1 := by simpa only [d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3618 p hg
    simpa only [d253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3642 (p : Pattern) (guard : d793 p = 1) : d254 p ≤ (0 : Int) + d66 p := by
  cases selected : p 141 with
  | false =>
    have hg : d793 p = 1 := by simpa only [d254, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3640 p hg
    simpa only [d254, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d793 p = 1 := by simpa only [d254, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3641 p hg
    simpa only [d254, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3643 (p : Pattern) (guard : d793 p = 1) : d255 p ≤ (0 : Int) + d66 p := by
  cases selected : p 134 with
  | false =>
    have hg : d793 p = 1 := by simpa only [d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3642 p hg
    simpa only [d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d793 p = 1 := by simpa only [d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3636 p hg
    simpa only [d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3644 (p : Pattern) (guard : d802 p = 1) : d256 p ≤ (0 : Int) + d66 p := by
  cases selected : p 133 with
  | false =>
    have hg : d793 p = 1 := by simpa only [d802, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3643 p hg
    simpa only [d802, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d802, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare203 p hg
    simpa only [d802, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3645 (p : Pattern) (guard : d802 p = 1) : d257 p ≤ (0 : Int) + d1156 p := by
  cases selected : p 132 with
  | false =>
    have hg : d802 p = 1 := by simpa only [d257, d1156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3639 p hg
    simpa only [d257, d1156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d802 p = 1 := by simpa only [d257, d1156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3644 p hg
    simpa only [d257, d1156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3646 (p : Pattern) (guard : d802 p = 1) : d258 p ≤ (0 : Int) + d1157 p := by
  cases selected : p 108 with
  | false =>
    have hg : d802 p = 1 := by simpa only [d258, d1157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3626 p hg
    simpa only [d258, d1157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d802 p = 1 := by simpa only [d258, d1157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3645 p hg
    simpa only [d258, d1157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3647 (p : Pattern) (guard : d829 p = 1) : d64 p ≤ (0 : Int) + d451 p := by
  cases selected : p 141 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d64, d451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2111 p hg
    simpa only [d64, d451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d64, d451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2117 p hg
    simpa only [d64, d451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3648 (p : Pattern) (guard : d0 p = 1) : d119 p ≤ (0 : Int) + d55 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3649 (p : Pattern) (guard : d829 p = 1) : d120 p ≤ (0 : Int) + d56 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d829, d120, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare282 p hg
    simpa only [d829, d120, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, d120, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3648 p hg
    simpa only [d829, d120, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3650 (p : Pattern) (guard : d829 p = 1) : d121 p ≤ (0 : Int) + d452 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d121, d452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3649 p hg
    simpa only [d121, d452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d121, d452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2120 p hg
    simpa only [d121, d452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3651 (p : Pattern) (guard : d829 p = 1) : d122 p ≤ (0 : Int) + d452 p := by
  cases selected : p 159 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2121 p hg
    simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3650 p hg
    simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3652 (p : Pattern) (guard : d829 p = 1) : d179 p ≤ (0 : Int) + d452 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2121 p hg
    simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3651 p hg
    simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3653 (p : Pattern) (guard : d0 p = 1) : d125 p ≤ (0 : Int) + d60 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3654 (p : Pattern) (guard : d829 p = 1) : d126 p ≤ (0 : Int) + d61 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d829, d126, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare295 p hg
    simpa only [d829, d126, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, d126, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3653 p hg
    simpa only [d829, d126, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3655 (p : Pattern) (guard : d829 p = 1) : d127 p ≤ (0 : Int) + d62 p := by
  cases selected : p 168 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d127, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3649 p hg
    simpa only [d127, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d127, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3654 p hg
    simpa only [d127, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3656 (p : Pattern) (guard : d829 p = 1) : d128 p ≤ (0 : Int) + d453 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d128, d453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3655 p hg
    simpa only [d128, d453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d128, d453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2124 p hg
    simpa only [d128, d453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3657 (p : Pattern) (guard : d829 p = 1) : d129 p ≤ (0 : Int) + d453 p := by
  cases selected : p 159 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2125 p hg
    simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3656 p hg
    simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3658 (p : Pattern) (guard : d829 p = 1) : d237 p ≤ (0 : Int) + d453 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2125 p hg
    simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3657 p hg
    simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3659 (p : Pattern) (guard : d829 p = 1) : d238 p ≤ (0 : Int) + d454 p := by
  cases selected : p 141 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d238, d454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3652 p hg
    simpa only [d238, d454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d238, d454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3658 p hg
    simpa only [d238, d454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3660 (p : Pattern) (guard : d829 p = 1) : d239 p ≤ (0 : Int) + d455 p := by
  cases selected : p 134 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d239, d455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3647 p hg
    simpa only [d239, d455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d239, d455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3659 p hg
    simpa only [d239, d455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3661 (p : Pattern) (guard : d829 p = 1) : d68 p ≤ (0 : Int) + d456 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d68, d456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2111 p hg
    simpa only [d68, d456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d68, d456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2120 p hg
    simpa only [d68, d456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3662 (p : Pattern) (guard : d829 p = 1) : d69 p ≤ (0 : Int) + d457 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d69, d457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2117 p hg
    simpa only [d69, d457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d69, d457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2124 p hg
    simpa only [d69, d457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3663 (p : Pattern) (guard : d829 p = 1) : d70 p ≤ (0 : Int) + d458 p := by
  cases selected : p 141 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d70, d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3661 p hg
    simpa only [d70, d458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d70, d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3662 p hg
    simpa only [d70, d458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3664 (p : Pattern) (guard : d829 p = 1) : d181 p ≤ (0 : Int) + d459 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d181, d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3651 p hg
    simpa only [d181, d459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d181, d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2120 p hg
    simpa only [d181, d459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3665 (p : Pattern) (guard : d829 p = 1) : d240 p ≤ (0 : Int) + d460 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d240, d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3657 p hg
    simpa only [d240, d460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d240, d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2124 p hg
    simpa only [d240, d460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3666 (p : Pattern) (guard : d829 p = 1) : d241 p ≤ (0 : Int) + d461 p := by
  cases selected : p 141 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d241, d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3664 p hg
    simpa only [d241, d461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d241, d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3665 p hg
    simpa only [d241, d461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3667 (p : Pattern) (guard : d829 p = 1) : d242 p ≤ (0 : Int) + d462 p := by
  cases selected : p 134 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d242, d462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3663 p hg
    simpa only [d242, d462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d242, d462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3666 p hg
    simpa only [d242, d462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3668 (p : Pattern) (guard : d829 p = 1) : d243 p ≤ (0 : Int) + d463 p := by
  cases selected : p 133 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d243, d463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3660 p hg
    simpa only [d243, d463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d243, d463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3667 p hg
    simpa only [d243, d463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3669 (p : Pattern) (guard : d829 p = 1) : d244 p ≤ (0 : Int) + d464 p := by
  cases selected : p 133 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d244, d464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3667 p hg
    simpa only [d244, d464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d244, d464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3521 p hg
    simpa only [d244, d464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3670 (p : Pattern) (guard : d829 p = 1) : d245 p ≤ (0 : Int) + d465 p := by
  cases selected : p 132 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d245, d465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3668 p hg
    simpa only [d245, d465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d245, d465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3669 p hg
    simpa only [d245, d465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3671 (p : Pattern) (guard : d829 p = 1) : d139 p ≤ (0 : Int) + d466 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d139, d466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3649 p hg
    simpa only [d139, d466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d139, d466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2151 p hg
    simpa only [d139, d466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3672 (p : Pattern) (guard : d829 p = 1) : d153 p ≤ (0 : Int) + d467 p := by
  cases selected : p 159 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d153, d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2111 p hg
    simpa only [d153, d467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d153, d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3671 p hg
    simpa only [d153, d467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3673 (p : Pattern) (guard : d829 p = 1) : d186 p ≤ (0 : Int) + d468 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d186, d468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2111 p hg
    simpa only [d186, d468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d186, d468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3672 p hg
    simpa only [d186, d468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3674 (p : Pattern) (guard : d829 p = 1) : d146 p ≤ (0 : Int) + d469 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d146, d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3655 p hg
    simpa only [d146, d469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d146, d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2155 p hg
    simpa only [d146, d469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3675 (p : Pattern) (guard : d829 p = 1) : d155 p ≤ (0 : Int) + d470 p := by
  cases selected : p 159 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d155, d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2117 p hg
    simpa only [d155, d470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d155, d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3674 p hg
    simpa only [d155, d470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3676 (p : Pattern) (guard : d829 p = 1) : d246 p ≤ (0 : Int) + d471 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d246, d471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2117 p hg
    simpa only [d246, d471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d246, d471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3675 p hg
    simpa only [d246, d471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3677 (p : Pattern) (guard : d829 p = 1) : d247 p ≤ (0 : Int) + d472 p := by
  cases selected : p 141 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d247, d472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3673 p hg
    simpa only [d247, d472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d247, d472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3676 p hg
    simpa only [d247, d472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3678 (p : Pattern) (guard : d829 p = 1) : d248 p ≤ (0 : Int) + d473 p := by
  cases selected : p 134 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d248, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3677 p hg
    simpa only [d248, d473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d248, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3521 p hg
    simpa only [d248, d473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3679 (p : Pattern) (guard : d829 p = 1) : d140 p ≤ (0 : Int) + d466 p := by
  cases selected : p 159 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2152 p hg
    simpa only [d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3671 p hg
    simpa only [d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3680 (p : Pattern) (guard : d829 p = 1) : d188 p ≤ (0 : Int) + d474 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d188, d474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3679 p hg
    simpa only [d188, d474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d188, d474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2120 p hg
    simpa only [d188, d474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3681 (p : Pattern) (guard : d829 p = 1) : d147 p ≤ (0 : Int) + d469 p := by
  cases selected : p 159 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2156 p hg
    simpa only [d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3674 p hg
    simpa only [d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3682 (p : Pattern) (guard : d829 p = 1) : d249 p ≤ (0 : Int) + d475 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d249, d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3681 p hg
    simpa only [d249, d475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d249, d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2124 p hg
    simpa only [d249, d475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3683 (p : Pattern) (guard : d829 p = 1) : d250 p ≤ (0 : Int) + d476 p := by
  cases selected : p 141 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d250, d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3680 p hg
    simpa only [d250, d476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d250, d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3682 p hg
    simpa only [d250, d476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3684 (p : Pattern) (guard : d829 p = 1) : d251 p ≤ (0 : Int) + d477 p := by
  cases selected : p 134 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d251, d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3683 p hg
    simpa only [d251, d477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d251, d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3521 p hg
    simpa only [d251, d477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3685 (p : Pattern) (guard : d829 p = 1) : d252 p ≤ (0 : Int) + d478 p := by
  cases selected : p 133 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d252, d478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3678 p hg
    simpa only [d252, d478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d252, d478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3684 p hg
    simpa only [d252, d478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3686 (p : Pattern) (guard : d829 p = 1) : d191 p ≤ (0 : Int) + d479 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d191, d479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3672 p hg
    simpa only [d191, d479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d191, d479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2120 p hg
    simpa only [d191, d479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3687 (p : Pattern) (guard : d829 p = 1) : d253 p ≤ (0 : Int) + d480 p := by
  cases selected : p 158 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d253, d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3675 p hg
    simpa only [d253, d480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d253, d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2124 p hg
    simpa only [d253, d480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3688 (p : Pattern) (guard : d829 p = 1) : d254 p ≤ (0 : Int) + d481 p := by
  cases selected : p 141 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d254, d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3686 p hg
    simpa only [d254, d481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d254, d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3687 p hg
    simpa only [d254, d481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3689 (p : Pattern) (guard : d829 p = 1) : d255 p ≤ (0 : Int) + d482 p := by
  cases selected : p 134 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d255, d482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3688 p hg
    simpa only [d255, d482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d255, d482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3521 p hg
    simpa only [d255, d482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3690 (p : Pattern) (guard : d829 p = 1) : d256 p ≤ (0 : Int) + d483 p := by
  cases selected : p 133 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d256, d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3689 p hg
    simpa only [d256, d483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d256, d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3521 p hg
    simpa only [d256, d483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3691 (p : Pattern) (guard : d829 p = 1) : d257 p ≤ (0 : Int) + d484 p := by
  cases selected : p 132 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d257, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3685 p hg
    simpa only [d257, d484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d257, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3690 p hg
    simpa only [d257, d484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3692 (p : Pattern) (guard : d829 p = 1) : d258 p ≤ (0 : Int) + d485 p := by
  cases selected : p 108 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d258, d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3670 p hg
    simpa only [d258, d485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d258, d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3691 p hg
    simpa only [d258, d485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3693 (p : Pattern) (guard : d1158 p = 1) : d7 p ≤ (4 : Int) + d7 p := by
  omega
theorem compare3694 (p : Pattern) (guard : d0 p = 1) : d7 p ≤ (4 : Int) + d7 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3695 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (4 : Int) + d0 p := by
  change (2 : Int) ≤ (4 : Int) + 0
  decide
theorem compare3696 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (4 : Int) + d2 p := by
  change (4 : Int) ≤ (4 : Int) + 2
  decide
theorem compare3697 (p : Pattern) (guard : d1 p = 1) : d54 p ≤ (4 : Int) + d6 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d54, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3695 p hg
    simpa only [d54, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d54, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3696 p hg
    simpa only [d54, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3698 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (4 : Int) + d7 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d55, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3695 p hg
    simpa only [d55, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d55, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3697 p hg
    simpa only [d55, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3699 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (4 : Int) + d7 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3700 (p : Pattern) (guard : d851 p = 1) : d55 p ≤ (4 : Int) + d7 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3698 p hg
    simpa only [d851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3699 p hg
    simpa only [d851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3701 (p : Pattern) (guard : d1158 p = 1) : d56 p ≤ (4 : Int) + d7 p := by
  cases selected : p 186 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1158, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3694 p hg
    simpa only [d1158, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d1158, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3700 p hg
    simpa only [d1158, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3702 (p : Pattern) (guard : d1158 p = 1) : d57 p ≤ (4 : Int) + d7 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3693 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3701 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3703 (p : Pattern) (guard : d1158 p = 1) : d12 p ≤ (4 : Int) + d12 p := by
  omega
theorem compare3704 (p : Pattern) (guard : d0 p = 1) : d11 p ≤ (4 : Int) + d11 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3705 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (4 : Int) + d1 p := by
  change (3 : Int) ≤ (4 : Int) + 1
  decide
theorem compare3706 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (4 : Int) + d8 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d9, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3695 p hg
    simpa only [d9, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d9, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3705 p hg
    simpa only [d9, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3707 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (4 : Int) + d3 p := by
  change (5 : Int) ≤ (4 : Int) + 3
  decide
theorem compare3708 (p : Pattern) (guard : d1 p = 1) : d58 p ≤ (4 : Int) + d9 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d58, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3696 p hg
    simpa only [d58, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d58, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3707 p hg
    simpa only [d58, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3709 (p : Pattern) (guard : d1 p = 1) : d59 p ≤ (4 : Int) + d10 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d59, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3706 p hg
    simpa only [d59, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d59, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3708 p hg
    simpa only [d59, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3710 (p : Pattern) (guard : d1 p = 1) : d60 p ≤ (4 : Int) + d11 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d60, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3706 p hg
    simpa only [d60, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d60, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3709 p hg
    simpa only [d60, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3711 (p : Pattern) (guard : d0 p = 1) : d60 p ≤ (4 : Int) + d11 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3712 (p : Pattern) (guard : d851 p = 1) : d60 p ≤ (4 : Int) + d11 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3710 p hg
    simpa only [d851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3711 p hg
    simpa only [d851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3713 (p : Pattern) (guard : d1158 p = 1) : d61 p ≤ (4 : Int) + d11 p := by
  cases selected : p 186 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1158, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3704 p hg
    simpa only [d1158, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d1158, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3712 p hg
    simpa only [d1158, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3714 (p : Pattern) (guard : d1158 p = 1) : d62 p ≤ (4 : Int) + d12 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d62, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3701 p hg
    simpa only [d62, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d62, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3713 p hg
    simpa only [d62, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3715 (p : Pattern) (guard : d1158 p = 1) : d63 p ≤ (4 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3703 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3714 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3716 (p : Pattern) (guard : d1158 p = 1) : d64 p ≤ (4 : Int) + d13 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d64, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3702 p hg
    simpa only [d64, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d64, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3715 p hg
    simpa only [d64, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3717 (p : Pattern) (guard : d1158 p = 1) : d106 p ≤ (4 : Int) + d106 p := by
  omega
theorem compare3718 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (4 : Int) + d7 p := by
  omega
theorem compare3719 (p : Pattern) (guard : d851 p = 1) : d119 p ≤ (4 : Int) + d7 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d851, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3718 p hg
    simpa only [d851, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d851, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3699 p hg
    simpa only [d851, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3720 (p : Pattern) (guard : d1158 p = 1) : d120 p ≤ (4 : Int) + d7 p := by
  cases selected : p 186 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1158, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3694 p hg
    simpa only [d1158, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d1158, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3719 p hg
    simpa only [d1158, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3721 (p : Pattern) (guard : d1158 p = 1) : d55 p ≤ (4 : Int) + d55 p := by
  omega
theorem compare3722 (p : Pattern) (guard : d1158 p = 1) : d121 p ≤ (4 : Int) + d106 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d121, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3720 p hg
    simpa only [d121, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d121, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3721 p hg
    simpa only [d121, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3723 (p : Pattern) (guard : d1158 p = 1) : d122 p ≤ (4 : Int) + d106 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3717 p hg
    simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3722 p hg
    simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3724 (p : Pattern) (guard : d1158 p = 1) : d179 p ≤ (4 : Int) + d106 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3717 p hg
    simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3723 p hg
    simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3725 (p : Pattern) (guard : d1158 p = 1) : d109 p ≤ (4 : Int) + d109 p := by
  omega
theorem compare3726 (p : Pattern) (guard : d1 p = 1) : d11 p ≤ (4 : Int) + d11 p := by
  omega
theorem compare3727 (p : Pattern) (guard : d851 p = 1) : d125 p ≤ (4 : Int) + d11 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d851, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3726 p hg
    simpa only [d851, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d851, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3711 p hg
    simpa only [d851, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3728 (p : Pattern) (guard : d1158 p = 1) : d126 p ≤ (4 : Int) + d11 p := by
  cases selected : p 186 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1158, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3704 p hg
    simpa only [d1158, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d1158, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3727 p hg
    simpa only [d1158, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3729 (p : Pattern) (guard : d1158 p = 1) : d127 p ≤ (4 : Int) + d12 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d127, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3720 p hg
    simpa only [d127, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d127, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3728 p hg
    simpa only [d127, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3730 (p : Pattern) (guard : d1158 p = 1) : d65 p ≤ (4 : Int) + d65 p := by
  omega
theorem compare3731 (p : Pattern) (guard : d1158 p = 1) : d128 p ≤ (4 : Int) + d109 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d128, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3729 p hg
    simpa only [d128, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d128, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3730 p hg
    simpa only [d128, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3732 (p : Pattern) (guard : d1158 p = 1) : d129 p ≤ (4 : Int) + d109 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3725 p hg
    simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3731 p hg
    simpa only [d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3733 (p : Pattern) (guard : d1158 p = 1) : d237 p ≤ (4 : Int) + d109 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3725 p hg
    simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3732 p hg
    simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3734 (p : Pattern) (guard : d1158 p = 1) : d238 p ≤ (4 : Int) + d227 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d238, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3724 p hg
    simpa only [d238, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d238, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3733 p hg
    simpa only [d238, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3735 (p : Pattern) (guard : d1158 p = 1) : d239 p ≤ (4 : Int) + d1018 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d239, d1018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3716 p hg
    simpa only [d239, d1018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d239, d1018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3734 p hg
    simpa only [d239, d1018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3736 (p : Pattern) (guard : d1158 p = 1) : d68 p ≤ (4 : Int) + d832 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d68, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3702 p hg
    simpa only [d68, d832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d68, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3721 p hg
    simpa only [d68, d832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3737 (p : Pattern) (guard : d1158 p = 1) : d69 p ≤ (4 : Int) + d833 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d69, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3715 p hg
    simpa only [d69, d833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d69, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3730 p hg
    simpa only [d69, d833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3738 (p : Pattern) (guard : d1158 p = 1) : d70 p ≤ (4 : Int) + d834 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d70, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3736 p hg
    simpa only [d70, d834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d70, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3737 p hg
    simpa only [d70, d834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3739 (p : Pattern) (guard : d1158 p = 1) : d181 p ≤ (4 : Int) + d229 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d181, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3723 p hg
    simpa only [d181, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d181, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3721 p hg
    simpa only [d181, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3740 (p : Pattern) (guard : d1158 p = 1) : d240 p ≤ (4 : Int) + d230 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d240, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3732 p hg
    simpa only [d240, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d240, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3730 p hg
    simpa only [d240, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3741 (p : Pattern) (guard : d1158 p = 1) : d241 p ≤ (4 : Int) + d231 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d241, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3739 p hg
    simpa only [d241, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d241, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3740 p hg
    simpa only [d241, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3742 (p : Pattern) (guard : d1158 p = 1) : d242 p ≤ (4 : Int) + d1019 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d242, d1019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3738 p hg
    simpa only [d242, d1019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d242, d1019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3741 p hg
    simpa only [d242, d1019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3743 (p : Pattern) (guard : d1158 p = 1) : d243 p ≤ (4 : Int) + d1020 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d243, d1020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3735 p hg
    simpa only [d243, d1020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d243, d1020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3742 p hg
    simpa only [d243, d1020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3744 (p : Pattern) (guard : d1158 p = 1) : d66 p ≤ (4 : Int) + d66 p := by
  omega
theorem compare3745 (p : Pattern) (guard : d1158 p = 1) : d244 p ≤ (4 : Int) + d1021 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d244, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3742 p hg
    simpa only [d244, d1021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d244, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3744 p hg
    simpa only [d244, d1021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3746 (p : Pattern) (guard : d1158 p = 1) : d245 p ≤ (4 : Int) + d1022 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d245, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3743 p hg
    simpa only [d245, d1022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d245, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3745 p hg
    simpa only [d245, d1022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3747 (p : Pattern) (guard : d0 p = 1) : d119 p ≤ (4 : Int) + d55 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3748 (p : Pattern) (guard : d851 p = 1) : d55 p ≤ (4 : Int) + d55 p := by
  omega
theorem compare3749 (p : Pattern) (guard : d1158 p = 1) : d137 p ≤ (4 : Int) + d55 p := by
  cases selected : p 186 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1158, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3747 p hg
    simpa only [d1158, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d1158, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3748 p hg
    simpa only [d1158, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3750 (p : Pattern) (guard : d1158 p = 1) : d139 p ≤ (4 : Int) + d106 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d139, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3720 p hg
    simpa only [d139, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d139, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3749 p hg
    simpa only [d139, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3751 (p : Pattern) (guard : d1158 p = 1) : d153 p ≤ (4 : Int) + d1159 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d153, d1159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3702 p hg
    simpa only [d153, d1159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d153, d1159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3750 p hg
    simpa only [d153, d1159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3752 (p : Pattern) (guard : d1158 p = 1) : d186 p ≤ (4 : Int) + d1160 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d186, d1160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3702 p hg
    simpa only [d186, d1160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d186, d1160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3751 p hg
    simpa only [d186, d1160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3753 (p : Pattern) (guard : d0 p = 1) : d125 p ≤ (4 : Int) + d60 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare3754 (p : Pattern) (guard : d851 p = 1) : d60 p ≤ (4 : Int) + d60 p := by
  omega
theorem compare3755 (p : Pattern) (guard : d1158 p = 1) : d143 p ≤ (4 : Int) + d60 p := by
  cases selected : p 186 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1158, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3753 p hg
    simpa only [d1158, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d1158, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3754 p hg
    simpa only [d1158, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3756 (p : Pattern) (guard : d1158 p = 1) : d144 p ≤ (4 : Int) + d65 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d144, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3749 p hg
    simpa only [d144, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d144, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3755 p hg
    simpa only [d144, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3757 (p : Pattern) (guard : d1158 p = 1) : d146 p ≤ (4 : Int) + d109 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d146, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3729 p hg
    simpa only [d146, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d146, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3756 p hg
    simpa only [d146, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3758 (p : Pattern) (guard : d1158 p = 1) : d155 p ≤ (4 : Int) + d1161 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d155, d1161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3715 p hg
    simpa only [d155, d1161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d155, d1161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3757 p hg
    simpa only [d155, d1161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3759 (p : Pattern) (guard : d1158 p = 1) : d246 p ≤ (4 : Int) + d1162 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d246, d1162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3715 p hg
    simpa only [d246, d1162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d246, d1162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3758 p hg
    simpa only [d246, d1162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3760 (p : Pattern) (guard : d1158 p = 1) : d247 p ≤ (4 : Int) + d1163 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d247, d1163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3752 p hg
    simpa only [d247, d1163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d247, d1163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3759 p hg
    simpa only [d247, d1163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3761 (p : Pattern) (guard : d1158 p = 1) : d248 p ≤ (4 : Int) + d1164 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d248, d1164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3760 p hg
    simpa only [d248, d1164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d248, d1164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3744 p hg
    simpa only [d248, d1164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3762 (p : Pattern) (guard : d1158 p = 1) : d138 p ≤ (4 : Int) + d106 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d138, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3693 p hg
    simpa only [d138, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d138, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3749 p hg
    simpa only [d138, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3763 (p : Pattern) (guard : d1158 p = 1) : d140 p ≤ (4 : Int) + d106 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3762 p hg
    simpa only [d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3750 p hg
    simpa only [d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3764 (p : Pattern) (guard : d1158 p = 1) : d188 p ≤ (4 : Int) + d229 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d188, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3763 p hg
    simpa only [d188, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d188, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3721 p hg
    simpa only [d188, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3765 (p : Pattern) (guard : d1158 p = 1) : d145 p ≤ (4 : Int) + d109 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d145, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3703 p hg
    simpa only [d145, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d145, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3756 p hg
    simpa only [d145, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3766 (p : Pattern) (guard : d1158 p = 1) : d147 p ≤ (4 : Int) + d109 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3765 p hg
    simpa only [d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3757 p hg
    simpa only [d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3767 (p : Pattern) (guard : d1158 p = 1) : d249 p ≤ (4 : Int) + d230 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d249, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3766 p hg
    simpa only [d249, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d249, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3730 p hg
    simpa only [d249, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3768 (p : Pattern) (guard : d1158 p = 1) : d250 p ≤ (4 : Int) + d231 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d250, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3764 p hg
    simpa only [d250, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d250, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3767 p hg
    simpa only [d250, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3769 (p : Pattern) (guard : d1158 p = 1) : d251 p ≤ (4 : Int) + d370 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d251, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3768 p hg
    simpa only [d251, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d251, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3744 p hg
    simpa only [d251, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3770 (p : Pattern) (guard : d1158 p = 1) : d252 p ≤ (4 : Int) + d1165 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d252, d1165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3761 p hg
    simpa only [d252, d1165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d252, d1165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3769 p hg
    simpa only [d252, d1165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3771 (p : Pattern) (guard : d1158 p = 1) : d191 p ≤ (4 : Int) + d1166 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d191, d1166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3751 p hg
    simpa only [d191, d1166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d191, d1166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3721 p hg
    simpa only [d191, d1166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3772 (p : Pattern) (guard : d1158 p = 1) : d253 p ≤ (4 : Int) + d1167 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d253, d1167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3758 p hg
    simpa only [d253, d1167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d253, d1167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3730 p hg
    simpa only [d253, d1167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3773 (p : Pattern) (guard : d1158 p = 1) : d254 p ≤ (4 : Int) + d1168 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d254, d1168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3771 p hg
    simpa only [d254, d1168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d254, d1168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3772 p hg
    simpa only [d254, d1168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3774 (p : Pattern) (guard : d1158 p = 1) : d255 p ≤ (4 : Int) + d1169 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d255, d1169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3773 p hg
    simpa only [d255, d1169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d255, d1169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3744 p hg
    simpa only [d255, d1169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3775 (p : Pattern) (guard : d1158 p = 1) : d256 p ≤ (4 : Int) + d1170 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d256, d1170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3774 p hg
    simpa only [d256, d1170, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d256, d1170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3744 p hg
    simpa only [d256, d1170, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3776 (p : Pattern) (guard : d1158 p = 1) : d257 p ≤ (4 : Int) + d1171 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d257, d1171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3770 p hg
    simpa only [d257, d1171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d257, d1171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3775 p hg
    simpa only [d257, d1171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3777 (p : Pattern) (guard : d1158 p = 1) : d258 p ≤ (4 : Int) + d1172 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d258, d1172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3746 p hg
    simpa only [d258, d1172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d258, d1172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3776 p hg
    simpa only [d258, d1172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3778 (p : Pattern) (guard : d1016 p = 1) : d57 p ≤ (0 : Int) + d106 p := by
  cases selected : p 160 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d1016, d57, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2397 p hg
    simpa only [d1016, d57, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1016, d57, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare684 p hg
    simpa only [d1016, d57, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3779 (p : Pattern) (guard : d1050 p = 1) : d57 p ≤ (0 : Int) + d106 p := by
  cases selected : p 159 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare685 p hg
    simpa only [d1050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1016 p = 1 := by simpa only [d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3778 p hg
    simpa only [d1050, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
