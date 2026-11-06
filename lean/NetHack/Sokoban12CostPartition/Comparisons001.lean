/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare140 (p : Pattern) (guard : d742 p = 1) : d55 p ≤ (2 : Int) + d141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare138 p hg
    simpa only [d742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare139 p hg
    simpa only [d742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare141 (p : Pattern) (guard : d1 p = 1) : d60 p ≤ (2 : Int) + d143 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare103 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare142 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (2 : Int) + d144 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d65, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare136 p hg
    simpa only [d65, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d65, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare141 p hg
    simpa only [d65, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare143 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (2 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare105 p hg
    simpa only [d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare142 p hg
    simpa only [d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare144 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (2 : Int) + d148 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare143 p hg
    simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27 p hg
    simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare145 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (2 : Int) + d148 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare146 (p : Pattern) (guard : d742 p = 1) : d65 p ≤ (2 : Int) + d148 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare144 p hg
    simpa only [d742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare145 p hg
    simpa only [d742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare147 (p : Pattern) (guard : d742 p = 1) : d66 p ≤ (2 : Int) + d748 p := by
  cases selected : p 141 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d66, d748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare140 p hg
    simpa only [d66, d748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d66, d748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare146 p hg
    simpa only [d66, d748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare148 (p : Pattern) (guard : d742 p = 1) : d66 p ≤ (2 : Int) + d749 p := by
  cases selected : p 134 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare147 p hg
    simpa only [d749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare134 p hg
    simpa only [d749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare149 (p : Pattern) (guard : d742 p = 1) : d159 p ≤ (2 : Int) + d750 p := by
  cases selected : p 133 with
  | false =>
    have hg : d742 p = 1 := by simpa only [d159, d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare135 p hg
    simpa only [d159, d750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d159, d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare148 p hg
    simpa only [d159, d750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare150 (p : Pattern) (guard : d743 p = 1) : d160 p ≤ (2 : Int) + d750 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d743, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare114 p hg
    simpa only [d743, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d742 p = 1 := by simpa only [d743, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare149 p hg
    simpa only [d743, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare151 (p : Pattern) (guard : d743 p = 1) : d161 p ≤ (2 : Int) + d751 p := by
  cases selected : p 108 with
  | false =>
    have hg : d743 p = 1 := by simpa only [d161, d751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare113 p hg
    simpa only [d161, d751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d743 p = 1 := by simpa only [d161, d751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare150 p hg
    simpa only [d161, d751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare152 (p : Pattern) (guard : d1 p = 1) : d113 p ≤ (0 : Int) + d113 p := by
  omega
theorem compare153 (p : Pattern) (guard : d0 p = 1) : d133 p ≤ (0 : Int) + d66 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare154 (p : Pattern) (guard : d753 p = 1) : d134 p ≤ (0 : Int) + d210 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d753, d134, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare152 p hg
    simpa only [d753, d134, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d753, d134, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare153 p hg
    simpa only [d753, d134, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare155 (p : Pattern) (guard : d0 p = 1) : d135 p ≤ (0 : Int) + d215 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare156 (p : Pattern) (guard : d754 p = 1) : d136 p ≤ (0 : Int) + d216 p := by
  cases selected : p 132 with
  | false =>
    have hg : d753 p = 1 := by simpa only [d754, d136, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare154 p hg
    simpa only [d754, d136, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d754, d136, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare155 p hg
    simpa only [d754, d136, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare157 (p : Pattern) (guard : d1 p = 1) : d67 p ≤ (0 : Int) + d67 p := by
  omega
theorem compare158 (p : Pattern) (guard : d0 p = 1) : d151 p ≤ (0 : Int) + d66 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare159 (p : Pattern) (guard : d753 p = 1) : d152 p ≤ (0 : Int) + d217 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d753, d152, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare157 p hg
    simpa only [d753, d152, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d753, d152, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare158 p hg
    simpa only [d753, d152, d217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare160 (p : Pattern) (guard : d0 p = 1) : d159 p ≤ (0 : Int) + d73 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare161 (p : Pattern) (guard : d754 p = 1) : d160 p ≤ (0 : Int) + d218 p := by
  cases selected : p 132 with
  | false =>
    have hg : d753 p = 1 := by simpa only [d754, d160, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare159 p hg
    simpa only [d754, d160, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d754, d160, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare160 p hg
    simpa only [d754, d160, d218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare162 (p : Pattern) (guard : d754 p = 1) : d161 p ≤ (0 : Int) + d219 p := by
  cases selected : p 108 with
  | false =>
    have hg : d754 p = 1 := by simpa only [d161, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare156 p hg
    simpa only [d161, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d754 p = 1 := by simpa only [d161, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare161 p hg
    simpa only [d161, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare163 (p : Pattern) (guard : d737 p = 1) : d74 p ≤ (0 : Int) + d74 p := by
  omega
theorem compare164 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (0 : Int) + d74 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare165 (p : Pattern) (guard : d755 p = 1) : d75 p ≤ (0 : Int) + d74 p := by
  cases selected : p 108 with
  | false =>
    have hg : d737 p = 1 := by simpa only [d755, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare163 p hg
    simpa only [d755, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d755, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare164 p hg
    simpa only [d755, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare166 (p : Pattern) (guard : d0 p = 1) : d64 p ≤ (2 : Int) + d451 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare167 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (2 : Int) + d56 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare168 (p : Pattern) (guard : d758 p = 1) : d55 p ≤ (2 : Int) + d56 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare78 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare167 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare169 (p : Pattern) (guard : d0 p = 1) : d65 p ≤ (2 : Int) + d62 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare170 (p : Pattern) (guard : d758 p = 1) : d65 p ≤ (2 : Int) + d62 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare91 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare169 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare171 (p : Pattern) (guard : d758 p = 1) : d66 p ≤ (2 : Int) + d451 p := by
  cases selected : p 141 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d66, d451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare168 p hg
    simpa only [d66, d451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d66, d451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare170 p hg
    simpa only [d66, d451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare172 (p : Pattern) (guard : d759 p = 1) : d67 p ≤ (2 : Int) + d451 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d759, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare166 p hg
    simpa only [d759, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d759, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare171 p hg
    simpa only [d759, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare173 (p : Pattern) (guard : d0 p = 1) : d70 p ≤ (2 : Int) + d458 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare174 (p : Pattern) (guard : d758 p = 1) : d55 p ≤ (2 : Int) + d55 p := by
  omega
theorem compare175 (p : Pattern) (guard : d758 p = 1) : d55 p ≤ (2 : Int) + d456 p := by
  cases selected : p 158 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare168 p hg
    simpa only [d456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare174 p hg
    simpa only [d456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare176 (p : Pattern) (guard : d758 p = 1) : d65 p ≤ (2 : Int) + d65 p := by
  omega
theorem compare177 (p : Pattern) (guard : d758 p = 1) : d65 p ≤ (2 : Int) + d457 p := by
  cases selected : p 158 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare170 p hg
    simpa only [d457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare176 p hg
    simpa only [d457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare178 (p : Pattern) (guard : d758 p = 1) : d66 p ≤ (2 : Int) + d458 p := by
  cases selected : p 141 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d66, d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare175 p hg
    simpa only [d66, d458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d66, d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare177 p hg
    simpa only [d66, d458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare179 (p : Pattern) (guard : d759 p = 1) : d71 p ≤ (2 : Int) + d458 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d759, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare173 p hg
    simpa only [d759, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d759, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare178 p hg
    simpa only [d759, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare180 (p : Pattern) (guard : d759 p = 1) : d72 p ≤ (2 : Int) + d761 p := by
  cases selected : p 133 with
  | false =>
    have hg : d759 p = 1 := by simpa only [d72, d761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare172 p hg
    simpa only [d72, d761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d759 p = 1 := by simpa only [d72, d761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare179 p hg
    simpa only [d72, d761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare181 (p : Pattern) (guard : d759 p = 1) : d66 p ≤ (2 : Int) + d66 p := by
  omega
theorem compare182 (p : Pattern) (guard : d759 p = 1) : d73 p ≤ (2 : Int) + d762 p := by
  cases selected : p 133 with
  | false =>
    have hg : d759 p = 1 := by simpa only [d73, d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare179 p hg
    simpa only [d73, d762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d759 p = 1 := by simpa only [d73, d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare181 p hg
    simpa only [d73, d762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare183 (p : Pattern) (guard : d759 p = 1) : d74 p ≤ (2 : Int) + d763 p := by
  cases selected : p 132 with
  | false =>
    have hg : d759 p = 1 := by simpa only [d74, d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare180 p hg
    simpa only [d74, d763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d759 p = 1 := by simpa only [d74, d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare182 p hg
    simpa only [d74, d763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare184 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (2 : Int) + d763 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare185 (p : Pattern) (guard : d760 p = 1) : d75 p ≤ (2 : Int) + d763 p := by
  cases selected : p 108 with
  | false =>
    have hg : d759 p = 1 := by simpa only [d760, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare183 p hg
    simpa only [d760, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d760, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare184 p hg
    simpa only [d760, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare186 (p : Pattern) (guard : d1 p = 1) : d64 p ≤ (0 : Int) + d64 p := by
  omega
theorem compare187 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (0 : Int) + d227 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare188 (p : Pattern) (guard : d737 p = 1) : d67 p ≤ (0 : Int) + d228 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d737, d67, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare186 p hg
    simpa only [d737, d67, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d737, d67, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare187 p hg
    simpa only [d737, d67, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare189 (p : Pattern) (guard : d1 p = 1) : d70 p ≤ (0 : Int) + d70 p := by
  omega
theorem compare190 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (0 : Int) + d231 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare191 (p : Pattern) (guard : d737 p = 1) : d71 p ≤ (0 : Int) + d232 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d737, d71, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare189 p hg
    simpa only [d737, d71, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d737, d71, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare190 p hg
    simpa only [d737, d71, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare192 (p : Pattern) (guard : d737 p = 1) : d72 p ≤ (0 : Int) + d233 p := by
  cases selected : p 133 with
  | false =>
    have hg : d737 p = 1 := by simpa only [d72, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare188 p hg
    simpa only [d72, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d737 p = 1 := by simpa only [d72, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare191 p hg
    simpa only [d72, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare193 (p : Pattern) (guard : d737 p = 1) : d66 p ≤ (0 : Int) + d66 p := by
  omega
theorem compare194 (p : Pattern) (guard : d737 p = 1) : d73 p ≤ (0 : Int) + d234 p := by
  cases selected : p 133 with
  | false =>
    have hg : d737 p = 1 := by simpa only [d73, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare191 p hg
    simpa only [d73, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d737 p = 1 := by simpa only [d73, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare193 p hg
    simpa only [d73, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare195 (p : Pattern) (guard : d737 p = 1) : d74 p ≤ (0 : Int) + d235 p := by
  cases selected : p 132 with
  | false =>
    have hg : d737 p = 1 := by simpa only [d74, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare192 p hg
    simpa only [d74, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d737 p = 1 := by simpa only [d74, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare194 p hg
    simpa only [d74, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare196 (p : Pattern) (guard : d755 p = 1) : d75 p ≤ (0 : Int) + d236 p := by
  cases selected : p 108 with
  | false =>
    have hg : d737 p = 1 := by simpa only [d755, d75, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare195 p hg
    simpa only [d755, d75, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d755, d75, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare164 p hg
    simpa only [d755, d75, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare197 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (0 : Int) + d112 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare198 (p : Pattern) (guard : d737 p = 1) : d67 p ≤ (0 : Int) + d113 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d737, d67, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare186 p hg
    simpa only [d737, d67, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d737, d67, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare197 p hg
    simpa only [d737, d67, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare199 (p : Pattern) (guard : d0 p = 1) : d71 p ≤ (0 : Int) + d66 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare200 (p : Pattern) (guard : d765 p = 1) : d72 p ≤ (0 : Int) + d210 p := by
  cases selected : p 133 with
  | false =>
    have hg : d737 p = 1 := by simpa only [d765, d72, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare198 p hg
    simpa only [d765, d72, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d765, d72, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare199 p hg
    simpa only [d765, d72, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare201 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (0 : Int) + d213 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare202 (p : Pattern) (guard : d737 p = 1) : d71 p ≤ (0 : Int) + d214 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d737, d71, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare189 p hg
    simpa only [d737, d71, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d737, d71, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare201 p hg
    simpa only [d737, d71, d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare203 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (0 : Int) + d66 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare204 (p : Pattern) (guard : d765 p = 1) : d73 p ≤ (0 : Int) + d215 p := by
  cases selected : p 133 with
  | false =>
    have hg : d737 p = 1 := by simpa only [d765, d73, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare202 p hg
    simpa only [d765, d73, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d765, d73, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare203 p hg
    simpa only [d765, d73, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare205 (p : Pattern) (guard : d765 p = 1) : d74 p ≤ (0 : Int) + d216 p := by
  cases selected : p 132 with
  | false =>
    have hg : d765 p = 1 := by simpa only [d74, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare200 p hg
    simpa only [d74, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d765 p = 1 := by simpa only [d74, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare204 p hg
    simpa only [d74, d216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare206 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (0 : Int) + d218 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare207 (p : Pattern) (guard : d766 p = 1) : d75 p ≤ (0 : Int) + d219 p := by
  cases selected : p 108 with
  | false =>
    have hg : d765 p = 1 := by simpa only [d766, d75, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare205 p hg
    simpa only [d766, d75, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d766, d75, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare206 p hg
    simpa only [d766, d75, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare208 (p : Pattern) (guard : d1 p = 1) : d57 p ≤ (0 : Int) + d57 p := by
  omega
theorem compare209 (p : Pattern) (guard : d0 p = 1) : d57 p ≤ (0 : Int) + d267 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare210 (p : Pattern) (guard : d768 p = 1) : d57 p ≤ (0 : Int) + d268 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare208 p hg
    simpa only [d768, d268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare209 p hg
    simpa only [d768, d268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare211 (p : Pattern) (guard : d1 p = 1) : d179 p ≤ (0 : Int) + d179 p := by
  omega
theorem compare212 (p : Pattern) (guard : d0 p = 1) : d179 p ≤ (0 : Int) + d278 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare213 (p : Pattern) (guard : d768 p = 1) : d179 p ≤ (0 : Int) + d279 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare211 p hg
    simpa only [d768, d279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare212 p hg
    simpa only [d768, d279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare214 (p : Pattern) (guard : d768 p = 1) : d180 p ≤ (0 : Int) + d280 p := by
  cases selected : p 134 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d180, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare210 p hg
    simpa only [d180, d280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d180, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare213 p hg
    simpa only [d180, d280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare215 (p : Pattern) (guard : d1 p = 1) : d68 p ≤ (0 : Int) + d68 p := by
  omega
theorem compare216 (p : Pattern) (guard : d0 p = 1) : d68 p ≤ (0 : Int) + d281 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare217 (p : Pattern) (guard : d768 p = 1) : d68 p ≤ (0 : Int) + d282 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare215 p hg
    simpa only [d768, d282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare216 p hg
    simpa only [d768, d282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare218 (p : Pattern) (guard : d1 p = 1) : d181 p ≤ (0 : Int) + d181 p := by
  omega
theorem compare219 (p : Pattern) (guard : d0 p = 1) : d181 p ≤ (0 : Int) + d283 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare220 (p : Pattern) (guard : d768 p = 1) : d181 p ≤ (0 : Int) + d284 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare218 p hg
    simpa only [d768, d284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare219 p hg
    simpa only [d768, d284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare221 (p : Pattern) (guard : d768 p = 1) : d182 p ≤ (0 : Int) + d285 p := by
  cases selected : p 134 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d182, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare217 p hg
    simpa only [d182, d285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d182, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare220 p hg
    simpa only [d182, d285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare222 (p : Pattern) (guard : d768 p = 1) : d183 p ≤ (0 : Int) + d286 p := by
  cases selected : p 133 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d183, d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare214 p hg
    simpa only [d183, d286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d183, d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare221 p hg
    simpa only [d183, d286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare223 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (0 : Int) + d55 p := by
  omega
theorem compare224 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (0 : Int) + d269 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare225 (p : Pattern) (guard : d768 p = 1) : d55 p ≤ (0 : Int) + d287 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare223 p hg
    simpa only [d768, d287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare224 p hg
    simpa only [d768, d287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare226 (p : Pattern) (guard : d768 p = 1) : d184 p ≤ (0 : Int) + d288 p := by
  cases selected : p 133 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d184, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare221 p hg
    simpa only [d184, d288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d184, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare225 p hg
    simpa only [d184, d288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare227 (p : Pattern) (guard : d768 p = 1) : d185 p ≤ (0 : Int) + d289 p := by
  cases selected : p 132 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d185, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare222 p hg
    simpa only [d185, d289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d185, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare226 p hg
    simpa only [d185, d289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare228 (p : Pattern) (guard : d1 p = 1) : d186 p ≤ (0 : Int) + d186 p := by
  omega
theorem compare229 (p : Pattern) (guard : d0 p = 1) : d186 p ≤ (0 : Int) + d295 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare230 (p : Pattern) (guard : d768 p = 1) : d186 p ≤ (0 : Int) + d296 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare228 p hg
    simpa only [d768, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare229 p hg
    simpa only [d768, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare231 (p : Pattern) (guard : d768 p = 1) : d187 p ≤ (0 : Int) + d297 p := by
  cases selected : p 134 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d187, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare230 p hg
    simpa only [d187, d297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d187, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare225 p hg
    simpa only [d187, d297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare232 (p : Pattern) (guard : d1 p = 1) : d188 p ≤ (0 : Int) + d188 p := by
  omega
theorem compare233 (p : Pattern) (guard : d0 p = 1) : d188 p ≤ (0 : Int) + d300 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare234 (p : Pattern) (guard : d768 p = 1) : d188 p ≤ (0 : Int) + d301 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare232 p hg
    simpa only [d768, d301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare233 p hg
    simpa only [d768, d301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare235 (p : Pattern) (guard : d768 p = 1) : d189 p ≤ (0 : Int) + d302 p := by
  cases selected : p 134 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d189, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare234 p hg
    simpa only [d189, d302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d189, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare225 p hg
    simpa only [d189, d302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare236 (p : Pattern) (guard : d768 p = 1) : d190 p ≤ (0 : Int) + d303 p := by
  cases selected : p 133 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d190, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare231 p hg
    simpa only [d190, d303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d190, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare235 p hg
    simpa only [d190, d303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare237 (p : Pattern) (guard : d1 p = 1) : d191 p ≤ (0 : Int) + d191 p := by
  omega
theorem compare238 (p : Pattern) (guard : d0 p = 1) : d191 p ≤ (0 : Int) + d304 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare239 (p : Pattern) (guard : d768 p = 1) : d191 p ≤ (0 : Int) + d305 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare237 p hg
    simpa only [d768, d305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare238 p hg
    simpa only [d768, d305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare240 (p : Pattern) (guard : d768 p = 1) : d192 p ≤ (0 : Int) + d306 p := by
  cases selected : p 134 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d192, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare239 p hg
    simpa only [d192, d306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d192, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare225 p hg
    simpa only [d192, d306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare241 (p : Pattern) (guard : d768 p = 1) : d193 p ≤ (0 : Int) + d307 p := by
  cases selected : p 133 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d193, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare240 p hg
    simpa only [d193, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d193, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare225 p hg
    simpa only [d193, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare242 (p : Pattern) (guard : d768 p = 1) : d194 p ≤ (0 : Int) + d308 p := by
  cases selected : p 132 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d194, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare236 p hg
    simpa only [d194, d308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d194, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare241 p hg
    simpa only [d194, d308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare243 (p : Pattern) (guard : d768 p = 1) : d195 p ≤ (0 : Int) + d309 p := by
  cases selected : p 108 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d195, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare227 p hg
    simpa only [d195, d309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d195, d309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare242 p hg
    simpa only [d195, d309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare244 (p : Pattern) (guard : d767 p = 1) : d195 p ≤ (0 : Int) + d195 p := by
  omega
theorem compare245 (p : Pattern) (guard : d1 p = 1) : d195 p ≤ (0 : Int) + d195 p := by
  omega
theorem compare246 (p : Pattern) (guard : d1 p = 1) : d195 p ≤ (1 : Int) + d195 p := by
  omega
theorem compare247 (p : Pattern) (guard : d0 p = 1) : d57 p ≤ (0 : Int) + d63 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare248 (p : Pattern) (guard : d768 p = 1) : d57 p ≤ (0 : Int) + d64 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare208 p hg
    simpa only [d768, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare247 p hg
    simpa only [d768, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare249 (p : Pattern) (guard : d0 p = 1) : d179 p ≤ (0 : Int) + d237 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare250 (p : Pattern) (guard : d768 p = 1) : d179 p ≤ (0 : Int) + d238 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare211 p hg
    simpa only [d768, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare249 p hg
    simpa only [d768, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare251 (p : Pattern) (guard : d768 p = 1) : d180 p ≤ (0 : Int) + d239 p := by
  cases selected : p 134 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d180, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare248 p hg
    simpa only [d180, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d180, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare250 p hg
    simpa only [d180, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare252 (p : Pattern) (guard : d0 p = 1) : d68 p ≤ (0 : Int) + d69 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare253 (p : Pattern) (guard : d768 p = 1) : d68 p ≤ (0 : Int) + d70 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare215 p hg
    simpa only [d768, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare252 p hg
    simpa only [d768, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare254 (p : Pattern) (guard : d0 p = 1) : d181 p ≤ (0 : Int) + d240 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare255 (p : Pattern) (guard : d768 p = 1) : d181 p ≤ (0 : Int) + d241 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare218 p hg
    simpa only [d768, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare254 p hg
    simpa only [d768, d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare256 (p : Pattern) (guard : d768 p = 1) : d182 p ≤ (0 : Int) + d242 p := by
  cases selected : p 134 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d182, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare253 p hg
    simpa only [d182, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d182, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare255 p hg
    simpa only [d182, d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare257 (p : Pattern) (guard : d768 p = 1) : d183 p ≤ (0 : Int) + d243 p := by
  cases selected : p 133 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d183, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare251 p hg
    simpa only [d183, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d183, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare256 p hg
    simpa only [d183, d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare258 (p : Pattern) (guard : d0 p = 1) : d55 p ≤ (0 : Int) + d65 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare259 (p : Pattern) (guard : d768 p = 1) : d55 p ≤ (0 : Int) + d66 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare223 p hg
    simpa only [d768, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare258 p hg
    simpa only [d768, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare260 (p : Pattern) (guard : d768 p = 1) : d184 p ≤ (0 : Int) + d244 p := by
  cases selected : p 133 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d184, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare256 p hg
    simpa only [d184, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d184, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare259 p hg
    simpa only [d184, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare261 (p : Pattern) (guard : d768 p = 1) : d185 p ≤ (0 : Int) + d245 p := by
  cases selected : p 132 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d185, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare257 p hg
    simpa only [d185, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d185, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare260 p hg
    simpa only [d185, d245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare262 (p : Pattern) (guard : d0 p = 1) : d186 p ≤ (0 : Int) + d246 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare263 (p : Pattern) (guard : d768 p = 1) : d186 p ≤ (0 : Int) + d247 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare228 p hg
    simpa only [d768, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare262 p hg
    simpa only [d768, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare264 (p : Pattern) (guard : d768 p = 1) : d187 p ≤ (0 : Int) + d248 p := by
  cases selected : p 134 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d187, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare263 p hg
    simpa only [d187, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d187, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare259 p hg
    simpa only [d187, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare265 (p : Pattern) (guard : d0 p = 1) : d188 p ≤ (0 : Int) + d249 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare266 (p : Pattern) (guard : d768 p = 1) : d188 p ≤ (0 : Int) + d250 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare232 p hg
    simpa only [d768, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare265 p hg
    simpa only [d768, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare267 (p : Pattern) (guard : d768 p = 1) : d189 p ≤ (0 : Int) + d251 p := by
  cases selected : p 134 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d189, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare266 p hg
    simpa only [d189, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d189, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare259 p hg
    simpa only [d189, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare268 (p : Pattern) (guard : d768 p = 1) : d190 p ≤ (0 : Int) + d252 p := by
  cases selected : p 133 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d190, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare264 p hg
    simpa only [d190, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d190, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare267 p hg
    simpa only [d190, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare269 (p : Pattern) (guard : d0 p = 1) : d191 p ≤ (0 : Int) + d253 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare270 (p : Pattern) (guard : d768 p = 1) : d191 p ≤ (0 : Int) + d254 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d768, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare237 p hg
    simpa only [d768, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d768, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare269 p hg
    simpa only [d768, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare271 (p : Pattern) (guard : d768 p = 1) : d192 p ≤ (0 : Int) + d255 p := by
  cases selected : p 134 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d192, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare270 p hg
    simpa only [d192, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d192, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare259 p hg
    simpa only [d192, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare272 (p : Pattern) (guard : d768 p = 1) : d193 p ≤ (0 : Int) + d256 p := by
  cases selected : p 133 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d193, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare271 p hg
    simpa only [d193, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d193, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare259 p hg
    simpa only [d193, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare273 (p : Pattern) (guard : d768 p = 1) : d194 p ≤ (0 : Int) + d257 p := by
  cases selected : p 132 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d194, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare268 p hg
    simpa only [d194, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d194, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare272 p hg
    simpa only [d194, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare274 (p : Pattern) (guard : d768 p = 1) : d195 p ≤ (0 : Int) + d258 p := by
  cases selected : p 108 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d195, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare261 p hg
    simpa only [d195, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d768 p = 1 := by simpa only [d195, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare273 p hg
    simpa only [d195, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare275 (p : Pattern) (guard : d770 p = 1) : d195 p ≤ (1 : Int) + d195 p := by
  omega
theorem compare276 (p : Pattern) (guard : d0 p = 1) : d134 p ≤ (0 : Int) + d133 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare277 (p : Pattern) (guard : d1 p = 1) : d133 p ≤ (0 : Int) + d133 p := by
  omega
theorem compare278 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (0 : Int) + d133 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare279 (p : Pattern) (guard : d753 p = 1) : d135 p ≤ (0 : Int) + d133 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d753, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare277 p hg
    simpa only [d753, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d753, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare278 p hg
    simpa only [d753, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
