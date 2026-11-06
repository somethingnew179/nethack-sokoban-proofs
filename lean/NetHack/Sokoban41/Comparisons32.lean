/- Staged soko4-1 certificate. No result until all kernel checks pass. -/
import NetHack.Sokoban41.Comparisons31
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem c5120 (pattern : Ten) (guard : d723 pattern = 1) : d130 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d722 pattern = 1 := by simpa only [d723, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5118 pattern childGuard
    simpa only [d723, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d723, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5119 pattern childGuard
    simpa only [d723, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5121 (pattern : Ten) (guard : d0 pattern = 1) : d131 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5122 (pattern : Ten) (guard : d724 pattern = 1) : d132 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d723 pattern = 1 := by simpa only [d724, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5120 pattern childGuard
    simpa only [d724, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d724, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5121 pattern childGuard
    simpa only [d724, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5123 (pattern : Ten) (guard : d724 pattern = 1) : d133 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d723 pattern = 1 := by simpa only [d724, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5069 pattern childGuard
    simpa only [d724, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d724, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5085 pattern childGuard
    simpa only [d724, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5124 (pattern : Ten) (guard : d0 pattern = 1) : d8 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5125 (pattern : Ten) (guard : d723 pattern = 1) : d134 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d722 pattern = 1 := by simpa only [d723, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5067 pattern childGuard
    simpa only [d723, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d723, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5124 pattern childGuard
    simpa only [d723, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5126 (pattern : Ten) (guard : d0 pattern = 1) : d56 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5127 (pattern : Ten) (guard : d724 pattern = 1) : d135 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d723 pattern = 1 := by simpa only [d724, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5125 pattern childGuard
    simpa only [d724, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d724, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5126 pattern childGuard
    simpa only [d724, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5128 (pattern : Ten) (guard : d0 pattern = 1) : d142 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5129 (pattern : Ten) (guard : d606 pattern = 1) : d12 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5047 pattern childGuard
    simpa only [d606, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5 pattern childGuard
    simpa only [d606, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5130 (pattern : Ten) (guard : d607 pattern = 1) : d140 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5129 pattern childGuard
    simpa only [d607, d140, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5049 pattern childGuard
    simpa only [d607, d140, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5131 (pattern : Ten) (guard : d608 pattern = 1) : d143 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5130 pattern childGuard
    simpa only [d608, d143, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5051 pattern childGuard
    simpa only [d608, d143, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5132 (pattern : Ten) (guard : d721 pattern = 1) : d145 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d721, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5128 pattern childGuard
    simpa only [d721, d145, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d608 pattern = 1 := by simpa only [d721, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5131 pattern childGuard
    simpa only [d721, d145, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5133 (pattern : Ten) (guard : d0 pattern = 1) : d146 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5134 (pattern : Ten) (guard : d722 pattern = 1) : d147 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d721 pattern = 1 := by simpa only [d722, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5132 pattern childGuard
    simpa only [d722, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d722, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5133 pattern childGuard
    simpa only [d722, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5135 (pattern : Ten) (guard : d723 pattern = 1) : d148 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d722 pattern = 1 := by simpa only [d723, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5134 pattern childGuard
    simpa only [d723, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d723, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5056 pattern childGuard
    simpa only [d723, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5136 (pattern : Ten) (guard : d724 pattern = 1) : d149 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d723 pattern = 1 := by simpa only [d724, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5135 pattern childGuard
    simpa only [d724, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d724, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5058 pattern childGuard
    simpa only [d724, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5137 (pattern : Ten) (guard : d608 pattern = 1) : d9 pattern ≤ (0 : Int) + d9 pattern := by
  omega
theorem c5138 (pattern : Ten) (guard : d721 pattern = 1) : d150 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d721, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c882 pattern childGuard
    simpa only [d721, d150, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d608 pattern = 1 := by simpa only [d721, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5137 pattern childGuard
    simpa only [d721, d150, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5139 (pattern : Ten) (guard : d722 pattern = 1) : d151 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d721 pattern = 1 := by simpa only [d722, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5138 pattern childGuard
    simpa only [d722, d151, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d722, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c882 pattern childGuard
    simpa only [d722, d151, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5140 (pattern : Ten) (guard : d0 pattern = 1) : d152 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5141 (pattern : Ten) (guard : d723 pattern = 1) : d154 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d722 pattern = 1 := by simpa only [d723, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5139 pattern childGuard
    simpa only [d723, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d723, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5140 pattern childGuard
    simpa only [d723, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5142 (pattern : Ten) (guard : d0 pattern = 1) : d155 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5143 (pattern : Ten) (guard : d724 pattern = 1) : d156 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d723 pattern = 1 := by simpa only [d724, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5141 pattern childGuard
    simpa only [d724, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d724, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5142 pattern childGuard
    simpa only [d724, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5144 (pattern : Ten) (guard : d359 pattern = 1) : d2 pattern ≤ (0 : Int) + d9 pattern := by
  change (2 : Int) ≤ (0 : Int) + 9
  decide
theorem c5145 (pattern : Ten) (guard : d0 pattern = 1) : d4 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5146 (pattern : Ten) (guard : d606 pattern = 1) : d44 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5144 pattern childGuard
    simpa only [d606, d44, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5145 pattern childGuard
    simpa only [d606, d44, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5147 (pattern : Ten) (guard : d0 pattern = 1) : d43 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5148 (pattern : Ten) (guard : d607 pattern = 1) : d50 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5146 pattern childGuard
    simpa only [d607, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5147 pattern childGuard
    simpa only [d607, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5149 (pattern : Ten) (guard : d0 pattern = 1) : d51 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5150 (pattern : Ten) (guard : d608 pattern = 1) : d55 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5148 pattern childGuard
    simpa only [d608, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5149 pattern childGuard
    simpa only [d608, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5151 (pattern : Ten) (guard : d721 pattern = 1) : d160 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d721, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c882 pattern childGuard
    simpa only [d721, d160, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d608 pattern = 1 := by simpa only [d721, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5150 pattern childGuard
    simpa only [d721, d160, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5152 (pattern : Ten) (guard : d0 pattern = 1) : d161 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5153 (pattern : Ten) (guard : d722 pattern = 1) : d165 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d721 pattern = 1 := by simpa only [d722, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5151 pattern childGuard
    simpa only [d722, d165, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d722, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5152 pattern childGuard
    simpa only [d722, d165, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5154 (pattern : Ten) (guard : d0 pattern = 1) : d166 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5155 (pattern : Ten) (guard : d723 pattern = 1) : d168 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d722 pattern = 1 := by simpa only [d723, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5153 pattern childGuard
    simpa only [d723, d168, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d723, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5154 pattern childGuard
    simpa only [d723, d168, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5156 (pattern : Ten) (guard : d0 pattern = 1) : d169 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5157 (pattern : Ten) (guard : d724 pattern = 1) : d170 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d723 pattern = 1 := by simpa only [d724, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5155 pattern childGuard
    simpa only [d724, d170, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d724, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5156 pattern childGuard
    simpa only [d724, d170, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5158 (pattern : Ten) (guard : d0 pattern = 1) : d17 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5159 (pattern : Ten) (guard : d359 pattern = 1) : d0 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) ≤ (0 : Int) + 6
  decide
theorem c5160 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5161 (pattern : Ten) (guard : d606 pattern = 1) : d12 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5159 pattern childGuard
    simpa only [d606, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5160 pattern childGuard
    simpa only [d606, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5162 (pattern : Ten) (guard : d607 pattern = 1) : d18 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5161 pattern childGuard
    simpa only [d607, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5160 pattern childGuard
    simpa only [d607, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5163 (pattern : Ten) (guard : d735 pattern = 1) : d23 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d735, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5158 pattern childGuard
    simpa only [d735, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d607 pattern = 1 := by simpa only [d735, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5162 pattern childGuard
    simpa only [d735, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5164 (pattern : Ten) (guard : d0 pattern = 1) : d24 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5165 (pattern : Ten) (guard : d736 pattern = 1) : d29 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d735 pattern = 1 := by simpa only [d736, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5163 pattern childGuard
    simpa only [d736, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d736, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5164 pattern childGuard
    simpa only [d736, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5166 (pattern : Ten) (guard : d0 pattern = 1) : d30 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5167 (pattern : Ten) (guard : d737 pattern = 1) : d33 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d736 pattern = 1 := by simpa only [d737, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5165 pattern childGuard
    simpa only [d737, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d737, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5166 pattern childGuard
    simpa only [d737, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5168 (pattern : Ten) (guard : d0 pattern = 1) : d34 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5169 (pattern : Ten) (guard : d738 pattern = 1) : d35 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d737 pattern = 1 := by simpa only [d738, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5167 pattern childGuard
    simpa only [d738, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d738, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5168 pattern childGuard
    simpa only [d738, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5170 (pattern : Ten) (guard : d0 pattern = 1) : d36 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5171 (pattern : Ten) (guard : d739 pattern = 1) : d37 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d738 pattern = 1 := by simpa only [d739, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5169 pattern childGuard
    simpa only [d739, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d739, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5170 pattern childGuard
    simpa only [d739, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5172 (pattern : Ten) (guard : d0 pattern = 1) : d48 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5173 (pattern : Ten) (guard : d359 pattern = 1) : d6 pattern ≤ (0 : Int) + d6 pattern := by
  omega
theorem c5174 (pattern : Ten) (guard : d606 pattern = 1) : d43 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5173 pattern childGuard
    simpa only [d606, d43, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5160 pattern childGuard
    simpa only [d606, d43, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5175 (pattern : Ten) (guard : d607 pattern = 1) : d49 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5174 pattern childGuard
    simpa only [d607, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5160 pattern childGuard
    simpa only [d607, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5176 (pattern : Ten) (guard : d735 pattern = 1) : d54 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d735, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5172 pattern childGuard
    simpa only [d735, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d607 pattern = 1 := by simpa only [d735, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5175 pattern childGuard
    simpa only [d735, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5177 (pattern : Ten) (guard : d0 pattern = 1) : d54 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5178 (pattern : Ten) (guard : d736 pattern = 1) : d54 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d735 pattern = 1 := by simpa only [d736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5176 pattern childGuard
    simpa only [d736, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5177 pattern childGuard
    simpa only [d736, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5179 (pattern : Ten) (guard : d737 pattern = 1) : d54 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d736 pattern = 1 := by simpa only [d737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5178 pattern childGuard
    simpa only [d737, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5177 pattern childGuard
    simpa only [d737, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5180 (pattern : Ten) (guard : d0 pattern = 1) : d62 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5181 (pattern : Ten) (guard : d738 pattern = 1) : d64 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d737 pattern = 1 := by simpa only [d738, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5179 pattern childGuard
    simpa only [d738, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d738, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5180 pattern childGuard
    simpa only [d738, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5182 (pattern : Ten) (guard : d0 pattern = 1) : d65 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5183 (pattern : Ten) (guard : d739 pattern = 1) : d66 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d738 pattern = 1 := by simpa only [d739, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5181 pattern childGuard
    simpa only [d739, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d739, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5182 pattern childGuard
    simpa only [d739, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5184 (pattern : Ten) (guard : d0 pattern = 1) : d71 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5185 (pattern : Ten) (guard : d736 pattern = 1) : d73 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d735 pattern = 1 := by simpa only [d736, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5163 pattern childGuard
    simpa only [d736, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d736, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5184 pattern childGuard
    simpa only [d736, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5186 (pattern : Ten) (guard : d0 pattern = 1) : d74 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5187 (pattern : Ten) (guard : d737 pattern = 1) : d77 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d736 pattern = 1 := by simpa only [d737, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5185 pattern childGuard
    simpa only [d737, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d737, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5186 pattern childGuard
    simpa only [d737, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5188 (pattern : Ten) (guard : d0 pattern = 1) : d78 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5189 (pattern : Ten) (guard : d738 pattern = 1) : d79 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d737 pattern = 1 := by simpa only [d738, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5187 pattern childGuard
    simpa only [d738, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d738, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5188 pattern childGuard
    simpa only [d738, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5190 (pattern : Ten) (guard : d0 pattern = 1) : d80 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5191 (pattern : Ten) (guard : d739 pattern = 1) : d81 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d738 pattern = 1 := by simpa only [d739, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5189 pattern childGuard
    simpa only [d739, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d739, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5190 pattern childGuard
    simpa only [d739, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5192 (pattern : Ten) (guard : d0 pattern = 1) : d7 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5193 (pattern : Ten) (guard : d737 pattern = 1) : d82 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d736 pattern = 1 := by simpa only [d737, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5178 pattern childGuard
    simpa only [d737, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d737, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5192 pattern childGuard
    simpa only [d737, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5194 (pattern : Ten) (guard : d0 pattern = 1) : d58 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5195 (pattern : Ten) (guard : d738 pattern = 1) : d83 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d737 pattern = 1 := by simpa only [d738, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5193 pattern childGuard
    simpa only [d738, d83, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d738, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5194 pattern childGuard
    simpa only [d738, d83, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5196 (pattern : Ten) (guard : d0 pattern = 1) : d84 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5197 (pattern : Ten) (guard : d739 pattern = 1) : d85 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d738 pattern = 1 := by simpa only [d739, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5195 pattern childGuard
    simpa only [d739, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d739, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5196 pattern childGuard
    simpa only [d739, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5198 (pattern : Ten) (guard : d0 pattern = 1) : d87 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5199 (pattern : Ten) (guard : d606 pattern = 1) : d0 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) ≤ (0 : Int) + 6
  decide
theorem c5200 (pattern : Ten) (guard : d607 pattern = 1) : d88 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5199 pattern childGuard
    simpa only [d607, d88, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5160 pattern childGuard
    simpa only [d607, d88, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5201 (pattern : Ten) (guard : d735 pattern = 1) : d93 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d735, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5198 pattern childGuard
    simpa only [d735, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d607 pattern = 1 := by simpa only [d735, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5200 pattern childGuard
    simpa only [d735, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5202 (pattern : Ten) (guard : d0 pattern = 1) : d94 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5203 (pattern : Ten) (guard : d736 pattern = 1) : d99 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d735 pattern = 1 := by simpa only [d736, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5201 pattern childGuard
    simpa only [d736, d99, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d736, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5202 pattern childGuard
    simpa only [d736, d99, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5204 (pattern : Ten) (guard : d0 pattern = 1) : d100 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5205 (pattern : Ten) (guard : d737 pattern = 1) : d103 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d736 pattern = 1 := by simpa only [d737, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5203 pattern childGuard
    simpa only [d737, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d737, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5204 pattern childGuard
    simpa only [d737, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5206 (pattern : Ten) (guard : d0 pattern = 1) : d104 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5207 (pattern : Ten) (guard : d738 pattern = 1) : d105 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d737 pattern = 1 := by simpa only [d738, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5205 pattern childGuard
    simpa only [d738, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d738, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5206 pattern childGuard
    simpa only [d738, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5208 (pattern : Ten) (guard : d0 pattern = 1) : d106 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5209 (pattern : Ten) (guard : d739 pattern = 1) : d107 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d738 pattern = 1 := by simpa only [d739, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5207 pattern childGuard
    simpa only [d739, d107, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d739, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5208 pattern childGuard
    simpa only [d739, d107, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5210 (pattern : Ten) (guard : d0 pattern = 1) : d108 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5211 (pattern : Ten) (guard : d0 pattern = 1) : d2 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5212 (pattern : Ten) (guard : d606 pattern = 1) : d15 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5159 pattern childGuard
    simpa only [d606, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5211 pattern childGuard
    simpa only [d606, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5213 (pattern : Ten) (guard : d607 pattern = 1) : d15 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5212 pattern childGuard
    simpa only [d607, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c630 pattern childGuard
    simpa only [d607, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5214 (pattern : Ten) (guard : d735 pattern = 1) : d109 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d735, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5210 pattern childGuard
    simpa only [d735, d109, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d607 pattern = 1 := by simpa only [d735, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5213 pattern childGuard
    simpa only [d735, d109, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5215 (pattern : Ten) (guard : d0 pattern = 1) : d110 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5216 (pattern : Ten) (guard : d736 pattern = 1) : d115 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d735 pattern = 1 := by simpa only [d736, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5214 pattern childGuard
    simpa only [d736, d115, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d736, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5215 pattern childGuard
    simpa only [d736, d115, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5217 (pattern : Ten) (guard : d0 pattern = 1) : d116 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5218 (pattern : Ten) (guard : d737 pattern = 1) : d119 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d736 pattern = 1 := by simpa only [d737, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5216 pattern childGuard
    simpa only [d737, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d737, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5217 pattern childGuard
    simpa only [d737, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5219 (pattern : Ten) (guard : d0 pattern = 1) : d120 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5220 (pattern : Ten) (guard : d738 pattern = 1) : d121 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d737 pattern = 1 := by simpa only [d738, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5218 pattern childGuard
    simpa only [d738, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d738, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5219 pattern childGuard
    simpa only [d738, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5221 (pattern : Ten) (guard : d0 pattern = 1) : d122 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5222 (pattern : Ten) (guard : d739 pattern = 1) : d123 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d738 pattern = 1 := by simpa only [d739, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5220 pattern childGuard
    simpa only [d739, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d739, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5221 pattern childGuard
    simpa only [d739, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5223 (pattern : Ten) (guard : d607 pattern = 1) : d6 pattern ≤ (0 : Int) + d6 pattern := by
  omega
theorem c5224 (pattern : Ten) (guard : d735 pattern = 1) : d124 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d735, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5172 pattern childGuard
    simpa only [d735, d124, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d607 pattern = 1 := by simpa only [d735, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5223 pattern childGuard
    simpa only [d735, d124, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5225 (pattern : Ten) (guard : d736 pattern = 1) : d125 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d735 pattern = 1 := by simpa only [d736, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5224 pattern childGuard
    simpa only [d736, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d736, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5172 pattern childGuard
    simpa only [d736, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5226 (pattern : Ten) (guard : d737 pattern = 1) : d128 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d736 pattern = 1 := by simpa only [d737, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5225 pattern childGuard
    simpa only [d737, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d737, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5172 pattern childGuard
    simpa only [d737, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5227 (pattern : Ten) (guard : d0 pattern = 1) : d129 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5228 (pattern : Ten) (guard : d738 pattern = 1) : d130 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d737 pattern = 1 := by simpa only [d738, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5226 pattern childGuard
    simpa only [d738, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d738, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5227 pattern childGuard
    simpa only [d738, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5229 (pattern : Ten) (guard : d0 pattern = 1) : d131 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5230 (pattern : Ten) (guard : d739 pattern = 1) : d132 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d738 pattern = 1 := by simpa only [d739, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5228 pattern childGuard
    simpa only [d739, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d739, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5229 pattern childGuard
    simpa only [d739, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5231 (pattern : Ten) (guard : d739 pattern = 1) : d133 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d738 pattern = 1 := by simpa only [d739, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5181 pattern childGuard
    simpa only [d739, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d739, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5192 pattern childGuard
    simpa only [d739, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5232 (pattern : Ten) (guard : d0 pattern = 1) : d8 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5233 (pattern : Ten) (guard : d738 pattern = 1) : d134 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d737 pattern = 1 := by simpa only [d738, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5179 pattern childGuard
    simpa only [d738, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d738, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5232 pattern childGuard
    simpa only [d738, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5234 (pattern : Ten) (guard : d0 pattern = 1) : d56 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5235 (pattern : Ten) (guard : d739 pattern = 1) : d135 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d738 pattern = 1 := by simpa only [d739, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5233 pattern childGuard
    simpa only [d739, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d739, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5234 pattern childGuard
    simpa only [d739, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5236 (pattern : Ten) (guard : d0 pattern = 1) : d139 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5237 (pattern : Ten) (guard : d735 pattern = 1) : d142 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d735, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5236 pattern childGuard
    simpa only [d735, d142, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d607 pattern = 1 := by simpa only [d735, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5162 pattern childGuard
    simpa only [d735, d142, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5238 (pattern : Ten) (guard : d0 pattern = 1) : d143 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5239 (pattern : Ten) (guard : d736 pattern = 1) : d145 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d735 pattern = 1 := by simpa only [d736, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5237 pattern childGuard
    simpa only [d736, d145, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d736, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5238 pattern childGuard
    simpa only [d736, d145, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5240 (pattern : Ten) (guard : d0 pattern = 1) : d146 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5241 (pattern : Ten) (guard : d737 pattern = 1) : d147 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d736 pattern = 1 := by simpa only [d737, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5239 pattern childGuard
    simpa only [d737, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d737, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5240 pattern childGuard
    simpa only [d737, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5242 (pattern : Ten) (guard : d738 pattern = 1) : d148 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d737 pattern = 1 := by simpa only [d738, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5241 pattern childGuard
    simpa only [d738, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d738, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5168 pattern childGuard
    simpa only [d738, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5243 (pattern : Ten) (guard : d739 pattern = 1) : d149 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d738 pattern = 1 := by simpa only [d739, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5242 pattern childGuard
    simpa only [d739, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d739, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5170 pattern childGuard
    simpa only [d739, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5244 (pattern : Ten) (guard : d0 pattern = 1) : d9 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5245 (pattern : Ten) (guard : d736 pattern = 1) : d150 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d735 pattern = 1 := by simpa only [d736, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5176 pattern childGuard
    simpa only [d736, d150, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d736, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5244 pattern childGuard
    simpa only [d736, d150, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5246 (pattern : Ten) (guard : d737 pattern = 1) : d151 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d736 pattern = 1 := by simpa only [d737, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5245 pattern childGuard
    simpa only [d737, d151, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d737, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5177 pattern childGuard
    simpa only [d737, d151, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5247 (pattern : Ten) (guard : d0 pattern = 1) : d152 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5248 (pattern : Ten) (guard : d738 pattern = 1) : d154 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d737 pattern = 1 := by simpa only [d738, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5246 pattern childGuard
    simpa only [d738, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d738, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5247 pattern childGuard
    simpa only [d738, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5249 (pattern : Ten) (guard : d0 pattern = 1) : d155 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5250 (pattern : Ten) (guard : d739 pattern = 1) : d156 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d738 pattern = 1 := by simpa only [d739, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5248 pattern childGuard
    simpa only [d739, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d739, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5249 pattern childGuard
    simpa only [d739, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5251 (pattern : Ten) (guard : d0 pattern = 1) : d55 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5252 (pattern : Ten) (guard : d736 pattern = 1) : d160 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d735 pattern = 1 := by simpa only [d736, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5176 pattern childGuard
    simpa only [d736, d160, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d736, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5251 pattern childGuard
    simpa only [d736, d160, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5253 (pattern : Ten) (guard : d0 pattern = 1) : d161 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5254 (pattern : Ten) (guard : d737 pattern = 1) : d165 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d736 pattern = 1 := by simpa only [d737, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5252 pattern childGuard
    simpa only [d737, d165, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d737, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5253 pattern childGuard
    simpa only [d737, d165, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5255 (pattern : Ten) (guard : d0 pattern = 1) : d166 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5256 (pattern : Ten) (guard : d738 pattern = 1) : d168 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d737 pattern = 1 := by simpa only [d738, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5254 pattern childGuard
    simpa only [d738, d168, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d738, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5255 pattern childGuard
    simpa only [d738, d168, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5257 (pattern : Ten) (guard : d0 pattern = 1) : d169 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5258 (pattern : Ten) (guard : d739 pattern = 1) : d170 pattern ≤ (0 : Int) + d6 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d738 pattern = 1 := by simpa only [d739, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5256 pattern childGuard
    simpa only [d739, d170, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d739, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5257 pattern childGuard
    simpa only [d739, d170, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5259 (pattern : Ten) (guard : d359 pattern = 1) : d0 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) ≤ (0 : Int) + 5
  decide
theorem c5260 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5261 (pattern : Ten) (guard : d606 pattern = 1) : d12 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5259 pattern childGuard
    simpa only [d606, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5260 pattern childGuard
    simpa only [d606, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5262 (pattern : Ten) (guard : d746 pattern = 1) : d17 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d746, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c501 pattern childGuard
    simpa only [d746, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d606 pattern = 1 := by simpa only [d746, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5261 pattern childGuard
    simpa only [d746, d17, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5263 (pattern : Ten) (guard : d0 pattern = 1) : d18 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5264 (pattern : Ten) (guard : d747 pattern = 1) : d23 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d746 pattern = 1 := by simpa only [d747, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5262 pattern childGuard
    simpa only [d747, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d747, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5263 pattern childGuard
    simpa only [d747, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5265 (pattern : Ten) (guard : d0 pattern = 1) : d24 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5266 (pattern : Ten) (guard : d748 pattern = 1) : d29 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d747 pattern = 1 := by simpa only [d748, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5264 pattern childGuard
    simpa only [d748, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d748, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5265 pattern childGuard
    simpa only [d748, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5267 (pattern : Ten) (guard : d0 pattern = 1) : d30 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5268 (pattern : Ten) (guard : d749 pattern = 1) : d33 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d748 pattern = 1 := by simpa only [d749, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5266 pattern childGuard
    simpa only [d749, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d749, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5267 pattern childGuard
    simpa only [d749, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5269 (pattern : Ten) (guard : d0 pattern = 1) : d34 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5270 (pattern : Ten) (guard : d750 pattern = 1) : d35 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d749 pattern = 1 := by simpa only [d750, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5268 pattern childGuard
    simpa only [d750, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d750, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5269 pattern childGuard
    simpa only [d750, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5271 (pattern : Ten) (guard : d0 pattern = 1) : d36 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5272 (pattern : Ten) (guard : d751 pattern = 1) : d37 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d750 pattern = 1 := by simpa only [d751, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5270 pattern childGuard
    simpa only [d751, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d751, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5271 pattern childGuard
    simpa only [d751, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5273 (pattern : Ten) (guard : d0 pattern = 1) : d15 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5274 (pattern : Ten) (guard : d359 pattern = 1) : d4 pattern ≤ (0 : Int) + d5 pattern := by
  change (4 : Int) ≤ (0 : Int) + 5
  decide
theorem c5275 (pattern : Ten) (guard : d606 pattern = 1) : d42 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5274 pattern childGuard
    simpa only [d606, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5260 pattern childGuard
    simpa only [d606, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5276 (pattern : Ten) (guard : d746 pattern = 1) : d48 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d746, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5273 pattern childGuard
    simpa only [d746, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d606 pattern = 1 := by simpa only [d746, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5275 pattern childGuard
    simpa only [d746, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5277 (pattern : Ten) (guard : d0 pattern = 1) : d49 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5278 (pattern : Ten) (guard : d747 pattern = 1) : d54 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d746 pattern = 1 := by simpa only [d747, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5276 pattern childGuard
    simpa only [d747, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d747, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5277 pattern childGuard
    simpa only [d747, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5279 (pattern : Ten) (guard : d0 pattern = 1) : d54 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban41.Diagram
