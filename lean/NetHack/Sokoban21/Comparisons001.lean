/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons000
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c140 (pattern : Twelve) (guard : d1837 pattern = 1) : d81 pattern ≤ (0 : Int) + d266 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d81, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c137 pattern childGuard
    simpa only [d81, d266, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d81, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c139 pattern childGuard
    simpa only [d81, d266, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c141 (pattern : Twelve) (guard : d0 pattern = 1) : d39 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c142 (pattern : Twelve) (guard : d1837 pattern = 1) : d59 pattern ≤ (0 : Int) + d250 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d59, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c135 pattern childGuard
    simpa only [d1837, d59, d250, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d59, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c141 pattern childGuard
    simpa only [d1837, d59, d250, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c143 (pattern : Twelve) (guard : d1 pattern = 1) : d41 pattern ≤ (0 : Int) + d41 pattern := by
  omega
theorem c144 (pattern : Twelve) (guard : d0 pattern = 1) : d42 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c145 (pattern : Twelve) (guard : d1837 pattern = 1) : d61 pattern ≤ (0 : Int) + d251 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d61, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c143 pattern childGuard
    simpa only [d1837, d61, d251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d61, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c144 pattern childGuard
    simpa only [d1837, d61, d251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c146 (pattern : Twelve) (guard : d1837 pattern = 1) : d82 pattern ≤ (0 : Int) + d267 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d82, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c142 pattern childGuard
    simpa only [d82, d267, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d82, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c145 pattern childGuard
    simpa only [d82, d267, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c147 (pattern : Twelve) (guard : d1837 pattern = 1) : d96 pattern ≤ (0 : Int) + d277 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d96, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c140 pattern childGuard
    simpa only [d96, d277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d96, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c146 pattern childGuard
    simpa only [d96, d277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c148 (pattern : Twelve) (guard : d1837 pattern = 1) : d104 pattern ≤ (0 : Int) + d286 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d104, d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c134 pattern childGuard
    simpa only [d104, d286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d104, d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c147 pattern childGuard
    simpa only [d104, d286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c149 (pattern : Twelve) (guard : d0 pattern = 1) : d35 pattern ≤ (0 : Int) + d183 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c150 (pattern : Twelve) (guard : d1837 pattern = 1) : d56 pattern ≤ (0 : Int) + d252 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d56, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1837, d56, d252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d56, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c149 pattern childGuard
    simpa only [d1837, d56, d252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c151 (pattern : Twelve) (guard : d1837 pattern = 1) : d77 pattern ≤ (0 : Int) + d268 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d77, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c150 pattern childGuard
    simpa only [d77, d268, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d77, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c118 pattern childGuard
    simpa only [d77, d268, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c152 (pattern : Twelve) (guard : d1837 pattern = 1) : d94 pattern ≤ (0 : Int) + d278 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d94, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c151 pattern childGuard
    simpa only [d94, d278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d94, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c122 pattern childGuard
    simpa only [d94, d278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c153 (pattern : Twelve) (guard : d1837 pattern = 1) : d6 pattern ≤ (0 : Int) + d6 pattern := by
  omega
theorem c154 (pattern : Twelve) (guard : d1837 pattern = 1) : d105 pattern ≤ (0 : Int) + d287 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d105, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c152 pattern childGuard
    simpa only [d105, d287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d105, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c153 pattern childGuard
    simpa only [d105, d287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c155 (pattern : Twelve) (guard : d1837 pattern = 1) : d111 pattern ≤ (0 : Int) + d294 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d111, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c148 pattern childGuard
    simpa only [d111, d294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d111, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c154 pattern childGuard
    simpa only [d111, d294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c156 (pattern : Twelve) (guard : d1837 pattern = 1) : d114 pattern ≤ (0 : Int) + d297 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d114, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c125 pattern childGuard
    simpa only [d114, d297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d114, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c155 pattern childGuard
    simpa only [d114, d297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c157 (pattern : Twelve) (guard : d0 pattern = 1) : d0 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c158 (pattern : Twelve) (guard : d1837 pattern = 1) : d0 pattern ≤ (0 : Int) + d253 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1837, d253, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c157 pattern childGuard
    simpa only [d1837, d253, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c159 (pattern : Twelve) (guard : d0 pattern = 1) : d27 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c160 (pattern : Twelve) (guard : d1837 pattern = 1) : d50 pattern ≤ (0 : Int) + d254 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d50, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c81 pattern childGuard
    simpa only [d1837, d50, d254, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d50, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c159 pattern childGuard
    simpa only [d1837, d50, d254, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c161 (pattern : Twelve) (guard : d1837 pattern = 1) : d72 pattern ≤ (0 : Int) + d269 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d72, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c158 pattern childGuard
    simpa only [d72, d269, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d72, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c160 pattern childGuard
    simpa only [d72, d269, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c162 (pattern : Twelve) (guard : d0 pattern = 1) : d30 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c163 (pattern : Twelve) (guard : d1837 pattern = 1) : d30 pattern ≤ (0 : Int) + d246 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1837, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c162 pattern childGuard
    simpa only [d1837, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c164 (pattern : Twelve) (guard : d1837 pattern = 1) : d80 pattern ≤ (0 : Int) + d263 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d80, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c163 pattern childGuard
    simpa only [d80, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d80, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c102 pattern childGuard
    simpa only [d80, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c165 (pattern : Twelve) (guard : d1837 pattern = 1) : d97 pattern ≤ (0 : Int) + d279 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d97, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c161 pattern childGuard
    simpa only [d97, d279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d97, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c164 pattern childGuard
    simpa only [d97, d279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c166 (pattern : Twelve) (guard : d0 pattern = 1) : d31 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c167 (pattern : Twelve) (guard : d1837 pattern = 1) : d52 pattern ≤ (0 : Int) + d246 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d52, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1837, d52, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d52, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c166 pattern childGuard
    simpa only [d1837, d52, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c168 (pattern : Twelve) (guard : d0 pattern = 1) : d43 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c169 (pattern : Twelve) (guard : d1837 pattern = 1) : d62 pattern ≤ (0 : Int) + d246 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d62, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1837, d62, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d62, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c168 pattern childGuard
    simpa only [d1837, d62, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c170 (pattern : Twelve) (guard : d1837 pattern = 1) : d83 pattern ≤ (0 : Int) + d246 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c167 pattern childGuard
    simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c169 pattern childGuard
    simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c171 (pattern : Twelve) (guard : d0 pattern = 1) : d44 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c172 (pattern : Twelve) (guard : d1837 pattern = 1) : d63 pattern ≤ (0 : Int) + d246 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d63, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1837, d63, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d63, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c171 pattern childGuard
    simpa only [d1837, d63, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c173 (pattern : Twelve) (guard : d1837 pattern = 1) : d64 pattern ≤ (0 : Int) + d241 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d64, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c100 pattern childGuard
    simpa only [d1837, d64, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d64, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c138 pattern childGuard
    simpa only [d1837, d64, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c174 (pattern : Twelve) (guard : d1837 pattern = 1) : d84 pattern ≤ (0 : Int) + d263 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d84, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c172 pattern childGuard
    simpa only [d84, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d84, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c173 pattern childGuard
    simpa only [d84, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c175 (pattern : Twelve) (guard : d1837 pattern = 1) : d98 pattern ≤ (0 : Int) + d280 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d98, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c170 pattern childGuard
    simpa only [d98, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d98, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c174 pattern childGuard
    simpa only [d98, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c176 (pattern : Twelve) (guard : d1837 pattern = 1) : d106 pattern ≤ (0 : Int) + d288 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d106, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c165 pattern childGuard
    simpa only [d106, d288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d106, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c175 pattern childGuard
    simpa only [d106, d288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c177 (pattern : Twelve) (guard : d0 pattern = 1) : d45 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c178 (pattern : Twelve) (guard : d1837 pattern = 1) : d65 pattern ≤ (0 : Int) + d246 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d65, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1837, d65, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d65, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c177 pattern childGuard
    simpa only [d1837, d65, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c179 (pattern : Twelve) (guard : d1837 pattern = 1) : d85 pattern ≤ (0 : Int) + d246 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c121 pattern childGuard
    simpa only [d85, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c178 pattern childGuard
    simpa only [d85, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c180 (pattern : Twelve) (guard : d1837 pattern = 1) : d66 pattern ≤ (0 : Int) + d246 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d66, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1837, d66, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d66, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c141 pattern childGuard
    simpa only [d1837, d66, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c181 (pattern : Twelve) (guard : d1837 pattern = 1) : d86 pattern ≤ (0 : Int) + d263 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d86, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c180 pattern childGuard
    simpa only [d86, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d86, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c173 pattern childGuard
    simpa only [d86, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c182 (pattern : Twelve) (guard : d1837 pattern = 1) : d99 pattern ≤ (0 : Int) + d280 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d99, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c179 pattern childGuard
    simpa only [d99, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d99, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c181 pattern childGuard
    simpa only [d99, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c183 (pattern : Twelve) (guard : d1837 pattern = 1) : d107 pattern ≤ (0 : Int) + d288 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d107, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c165 pattern childGuard
    simpa only [d107, d288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d107, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c182 pattern childGuard
    simpa only [d107, d288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c184 (pattern : Twelve) (guard : d1837 pattern = 1) : d112 pattern ≤ (0 : Int) + d288 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c176 pattern childGuard
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c183 pattern childGuard
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c185 (pattern : Twelve) (guard : d0 pattern = 1) : d46 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c186 (pattern : Twelve) (guard : d1837 pattern = 1) : d67 pattern ≤ (0 : Int) + d246 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d67, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1837, d67, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d67, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c185 pattern childGuard
    simpa only [d1837, d67, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c187 (pattern : Twelve) (guard : d1837 pattern = 1) : d87 pattern ≤ (0 : Int) + d246 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c163 pattern childGuard
    simpa only [d87, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c186 pattern childGuard
    simpa only [d87, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c188 (pattern : Twelve) (guard : d0 pattern = 1) : d38 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c189 (pattern : Twelve) (guard : d1837 pattern = 1) : d68 pattern ≤ (0 : Int) + d246 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d68, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1837, d68, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d68, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c188 pattern childGuard
    simpa only [d1837, d68, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c190 (pattern : Twelve) (guard : d1837 pattern = 1) : d88 pattern ≤ (0 : Int) + d263 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d88, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c189 pattern childGuard
    simpa only [d88, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d88, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c173 pattern childGuard
    simpa only [d88, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c191 (pattern : Twelve) (guard : d1837 pattern = 1) : d100 pattern ≤ (0 : Int) + d280 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d100, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c187 pattern childGuard
    simpa only [d100, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d100, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c190 pattern childGuard
    simpa only [d100, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c192 (pattern : Twelve) (guard : d0 pattern = 1) : d47 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c193 (pattern : Twelve) (guard : d1837 pattern = 1) : d69 pattern ≤ (0 : Int) + d250 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d69, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c135 pattern childGuard
    simpa only [d1837, d69, d250, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d69, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c192 pattern childGuard
    simpa only [d1837, d69, d250, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c194 (pattern : Twelve) (guard : d1837 pattern = 1) : d89 pattern ≤ (0 : Int) + d250 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c142 pattern childGuard
    simpa only [d89, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c193 pattern childGuard
    simpa only [d89, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c195 (pattern : Twelve) (guard : d0 pattern = 1) : d48 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c196 (pattern : Twelve) (guard : d1837 pattern = 1) : d70 pattern ≤ (0 : Int) + d250 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d70, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c135 pattern childGuard
    simpa only [d1837, d70, d250, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d70, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c195 pattern childGuard
    simpa only [d1837, d70, d250, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c197 (pattern : Twelve) (guard : d0 pattern = 1) : d49 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c198 (pattern : Twelve) (guard : d1837 pattern = 1) : d71 pattern ≤ (0 : Int) + d251 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d71, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c143 pattern childGuard
    simpa only [d1837, d71, d251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d71, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c197 pattern childGuard
    simpa only [d1837, d71, d251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c199 (pattern : Twelve) (guard : d1837 pattern = 1) : d90 pattern ≤ (0 : Int) + d267 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d90, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c196 pattern childGuard
    simpa only [d90, d267, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d90, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c198 pattern childGuard
    simpa only [d90, d267, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c200 (pattern : Twelve) (guard : d1837 pattern = 1) : d101 pattern ≤ (0 : Int) + d281 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d101, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c194 pattern childGuard
    simpa only [d101, d281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d101, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c199 pattern childGuard
    simpa only [d101, d281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c201 (pattern : Twelve) (guard : d1837 pattern = 1) : d108 pattern ≤ (0 : Int) + d289 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d108, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c191 pattern childGuard
    simpa only [d108, d289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d108, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c200 pattern childGuard
    simpa only [d108, d289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c202 (pattern : Twelve) (guard : d1837 pattern = 1) : d109 pattern ≤ (0 : Int) + d290 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d109, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c182 pattern childGuard
    simpa only [d109, d290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d109, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c153 pattern childGuard
    simpa only [d109, d290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c203 (pattern : Twelve) (guard : d1837 pattern = 1) : d113 pattern ≤ (0 : Int) + d295 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d113, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c201 pattern childGuard
    simpa only [d113, d295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d113, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c202 pattern childGuard
    simpa only [d113, d295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c204 (pattern : Twelve) (guard : d1837 pattern = 1) : d115 pattern ≤ (0 : Int) + d298 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d115, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c184 pattern childGuard
    simpa only [d115, d298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d115, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c203 pattern childGuard
    simpa only [d115, d298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c205 (pattern : Twelve) (guard : d1837 pattern = 1) : d116 pattern ≤ (0 : Int) + d300 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d116, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c156 pattern childGuard
    simpa only [d116, d300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d116, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c204 pattern childGuard
    simpa only [d116, d300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c206 (pattern : Twelve) (guard : d1837 pattern = 1) : d51 pattern ≤ (0 : Int) + d255 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d51, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c87 pattern childGuard
    simpa only [d1837, d51, d255, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d51, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c101 pattern childGuard
    simpa only [d1837, d51, d255, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c207 (pattern : Twelve) (guard : d1837 pattern = 1) : d73 pattern ≤ (0 : Int) + d270 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d73, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c158 pattern childGuard
    simpa only [d73, d270, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d73, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c206 pattern childGuard
    simpa only [d73, d270, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c208 (pattern : Twelve) (guard : d1837 pattern = 1) : d91 pattern ≤ (0 : Int) + d282 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d91, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c161 pattern childGuard
    simpa only [d91, d282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d91, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c207 pattern childGuard
    simpa only [d91, d282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c209 (pattern : Twelve) (guard : d0 pattern = 1) : d32 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c210 (pattern : Twelve) (guard : d1837 pattern = 1) : d53 pattern ≤ (0 : Int) + d246 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d53, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1837, d53, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d53, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c209 pattern childGuard
    simpa only [d1837, d53, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c211 (pattern : Twelve) (guard : d1837 pattern = 1) : d74 pattern ≤ (0 : Int) + d246 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c167 pattern childGuard
    simpa only [d74, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c210 pattern childGuard
    simpa only [d74, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c212 (pattern : Twelve) (guard : d0 pattern = 1) : d33 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c213 (pattern : Twelve) (guard : d1837 pattern = 1) : d54 pattern ≤ (0 : Int) + d246 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d54, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1837, d54, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d54, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c212 pattern childGuard
    simpa only [d1837, d54, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c214 (pattern : Twelve) (guard : d1837 pattern = 1) : d75 pattern ≤ (0 : Int) + d263 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d75, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c213 pattern childGuard
    simpa only [d75, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d75, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c102 pattern childGuard
    simpa only [d75, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c215 (pattern : Twelve) (guard : d1837 pattern = 1) : d92 pattern ≤ (0 : Int) + d280 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d92, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c211 pattern childGuard
    simpa only [d92, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d92, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c214 pattern childGuard
    simpa only [d92, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c216 (pattern : Twelve) (guard : d1837 pattern = 1) : d102 pattern ≤ (0 : Int) + d291 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d102, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c208 pattern childGuard
    simpa only [d102, d291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d102, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c215 pattern childGuard
    simpa only [d102, d291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c217 (pattern : Twelve) (guard : d1837 pattern = 1) : d76 pattern ≤ (0 : Int) + d271 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d76, d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c158 pattern childGuard
    simpa only [d76, d271, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d76, d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c102 pattern childGuard
    simpa only [d76, d271, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c218 (pattern : Twelve) (guard : d1837 pattern = 1) : d93 pattern ≤ (0 : Int) + d283 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d93, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c161 pattern childGuard
    simpa only [d93, d283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d93, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c217 pattern childGuard
    simpa only [d93, d283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c219 (pattern : Twelve) (guard : d1837 pattern = 1) : d77 pattern ≤ (0 : Int) + d246 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c121 pattern childGuard
    simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c118 pattern childGuard
    simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c220 (pattern : Twelve) (guard : d1837 pattern = 1) : d94 pattern ≤ (0 : Int) + d280 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d94, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c219 pattern childGuard
    simpa only [d94, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d94, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c122 pattern childGuard
    simpa only [d94, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c221 (pattern : Twelve) (guard : d1837 pattern = 1) : d103 pattern ≤ (0 : Int) + d292 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d103, d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c218 pattern childGuard
    simpa only [d103, d292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d103, d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c220 pattern childGuard
    simpa only [d103, d292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c222 (pattern : Twelve) (guard : d1837 pattern = 1) : d110 pattern ≤ (0 : Int) + d296 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d110, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c216 pattern childGuard
    simpa only [d110, d296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d110, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c221 pattern childGuard
    simpa only [d110, d296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c223 (pattern : Twelve) (guard : d0 pattern = 1) : d37 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c224 (pattern : Twelve) (guard : d1837 pattern = 1) : d58 pattern ≤ (0 : Int) + d246 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d58, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1837, d58, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d58, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c223 pattern childGuard
    simpa only [d1837, d58, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c225 (pattern : Twelve) (guard : d1837 pattern = 1) : d79 pattern ≤ (0 : Int) + d246 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c163 pattern childGuard
    simpa only [d79, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c224 pattern childGuard
    simpa only [d79, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c226 (pattern : Twelve) (guard : d1837 pattern = 1) : d95 pattern ≤ (0 : Int) + d280 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d95, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c225 pattern childGuard
    simpa only [d95, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d95, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c164 pattern childGuard
    simpa only [d95, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c227 (pattern : Twelve) (guard : d1837 pattern = 1) : d81 pattern ≤ (0 : Int) + d250 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c142 pattern childGuard
    simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c139 pattern childGuard
    simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c228 (pattern : Twelve) (guard : d1837 pattern = 1) : d96 pattern ≤ (0 : Int) + d281 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d96, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c227 pattern childGuard
    simpa only [d96, d281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d96, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c146 pattern childGuard
    simpa only [d96, d281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c229 (pattern : Twelve) (guard : d1837 pattern = 1) : d104 pattern ≤ (0 : Int) + d289 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d104, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c226 pattern childGuard
    simpa only [d104, d289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d104, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c228 pattern childGuard
    simpa only [d104, d289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c230 (pattern : Twelve) (guard : d1837 pattern = 1) : d105 pattern ≤ (0 : Int) + d290 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d105, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c220 pattern childGuard
    simpa only [d105, d290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d105, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c153 pattern childGuard
    simpa only [d105, d290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c231 (pattern : Twelve) (guard : d1837 pattern = 1) : d111 pattern ≤ (0 : Int) + d295 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d111, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c229 pattern childGuard
    simpa only [d111, d295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d111, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c230 pattern childGuard
    simpa only [d111, d295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c232 (pattern : Twelve) (guard : d1837 pattern = 1) : d114 pattern ≤ (0 : Int) + d299 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d114, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c222 pattern childGuard
    simpa only [d114, d299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d114, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c231 pattern childGuard
    simpa only [d114, d299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c233 (pattern : Twelve) (guard : d1837 pattern = 1) : d116 pattern ≤ (0 : Int) + d301 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d116, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c232 pattern childGuard
    simpa only [d116, d301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d116, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c204 pattern childGuard
    simpa only [d116, d301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c234 (pattern : Twelve) (guard : d1837 pattern = 1) : d116 pattern ≤ (0 : Int) + d302 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c205 pattern childGuard
    simpa only [d302, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c233 pattern childGuard
    simpa only [d302, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c235 (pattern : Twelve) (guard : d1837 pattern = 1) : d116 pattern ≤ (0 : Int) + d303 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c234 pattern childGuard
    simpa only [d303, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c233 pattern childGuard
    simpa only [d303, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c236 (pattern : Twelve) (guard : d1 pattern = 1) : d27 pattern ≤ (0 : Int) + d27 pattern := by
  omega
theorem c237 (pattern : Twelve) (guard : d0 pattern = 1) : d816 pattern ≤ (0 : Int) + d173 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c238 (pattern : Twelve) (guard : d1837 pattern = 1) : d824 pattern ≤ (0 : Int) + d940 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d824, d940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c236 pattern childGuard
    simpa only [d1837, d824, d940, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d824, d940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c237 pattern childGuard
    simpa only [d1837, d824, d940, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c239 (pattern : Twelve) (guard : d1837 pattern = 1) : d838 pattern ≤ (0 : Int) + d947 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d838, d947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c86 pattern childGuard
    simpa only [d838, d947, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d838, d947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c238 pattern childGuard
    simpa only [d838, d947, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c240 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (0 : Int) + d17 pattern := by
  omega
theorem c241 (pattern : Twelve) (guard : d0 pattern = 1) : d17 pattern ≤ (0 : Int) + d173 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c242 (pattern : Twelve) (guard : d1837 pattern = 1) : d17 pattern ≤ (0 : Int) + d941 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1837, d941, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c241 pattern childGuard
    simpa only [d1837, d941, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c243 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (0 : Int) + d817 pattern := by
  omega
theorem c244 (pattern : Twelve) (guard : d1837 pattern = 1) : d825 pattern ≤ (0 : Int) + d942 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d825, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c243 pattern childGuard
    simpa only [d1837, d825, d942, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d825, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c144 pattern childGuard
    simpa only [d1837, d825, d942, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c245 (pattern : Twelve) (guard : d1837 pattern = 1) : d839 pattern ≤ (0 : Int) + d948 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d839, d948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c242 pattern childGuard
    simpa only [d839, d948, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d839, d948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c244 pattern childGuard
    simpa only [d839, d948, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c246 (pattern : Twelve) (guard : d1837 pattern = 1) : d853 pattern ≤ (0 : Int) + d955 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d853, d955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c239 pattern childGuard
    simpa only [d853, d955, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d853, d955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c245 pattern childGuard
    simpa only [d853, d955, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c247 (pattern : Twelve) (guard : d0 pattern = 1) : d35 pattern ≤ (0 : Int) + d176 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c248 (pattern : Twelve) (guard : d1837 pattern = 1) : d56 pattern ≤ (0 : Int) + d240 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d56, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1837, d56, d240, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d56, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c247 pattern childGuard
    simpa only [d1837, d56, d240, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c249 (pattern : Twelve) (guard : d0 pattern = 1) : d818 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c250 (pattern : Twelve) (guard : d1837 pattern = 1) : d826 pattern ≤ (0 : Int) + d241 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d826, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c100 pattern childGuard
    simpa only [d1837, d826, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d826, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c249 pattern childGuard
    simpa only [d1837, d826, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c251 (pattern : Twelve) (guard : d1837 pattern = 1) : d840 pattern ≤ (0 : Int) + d259 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d840, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c248 pattern childGuard
    simpa only [d840, d259, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d840, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c250 pattern childGuard
    simpa only [d840, d259, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c252 (pattern : Twelve) (guard : d1837 pattern = 1) : d827 pattern ≤ (0 : Int) + d241 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d827, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c100 pattern childGuard
    simpa only [d1837, d827, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d827, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c117 pattern childGuard
    simpa only [d1837, d827, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c253 (pattern : Twelve) (guard : d1837 pattern = 1) : d841 pattern ≤ (0 : Int) + d949 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d841, d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c252 pattern childGuard
    simpa only [d841, d949, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d841, d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c244 pattern childGuard
    simpa only [d841, d949, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c254 (pattern : Twelve) (guard : d1837 pattern = 1) : d854 pattern ≤ (0 : Int) + d956 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d854, d956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c251 pattern childGuard
    simpa only [d854, d956, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d854, d956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c253 pattern childGuard
    simpa only [d854, d956, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c255 (pattern : Twelve) (guard : d1837 pattern = 1) : d861 pattern ≤ (0 : Int) + d963 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d861, d963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c246 pattern childGuard
    simpa only [d861, d963, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d861, d963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c254 pattern childGuard
    simpa only [d861, d963, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c256 (pattern : Twelve) (guard : d0 pattern = 1) : d816 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c257 (pattern : Twelve) (guard : d1837 pattern = 1) : d824 pattern ≤ (0 : Int) + d943 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d824, d943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c236 pattern childGuard
    simpa only [d1837, d824, d943, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d824, d943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c256 pattern childGuard
    simpa only [d1837, d824, d943, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c258 (pattern : Twelve) (guard : d1837 pattern = 1) : d838 pattern ≤ (0 : Int) + d950 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d838, d950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c112 pattern childGuard
    simpa only [d838, d950, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d838, d950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c257 pattern childGuard
    simpa only [d838, d950, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c259 (pattern : Twelve) (guard : d0 pattern = 1) : d17 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c260 (pattern : Twelve) (guard : d1837 pattern = 1) : d17 pattern ≤ (0 : Int) + d944 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1837, d944, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c259 pattern childGuard
    simpa only [d1837, d944, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c261 (pattern : Twelve) (guard : d1837 pattern = 1) : d839 pattern ≤ (0 : Int) + d951 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d839, d951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c260 pattern childGuard
    simpa only [d839, d951, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d839, d951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c244 pattern childGuard
    simpa only [d839, d951, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c262 (pattern : Twelve) (guard : d1837 pattern = 1) : d853 pattern ≤ (0 : Int) + d957 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d853, d957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c258 pattern childGuard
    simpa only [d853, d957, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d853, d957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c261 pattern childGuard
    simpa only [d853, d957, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c263 (pattern : Twelve) (guard : d1837 pattern = 1) : d840 pattern ≤ (0 : Int) + d263 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d840, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c121 pattern childGuard
    simpa only [d840, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d840, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c250 pattern childGuard
    simpa only [d840, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c264 (pattern : Twelve) (guard : d1837 pattern = 1) : d854 pattern ≤ (0 : Int) + d958 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d854, d958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c263 pattern childGuard
    simpa only [d854, d958, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d854, d958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c253 pattern childGuard
    simpa only [d854, d958, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c265 (pattern : Twelve) (guard : d1837 pattern = 1) : d861 pattern ≤ (0 : Int) + d964 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d861, d964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c262 pattern childGuard
    simpa only [d861, d964, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d861, d964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c264 pattern childGuard
    simpa only [d861, d964, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c266 (pattern : Twelve) (guard : d1837 pattern = 1) : d861 pattern ≤ (0 : Int) + d970 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c255 pattern childGuard
    simpa only [d970, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c265 pattern childGuard
    simpa only [d970, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c267 (pattern : Twelve) (guard : d0 pattern = 1) : d819 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c268 (pattern : Twelve) (guard : d1837 pattern = 1) : d828 pattern ≤ (0 : Int) + d241 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d828, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c100 pattern childGuard
    simpa only [d1837, d828, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d828, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c267 pattern childGuard
    simpa only [d1837, d828, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c269 (pattern : Twelve) (guard : d1837 pattern = 1) : d842 pattern ≤ (0 : Int) + d265 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d842, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c132 pattern childGuard
    simpa only [d842, d265, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d842, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c268 pattern childGuard
    simpa only [d842, d265, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c270 (pattern : Twelve) (guard : d0 pattern = 1) : d34 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c271 (pattern : Twelve) (guard : d1837 pattern = 1) : d34 pattern ≤ (0 : Int) + d241 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c100 pattern childGuard
    simpa only [d1837, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c270 pattern childGuard
    simpa only [d1837, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c272 (pattern : Twelve) (guard : d1837 pattern = 1) : d843 pattern ≤ (0 : Int) + d949 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d843, d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c271 pattern childGuard
    simpa only [d843, d949, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d843, d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c244 pattern childGuard
    simpa only [d843, d949, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c273 (pattern : Twelve) (guard : d1837 pattern = 1) : d855 pattern ≤ (0 : Int) + d959 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d855, d959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c269 pattern childGuard
    simpa only [d855, d959, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d855, d959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c272 pattern childGuard
    simpa only [d855, d959, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c274 (pattern : Twelve) (guard : d0 pattern = 1) : d820 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c275 (pattern : Twelve) (guard : d1837 pattern = 1) : d829 pattern ≤ (0 : Int) + d251 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d829, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c143 pattern childGuard
    simpa only [d1837, d829, d251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d829, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c274 pattern childGuard
    simpa only [d1837, d829, d251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c276 (pattern : Twelve) (guard : d1837 pattern = 1) : d844 pattern ≤ (0 : Int) + d267 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d844, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c142 pattern childGuard
    simpa only [d844, d267, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d844, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c275 pattern childGuard
    simpa only [d844, d267, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c277 (pattern : Twelve) (guard : d1837 pattern = 1) : d830 pattern ≤ (0 : Int) + d251 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d830, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c143 pattern childGuard
    simpa only [d1837, d830, d251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d830, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c138 pattern childGuard
    simpa only [d1837, d830, d251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c278 (pattern : Twelve) (guard : d1 pattern = 1) : d821 pattern ≤ (0 : Int) + d821 pattern := by
  omega
theorem c279 (pattern : Twelve) (guard : d0 pattern = 1) : d822 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban21.Diagram
