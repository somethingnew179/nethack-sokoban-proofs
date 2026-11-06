/- Staged soko4-1 certificate. No result until all kernel checks pass. -/
import NetHack.Sokoban41.Comparisons00
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem c160 (pattern : Ten) (guard : d359 pattern = 1) : d9 pattern ≤ (0 : Int) + d11 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c159 pattern childGuard
    simpa only [d359, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c111 pattern childGuard
    simpa only [d359, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c161 (pattern : Ten) (guard : d359 pattern = 1) : d67 pattern ≤ (0 : Int) + d13 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d67, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c157 pattern childGuard
    simpa only [d67, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d359 pattern = 1 := by simpa only [d67, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c160 pattern childGuard
    simpa only [d67, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c162 (pattern : Ten) (guard : d359 pattern = 1) : d10 pattern ≤ (0 : Int) + d10 pattern := by
  omega
theorem c163 (pattern : Ten) (guard : d359 pattern = 1) : d68 pattern ≤ (0 : Int) + d14 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d68, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c160 pattern childGuard
    simpa only [d68, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d359 pattern = 1 := by simpa only [d68, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c162 pattern childGuard
    simpa only [d68, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c164 (pattern : Ten) (guard : d359 pattern = 1) : d69 pattern ≤ (0 : Int) + d19 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d69, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c161 pattern childGuard
    simpa only [d69, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d359 pattern = 1 := by simpa only [d69, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c163 pattern childGuard
    simpa only [d69, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c165 (pattern : Ten) (guard : d359 pattern = 1) : d70 pattern ≤ (0 : Int) + d20 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d70, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c163 pattern childGuard
    simpa only [d70, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d359 pattern = 1 := by simpa only [d70, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c162 pattern childGuard
    simpa only [d70, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c166 (pattern : Ten) (guard : d359 pattern = 1) : d71 pattern ≤ (0 : Int) + d24 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d71, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c164 pattern childGuard
    simpa only [d71, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d359 pattern = 1 := by simpa only [d71, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c165 pattern childGuard
    simpa only [d71, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c167 (pattern : Ten) (guard : d359 pattern = 1) : d73 pattern ≤ (0 : Int) + d29 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d73, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c156 pattern childGuard
    simpa only [d73, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d359 pattern = 1 := by simpa only [d73, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c166 pattern childGuard
    simpa only [d73, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c168 (pattern : Ten) (guard : d359 pattern = 1) : d25 pattern ≤ (0 : Int) + d25 pattern := by
  omega
theorem c169 (pattern : Ten) (guard : d359 pattern = 1) : d74 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d74, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c168 pattern childGuard
    simpa only [d74, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d359 pattern = 1 := by simpa only [d74, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c166 pattern childGuard
    simpa only [d74, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c170 (pattern : Ten) (guard : d359 pattern = 1) : d77 pattern ≤ (0 : Int) + d33 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d77, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c167 pattern childGuard
    simpa only [d77, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d359 pattern = 1 := by simpa only [d77, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c169 pattern childGuard
    simpa only [d77, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c171 (pattern : Ten) (guard : d359 pattern = 1) : d26 pattern ≤ (0 : Int) + d26 pattern := by
  omega
theorem c172 (pattern : Ten) (guard : d359 pattern = 1) : d72 pattern ≤ (0 : Int) + d27 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d72, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c165 pattern childGuard
    simpa only [d72, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d359 pattern = 1 := by simpa only [d72, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c162 pattern childGuard
    simpa only [d72, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c173 (pattern : Ten) (guard : d359 pattern = 1) : d75 pattern ≤ (0 : Int) + d31 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d75, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c171 pattern childGuard
    simpa only [d75, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d359 pattern = 1 := by simpa only [d75, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c172 pattern childGuard
    simpa only [d75, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c174 (pattern : Ten) (guard : d359 pattern = 1) : d28 pattern ≤ (0 : Int) + d28 pattern := by
  omega
theorem c175 (pattern : Ten) (guard : d359 pattern = 1) : d76 pattern ≤ (0 : Int) + d32 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d76, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c174 pattern childGuard
    simpa only [d76, d32, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d359 pattern = 1 := by simpa only [d76, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c172 pattern childGuard
    simpa only [d76, d32, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c176 (pattern : Ten) (guard : d359 pattern = 1) : d78 pattern ≤ (0 : Int) + d34 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d78, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c173 pattern childGuard
    simpa only [d78, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d359 pattern = 1 := by simpa only [d78, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c175 pattern childGuard
    simpa only [d78, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c177 (pattern : Ten) (guard : d359 pattern = 1) : d79 pattern ≤ (0 : Int) + d35 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d79, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c170 pattern childGuard
    simpa only [d79, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d359 pattern = 1 := by simpa only [d79, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c176 pattern childGuard
    simpa only [d79, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c178 (pattern : Ten) (guard : d359 pattern = 1) : d80 pattern ≤ (0 : Int) + d36 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d80, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c176 pattern childGuard
    simpa only [d80, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d359 pattern = 1 := by simpa only [d80, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c162 pattern childGuard
    simpa only [d80, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c179 (pattern : Ten) (guard : d359 pattern = 1) : d81 pattern ≤ (0 : Int) + d37 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d81, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c177 pattern childGuard
    simpa only [d81, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d359 pattern = 1 := by simpa only [d81, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c178 pattern childGuard
    simpa only [d81, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c180 (pattern : Ten) (guard : d358 pattern = 1) : d221 pattern ≤ (0 : Int) + d240 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d356 pattern = 1 := by simpa only [d358, d221, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c91 pattern childGuard
    simpa only [d358, d221, d240, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d358, d221, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c128 pattern childGuard
    simpa only [d358, d221, d240, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c181 (pattern : Ten) (guard : d356 pattern = 1) : d0 pattern ≤ (0 : Int) + d0 pattern := by
  omega
theorem c182 (pattern : Ten) (guard : d358 pattern = 1) : d0 pattern ≤ (0 : Int) + d171 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d356 pattern = 1 := by simpa only [d358, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c181 pattern childGuard
    simpa only [d358, d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d358, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c130 pattern childGuard
    simpa only [d358, d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c183 (pattern : Ten) (guard : d358 pattern = 1) : d222 pattern ≤ (0 : Int) + d241 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d222, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c180 pattern childGuard
    simpa only [d222, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d222, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c182 pattern childGuard
    simpa only [d222, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c184 (pattern : Ten) (guard : d358 pattern = 1) : d223 pattern ≤ (0 : Int) + d242 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d223, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c183 pattern childGuard
    simpa only [d223, d242, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d223, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c182 pattern childGuard
    simpa only [d223, d242, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c185 (pattern : Ten) (guard : d358 pattern = 1) : d10 pattern ≤ (0 : Int) + d10 pattern := by
  omega
theorem c186 (pattern : Ten) (guard : d358 pattern = 1) : d12 pattern ≤ (0 : Int) + d173 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d12, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c182 pattern childGuard
    simpa only [d12, d173, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d12, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c185 pattern childGuard
    simpa only [d12, d173, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c187 (pattern : Ten) (guard : d358 pattern = 1) : d224 pattern ≤ (0 : Int) + d243 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d224, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c184 pattern childGuard
    simpa only [d224, d243, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d224, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c186 pattern childGuard
    simpa only [d224, d243, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c188 (pattern : Ten) (guard : d358 pattern = 1) : d18 pattern ≤ (0 : Int) + d177 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d18, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c186 pattern childGuard
    simpa only [d18, d177, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d18, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c185 pattern childGuard
    simpa only [d18, d177, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c189 (pattern : Ten) (guard : d358 pattern = 1) : d225 pattern ≤ (0 : Int) + d244 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d225, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c187 pattern childGuard
    simpa only [d225, d244, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d225, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c188 pattern childGuard
    simpa only [d225, d244, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c190 (pattern : Ten) (guard : d358 pattern = 1) : d26 pattern ≤ (0 : Int) + d181 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d26, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c188 pattern childGuard
    simpa only [d26, d181, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d26, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c185 pattern childGuard
    simpa only [d26, d181, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c191 (pattern : Ten) (guard : d358 pattern = 1) : d226 pattern ≤ (0 : Int) + d245 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d226, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c189 pattern childGuard
    simpa only [d226, d245, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d226, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c190 pattern childGuard
    simpa only [d226, d245, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c192 (pattern : Ten) (guard : d356 pattern = 1) : d2 pattern ≤ (0 : Int) + d2 pattern := by
  omega
theorem c193 (pattern : Ten) (guard : d358 pattern = 1) : d2 pattern ≤ (0 : Int) + d172 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d356 pattern = 1 := by simpa only [d358, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c192 pattern childGuard
    simpa only [d358, d172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d358, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c140 pattern childGuard
    simpa only [d358, d172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c194 (pattern : Ten) (guard : d358 pattern = 1) : d15 pattern ≤ (0 : Int) + d174 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c182 pattern childGuard
    simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c193 pattern childGuard
    simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c195 (pattern : Ten) (guard : d358 pattern = 1) : d16 pattern ≤ (0 : Int) + d175 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d16, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c193 pattern childGuard
    simpa only [d16, d175, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d16, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c185 pattern childGuard
    simpa only [d16, d175, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c196 (pattern : Ten) (guard : d358 pattern = 1) : d21 pattern ≤ (0 : Int) + d178 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d21, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c194 pattern childGuard
    simpa only [d21, d178, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d21, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c195 pattern childGuard
    simpa only [d21, d178, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c197 (pattern : Ten) (guard : d358 pattern = 1) : d22 pattern ≤ (0 : Int) + d179 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d22, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c195 pattern childGuard
    simpa only [d22, d179, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d22, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c185 pattern childGuard
    simpa only [d22, d179, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c198 (pattern : Ten) (guard : d358 pattern = 1) : d25 pattern ≤ (0 : Int) + d182 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d25, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c196 pattern childGuard
    simpa only [d25, d182, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d25, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c197 pattern childGuard
    simpa only [d25, d182, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c199 (pattern : Ten) (guard : d358 pattern = 1) : d227 pattern ≤ (0 : Int) + d185 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d227, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c198 pattern childGuard
    simpa only [d227, d185, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d227, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c190 pattern childGuard
    simpa only [d227, d185, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c200 (pattern : Ten) (guard : d358 pattern = 1) : d230 pattern ≤ (0 : Int) + d246 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d230, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c191 pattern childGuard
    simpa only [d230, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d230, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c199 pattern childGuard
    simpa only [d230, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c201 (pattern : Ten) (guard : d358 pattern = 1) : d228 pattern ≤ (0 : Int) + d186 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d228, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c190 pattern childGuard
    simpa only [d228, d186, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d228, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c185 pattern childGuard
    simpa only [d228, d186, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c202 (pattern : Ten) (guard : d358 pattern = 1) : d28 pattern ≤ (0 : Int) + d183 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d28, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c197 pattern childGuard
    simpa only [d28, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d28, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c185 pattern childGuard
    simpa only [d28, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c203 (pattern : Ten) (guard : d358 pattern = 1) : d229 pattern ≤ (0 : Int) + d187 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d229, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c202 pattern childGuard
    simpa only [d229, d187, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d229, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c185 pattern childGuard
    simpa only [d229, d187, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c204 (pattern : Ten) (guard : d358 pattern = 1) : d231 pattern ≤ (0 : Int) + d189 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d231, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c201 pattern childGuard
    simpa only [d231, d189, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d231, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c203 pattern childGuard
    simpa only [d231, d189, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c205 (pattern : Ten) (guard : d358 pattern = 1) : d232 pattern ≤ (0 : Int) + d247 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d232, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c200 pattern childGuard
    simpa only [d232, d247, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d232, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c204 pattern childGuard
    simpa only [d232, d247, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c206 (pattern : Ten) (guard : d358 pattern = 1) : d233 pattern ≤ (0 : Int) + d191 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d233, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c204 pattern childGuard
    simpa only [d233, d191, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d233, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c185 pattern childGuard
    simpa only [d233, d191, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c207 (pattern : Ten) (guard : d358 pattern = 1) : d234 pattern ≤ (0 : Int) + d248 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d358 pattern = 1 := by simpa only [d234, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c205 pattern childGuard
    simpa only [d234, d248, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d358 pattern = 1 := by simpa only [d234, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c206 pattern childGuard
    simpa only [d234, d248, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c208 (pattern : Ten) (guard : d350 pattern = 1) : d64 pattern ≤ (0 : Int) + d64 pattern := by
  omega
theorem c209 (pattern : Ten) (guard : d0 pattern = 1) : d65 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c210 (pattern : Ten) (guard : d362 pattern = 1) : d66 pattern ≤ (0 : Int) + d133 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d362, d66, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c208 pattern childGuard
    simpa only [d362, d66, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d362, d66, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c209 pattern childGuard
    simpa only [d362, d66, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c211 (pattern : Ten) (guard : d1 pattern = 1) : d218 pattern ≤ (0 : Int) + d218 pattern := by
  omega
theorem c212 (pattern : Ten) (guard : d0 pattern = 1) : d219 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c213 (pattern : Ten) (guard : d361 pattern = 1) : d220 pattern ≤ (0 : Int) + d289 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d361, d220, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c211 pattern childGuard
    simpa only [d361, d220, d289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d361, d220, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c212 pattern childGuard
    simpa only [d361, d220, d289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c214 (pattern : Ten) (guard : d0 pattern = 1) : d62 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c215 (pattern : Ten) (guard : d367 pattern = 1) : d64 pattern ≤ (0 : Int) + d134 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d367, d64, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c61 pattern childGuard
    simpa only [d367, d64, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d367, d64, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c214 pattern childGuard
    simpa only [d367, d64, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c216 (pattern : Ten) (guard : d0 pattern = 1) : d63 pattern ≤ (0 : Int) + d56 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c217 (pattern : Ten) (guard : d368 pattern = 1) : d65 pattern ≤ (0 : Int) + d56 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d354 pattern = 1 := by simpa only [d368, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c68 pattern childGuard
    simpa only [d368, d65, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d368, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c216 pattern childGuard
    simpa only [d368, d65, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c218 (pattern : Ten) (guard : d369 pattern = 1) : d66 pattern ≤ (0 : Int) + d135 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d367 pattern = 1 := by simpa only [d369, d66, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c215 pattern childGuard
    simpa only [d369, d66, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d368 pattern = 1 := by simpa only [d369, d66, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c217 pattern childGuard
    simpa only [d369, d66, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c219 (pattern : Ten) (guard : d0 pattern = 1) : d215 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c220 (pattern : Ten) (guard : d366 pattern = 1) : d218 pattern ≤ (0 : Int) + d290 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d366, d218, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c74 pattern childGuard
    simpa only [d366, d218, d290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d366, d218, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c219 pattern childGuard
    simpa only [d366, d218, d290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c221 (pattern : Ten) (guard : d0 pattern = 1) : d217 pattern ≤ (0 : Int) + d209 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c222 (pattern : Ten) (guard : d370 pattern = 1) : d219 pattern ≤ (0 : Int) + d209 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d353 pattern = 1 := by simpa only [d370, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c83 pattern childGuard
    simpa only [d370, d219, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d370, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c221 pattern childGuard
    simpa only [d370, d219, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c223 (pattern : Ten) (guard : d371 pattern = 1) : d220 pattern ≤ (0 : Int) + d291 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d366 pattern = 1 := by simpa only [d371, d220, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c220 pattern childGuard
    simpa only [d371, d220, d291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d370 pattern = 1 := by simpa only [d371, d220, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c222 pattern childGuard
    simpa only [d371, d220, d291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c224 (pattern : Ten) (guard : d350 pattern = 1) : d48 pattern ≤ (0 : Int) + d48 pattern := by
  omega
theorem c225 (pattern : Ten) (guard : d0 pattern = 1) : d49 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c226 (pattern : Ten) (guard : d373 pattern = 1) : d54 pattern ≤ (0 : Int) + d124 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d373, d54, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c224 pattern childGuard
    simpa only [d373, d54, d124, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d373, d54, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c225 pattern childGuard
    simpa only [d373, d54, d124, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c227 (pattern : Ten) (guard : d0 pattern = 1) : d49 pattern ≤ (0 : Int) + d48 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c228 (pattern : Ten) (guard : d373 pattern = 1) : d54 pattern ≤ (0 : Int) + d48 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d373, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c224 pattern childGuard
    simpa only [d373, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d373, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c227 pattern childGuard
    simpa only [d373, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c229 (pattern : Ten) (guard : d373 pattern = 1) : d54 pattern ≤ (0 : Int) + d125 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d373 pattern = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c226 pattern childGuard
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d373 pattern = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c228 pattern childGuard
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c230 (pattern : Ten) (guard : d373 pattern = 1) : d54 pattern ≤ (0 : Int) + d128 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d373 pattern = 1 := by simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c229 pattern childGuard
    simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d373 pattern = 1 := by simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c228 pattern childGuard
    simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c231 (pattern : Ten) (guard : d350 pattern = 1) : d20 pattern ≤ (0 : Int) + d20 pattern := by
  omega
theorem c232 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d20 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c233 (pattern : Ten) (guard : d373 pattern = 1) : d27 pattern ≤ (0 : Int) + d20 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d373, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c231 pattern childGuard
    simpa only [d373, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d373, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c232 pattern childGuard
    simpa only [d373, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c234 (pattern : Ten) (guard : d373 pattern = 1) : d58 pattern ≤ (0 : Int) + d126 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d373 pattern = 1 := by simpa only [d58, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c228 pattern childGuard
    simpa only [d58, d126, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d373 pattern = 1 := by simpa only [d58, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c233 pattern childGuard
    simpa only [d58, d126, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c235 (pattern : Ten) (guard : d350 pattern = 1) : d50 pattern ≤ (0 : Int) + d50 pattern := by
  omega
theorem c236 (pattern : Ten) (guard : d0 pattern = 1) : d51 pattern ≤ (0 : Int) + d50 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c237 (pattern : Ten) (guard : d373 pattern = 1) : d55 pattern ≤ (0 : Int) + d50 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d373, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c235 pattern childGuard
    simpa only [d373, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d373, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c236 pattern childGuard
    simpa only [d373, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c238 (pattern : Ten) (guard : d373 pattern = 1) : d59 pattern ≤ (0 : Int) + d127 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d373 pattern = 1 := by simpa only [d59, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c237 pattern childGuard
    simpa only [d59, d127, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d373 pattern = 1 := by simpa only [d59, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c233 pattern childGuard
    simpa only [d59, d127, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c239 (pattern : Ten) (guard : d373 pattern = 1) : d62 pattern ≤ (0 : Int) + d129 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d373 pattern = 1 := by simpa only [d62, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c234 pattern childGuard
    simpa only [d62, d129, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d373 pattern = 1 := by simpa only [d62, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c238 pattern childGuard
    simpa only [d62, d129, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c240 (pattern : Ten) (guard : d373 pattern = 1) : d64 pattern ≤ (0 : Int) + d130 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d373 pattern = 1 := by simpa only [d64, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c230 pattern childGuard
    simpa only [d64, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d373 pattern = 1 := by simpa only [d64, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c239 pattern childGuard
    simpa only [d64, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c241 (pattern : Ten) (guard : d0 pattern = 1) : d65 pattern ≤ (0 : Int) + d131 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c242 (pattern : Ten) (guard : d374 pattern = 1) : d66 pattern ≤ (0 : Int) + d132 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d373 pattern = 1 := by simpa only [d374, d66, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d374, d66, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d374, d66, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c241 pattern childGuard
    simpa only [d374, d66, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c243 (pattern : Ten) (guard : d1 pattern = 1) : d202 pattern ≤ (0 : Int) + d202 pattern := by
  omega
theorem c244 (pattern : Ten) (guard : d0 pattern = 1) : d203 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c245 (pattern : Ten) (guard : d372 pattern = 1) : d207 pattern ≤ (0 : Int) + d280 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d372, d207, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c243 pattern childGuard
    simpa only [d372, d207, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d372, d207, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c244 pattern childGuard
    simpa only [d372, d207, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c246 (pattern : Ten) (guard : d0 pattern = 1) : d203 pattern ≤ (0 : Int) + d202 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c247 (pattern : Ten) (guard : d372 pattern = 1) : d207 pattern ≤ (0 : Int) + d202 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d372, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c243 pattern childGuard
    simpa only [d372, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d372, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c246 pattern childGuard
    simpa only [d372, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c248 (pattern : Ten) (guard : d372 pattern = 1) : d207 pattern ≤ (0 : Int) + d281 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d372 pattern = 1 := by simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c245 pattern childGuard
    simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d372 pattern = 1 := by simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c247 pattern childGuard
    simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c249 (pattern : Ten) (guard : d372 pattern = 1) : d207 pattern ≤ (0 : Int) + d284 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d372 pattern = 1 := by simpa only [d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c248 pattern childGuard
    simpa only [d284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d372 pattern = 1 := by simpa only [d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c247 pattern childGuard
    simpa only [d284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c250 (pattern : Ten) (guard : d372 pattern = 1) : d10 pattern ≤ (0 : Int) + d10 pattern := by
  omega
theorem c251 (pattern : Ten) (guard : d372 pattern = 1) : d211 pattern ≤ (0 : Int) + d282 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d372 pattern = 1 := by simpa only [d211, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c247 pattern childGuard
    simpa only [d211, d282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d372 pattern = 1 := by simpa only [d211, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c250 pattern childGuard
    simpa only [d211, d282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c252 (pattern : Ten) (guard : d1 pattern = 1) : d204 pattern ≤ (0 : Int) + d204 pattern := by
  omega
theorem c253 (pattern : Ten) (guard : d0 pattern = 1) : d205 pattern ≤ (0 : Int) + d204 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c254 (pattern : Ten) (guard : d372 pattern = 1) : d208 pattern ≤ (0 : Int) + d204 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d372, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c252 pattern childGuard
    simpa only [d372, d208, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d372, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c253 pattern childGuard
    simpa only [d372, d208, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c255 (pattern : Ten) (guard : d372 pattern = 1) : d212 pattern ≤ (0 : Int) + d283 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d372 pattern = 1 := by simpa only [d212, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c254 pattern childGuard
    simpa only [d212, d283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d372 pattern = 1 := by simpa only [d212, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c250 pattern childGuard
    simpa only [d212, d283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c256 (pattern : Ten) (guard : d372 pattern = 1) : d215 pattern ≤ (0 : Int) + d285 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d372 pattern = 1 := by simpa only [d215, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c251 pattern childGuard
    simpa only [d215, d285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d372 pattern = 1 := by simpa only [d215, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c255 pattern childGuard
    simpa only [d215, d285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c257 (pattern : Ten) (guard : d372 pattern = 1) : d218 pattern ≤ (0 : Int) + d286 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d372 pattern = 1 := by simpa only [d218, d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c249 pattern childGuard
    simpa only [d218, d286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d372 pattern = 1 := by simpa only [d218, d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c256 pattern childGuard
    simpa only [d218, d286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c258 (pattern : Ten) (guard : d0 pattern = 1) : d219 pattern ≤ (0 : Int) + d287 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c259 (pattern : Ten) (guard : d375 pattern = 1) : d220 pattern ≤ (0 : Int) + d288 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d372 pattern = 1 := by simpa only [d375, d220, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c257 pattern childGuard
    simpa only [d375, d220, d288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d375, d220, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c258 pattern childGuard
    simpa only [d375, d220, d288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c260 (pattern : Ten) (guard : d0 pattern = 1) : d7 pattern ≤ (0 : Int) + d54 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c261 (pattern : Ten) (guard : d354 pattern = 1) : d82 pattern ≤ (0 : Int) + d54 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d354, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c61 pattern childGuard
    simpa only [d354, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d354, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c260 pattern childGuard
    simpa only [d354, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c262 (pattern : Ten) (guard : d0 pattern = 1) : d58 pattern ≤ (0 : Int) + d59 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c263 (pattern : Ten) (guard : d354 pattern = 1) : d58 pattern ≤ (0 : Int) + d62 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d354, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c64 pattern childGuard
    simpa only [d354, d62, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d354, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c262 pattern childGuard
    simpa only [d354, d62, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c264 (pattern : Ten) (guard : d354 pattern = 1) : d83 pattern ≤ (0 : Int) + d64 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d354 pattern = 1 := by simpa only [d83, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c261 pattern childGuard
    simpa only [d83, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d354 pattern = 1 := by simpa only [d83, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c263 pattern childGuard
    simpa only [d83, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c265 (pattern : Ten) (guard : d0 pattern = 1) : d60 pattern ≤ (0 : Int) + d61 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c266 (pattern : Ten) (guard : d354 pattern = 1) : d60 pattern ≤ (0 : Int) + d63 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d354, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c69 pattern childGuard
    simpa only [d354, d63, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d354, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c265 pattern childGuard
    simpa only [d354, d63, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c267 (pattern : Ten) (guard : d354 pattern = 1) : d84 pattern ≤ (0 : Int) + d65 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d354 pattern = 1 := by simpa only [d84, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c68 pattern childGuard
    simpa only [d84, d65, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d354 pattern = 1 := by simpa only [d84, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c266 pattern childGuard
    simpa only [d84, d65, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c268 (pattern : Ten) (guard : d354 pattern = 1) : d85 pattern ≤ (0 : Int) + d66 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d354 pattern = 1 := by simpa only [d85, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c264 pattern childGuard
    simpa only [d85, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d354 pattern = 1 := by simpa only [d85, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c267 pattern childGuard
    simpa only [d85, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c269 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d207 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c270 (pattern : Ten) (guard : d353 pattern = 1) : d235 pattern ≤ (0 : Int) + d207 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d353, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c74 pattern childGuard
    simpa only [d353, d235, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d353, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c269 pattern childGuard
    simpa only [d353, d235, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c271 (pattern : Ten) (guard : d0 pattern = 1) : d211 pattern ≤ (0 : Int) + d212 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c272 (pattern : Ten) (guard : d353 pattern = 1) : d211 pattern ≤ (0 : Int) + d215 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d353, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c77 pattern childGuard
    simpa only [d353, d215, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d353, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c271 pattern childGuard
    simpa only [d353, d215, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c273 (pattern : Ten) (guard : d353 pattern = 1) : d236 pattern ≤ (0 : Int) + d218 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d353 pattern = 1 := by simpa only [d236, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c270 pattern childGuard
    simpa only [d236, d218, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d353 pattern = 1 := by simpa only [d236, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c272 pattern childGuard
    simpa only [d236, d218, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c274 (pattern : Ten) (guard : d0 pattern = 1) : d209 pattern ≤ (0 : Int) + d213 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c275 (pattern : Ten) (guard : d353 pattern = 1) : d209 pattern ≤ (0 : Int) + d216 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d353, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c81 pattern childGuard
    simpa only [d353, d216, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d353, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c274 pattern childGuard
    simpa only [d353, d216, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c276 (pattern : Ten) (guard : d0 pattern = 1) : d214 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c277 (pattern : Ten) (guard : d353 pattern = 1) : d214 pattern ≤ (0 : Int) + d217 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d353, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c84 pattern childGuard
    simpa only [d353, d217, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d353, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c276 pattern childGuard
    simpa only [d353, d217, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c278 (pattern : Ten) (guard : d353 pattern = 1) : d237 pattern ≤ (0 : Int) + d219 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d353 pattern = 1 := by simpa only [d237, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c275 pattern childGuard
    simpa only [d237, d219, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d353 pattern = 1 := by simpa only [d237, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c277 pattern childGuard
    simpa only [d237, d219, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c279 (pattern : Ten) (guard : d353 pattern = 1) : d238 pattern ≤ (0 : Int) + d220 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d353 pattern = 1 := by simpa only [d238, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c273 pattern childGuard
    simpa only [d238, d220, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d353 pattern = 1 := by simpa only [d238, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c278 pattern childGuard
    simpa only [d238, d220, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c280 (pattern : Ten) (guard : d0 pattern = 1) : d58 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c281 (pattern : Ten) (guard : d368 pattern = 1) : d83 pattern ≤ (0 : Int) + d134 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d354 pattern = 1 := by simpa only [d368, d83, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c261 pattern childGuard
    simpa only [d368, d83, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d368, d83, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c280 pattern childGuard
    simpa only [d368, d83, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c282 (pattern : Ten) (guard : d0 pattern = 1) : d60 pattern ≤ (0 : Int) + d56 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c283 (pattern : Ten) (guard : d368 pattern = 1) : d84 pattern ≤ (0 : Int) + d56 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d354 pattern = 1 := by simpa only [d368, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c68 pattern childGuard
    simpa only [d368, d84, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d368, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c282 pattern childGuard
    simpa only [d368, d84, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c284 (pattern : Ten) (guard : d368 pattern = 1) : d85 pattern ≤ (0 : Int) + d135 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d368 pattern = 1 := by simpa only [d85, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c281 pattern childGuard
    simpa only [d85, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d368 pattern = 1 := by simpa only [d85, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c283 pattern childGuard
    simpa only [d85, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c285 (pattern : Ten) (guard : d0 pattern = 1) : d211 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c286 (pattern : Ten) (guard : d370 pattern = 1) : d236 pattern ≤ (0 : Int) + d290 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d353 pattern = 1 := by simpa only [d370, d236, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c270 pattern childGuard
    simpa only [d370, d236, d290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d370, d236, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c285 pattern childGuard
    simpa only [d370, d236, d290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c287 (pattern : Ten) (guard : d353 pattern = 1) : d209 pattern ≤ (0 : Int) + d209 pattern := by
  omega
theorem c288 (pattern : Ten) (guard : d0 pattern = 1) : d214 pattern ≤ (0 : Int) + d209 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c289 (pattern : Ten) (guard : d370 pattern = 1) : d237 pattern ≤ (0 : Int) + d209 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d353 pattern = 1 := by simpa only [d370, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c287 pattern childGuard
    simpa only [d370, d237, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d370, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c288 pattern childGuard
    simpa only [d370, d237, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c290 (pattern : Ten) (guard : d370 pattern = 1) : d238 pattern ≤ (0 : Int) + d291 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d370 pattern = 1 := by simpa only [d238, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c286 pattern childGuard
    simpa only [d238, d291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d370 pattern = 1 := by simpa only [d238, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c289 pattern childGuard
    simpa only [d238, d291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c291 (pattern : Ten) (guard : d1 pattern = 1) : d171 pattern ≤ (0 : Int) + d171 pattern := by
  omega
theorem c292 (pattern : Ten) (guard : d0 pattern = 1) : d171 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c293 (pattern : Ten) (guard : d350 pattern = 1) : d171 pattern ≤ (0 : Int) + d292 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c291 pattern childGuard
    simpa only [d350, d292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c292 pattern childGuard
    simpa only [d350, d292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c294 (pattern : Ten) (guard : d350 pattern = 1) : d172 pattern ≤ (0 : Int) + d172 pattern := by
  omega
theorem c295 (pattern : Ten) (guard : d350 pattern = 1) : d174 pattern ≤ (0 : Int) + d293 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d174, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c293 pattern childGuard
    simpa only [d174, d293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d174, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c294 pattern childGuard
    simpa only [d174, d293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c296 (pattern : Ten) (guard : d350 pattern = 1) : d197 pattern ≤ (0 : Int) + d197 pattern := by
  omega
theorem c297 (pattern : Ten) (guard : d350 pattern = 1) : d202 pattern ≤ (0 : Int) + d294 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d202, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c295 pattern childGuard
    simpa only [d202, d294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d202, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c296 pattern childGuard
    simpa only [d202, d294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c298 (pattern : Ten) (guard : d350 pattern = 1) : d203 pattern ≤ (0 : Int) + d203 pattern := by
  omega
theorem c299 (pattern : Ten) (guard : d350 pattern = 1) : d207 pattern ≤ (0 : Int) + d295 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d207, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c297 pattern childGuard
    simpa only [d207, d295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d207, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c298 pattern childGuard
    simpa only [d207, d295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c300 (pattern : Ten) (guard : d350 pattern = 1) : d207 pattern ≤ (0 : Int) + d207 pattern := by
  omega
theorem c301 (pattern : Ten) (guard : d350 pattern = 1) : d207 pattern ≤ (0 : Int) + d296 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c299 pattern childGuard
    simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c300 pattern childGuard
    simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c302 (pattern : Ten) (guard : d354 pattern = 1) : d235 pattern ≤ (0 : Int) + d297 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d354, d235, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c301 pattern childGuard
    simpa only [d354, d235, d297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d354, d235, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c269 pattern childGuard
    simpa only [d354, d235, d297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c303 (pattern : Ten) (guard : d350 pattern = 1) : d211 pattern ≤ (0 : Int) + d211 pattern := by
  omega
theorem c304 (pattern : Ten) (guard : d354 pattern = 1) : d211 pattern ≤ (0 : Int) + d215 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d354, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c303 pattern childGuard
    simpa only [d354, d215, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d354, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c271 pattern childGuard
    simpa only [d354, d215, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c305 (pattern : Ten) (guard : d354 pattern = 1) : d236 pattern ≤ (0 : Int) + d298 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d354 pattern = 1 := by simpa only [d236, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c302 pattern childGuard
    simpa only [d236, d298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d354 pattern = 1 := by simpa only [d236, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c304 pattern childGuard
    simpa only [d236, d298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c306 (pattern : Ten) (guard : d354 pattern = 1) : d209 pattern ≤ (0 : Int) + d209 pattern := by
  omega
theorem c307 (pattern : Ten) (guard : d350 pattern = 1) : d214 pattern ≤ (0 : Int) + d214 pattern := by
  omega
theorem c308 (pattern : Ten) (guard : d354 pattern = 1) : d214 pattern ≤ (0 : Int) + d217 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d354, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c307 pattern childGuard
    simpa only [d354, d217, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d354, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c276 pattern childGuard
    simpa only [d354, d217, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c309 (pattern : Ten) (guard : d354 pattern = 1) : d237 pattern ≤ (0 : Int) + d299 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d354 pattern = 1 := by simpa only [d237, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c306 pattern childGuard
    simpa only [d237, d299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d354 pattern = 1 := by simpa only [d237, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c308 pattern childGuard
    simpa only [d237, d299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c310 (pattern : Ten) (guard : d354 pattern = 1) : d238 pattern ≤ (0 : Int) + d300 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d354 pattern = 1 := by simpa only [d238, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c305 pattern childGuard
    simpa only [d238, d300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d354 pattern = 1 := by simpa only [d238, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c309 pattern childGuard
    simpa only [d238, d300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c311 (pattern : Ten) (guard : d0 pattern = 1) : d84 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c312 (pattern : Ten) (guard : d377 pattern = 1) : d85 pattern ≤ (0 : Int) + d133 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d354 pattern = 1 := by simpa only [d377, d85, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c264 pattern childGuard
    simpa only [d377, d85, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d377, d85, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c311 pattern childGuard
    simpa only [d377, d85, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c313 (pattern : Ten) (guard : d0 pattern = 1) : d237 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c314 (pattern : Ten) (guard : d378 pattern = 1) : d238 pattern ≤ (0 : Int) + d289 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d353 pattern = 1 := by simpa only [d378, d238, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c273 pattern childGuard
    simpa only [d378, d238, d289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d378, d238, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c313 pattern childGuard
    simpa only [d378, d238, d289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c315 (pattern : Ten) (guard : d350 pattern = 1) : d207 pattern ≤ (0 : Int) + d297 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c301 pattern childGuard
    simpa only [d297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c300 pattern childGuard
    simpa only [d297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c316 (pattern : Ten) (guard : d350 pattern = 1) : d215 pattern ≤ (0 : Int) + d215 pattern := by
  omega
theorem c317 (pattern : Ten) (guard : d350 pattern = 1) : d218 pattern ≤ (0 : Int) + d298 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d218, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c315 pattern childGuard
    simpa only [d218, d298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d218, d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c316 pattern childGuard
    simpa only [d218, d298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c318 (pattern : Ten) (guard : d350 pattern = 1) : d209 pattern ≤ (0 : Int) + d209 pattern := by
  omega
theorem c319 (pattern : Ten) (guard : d1 pattern = 1) : d195 pattern ≤ (0 : Int) + d195 pattern := by
  omega
end NetHack.Sokoban41.Diagram
