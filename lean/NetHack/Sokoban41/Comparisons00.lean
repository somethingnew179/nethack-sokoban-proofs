/- Staged soko4-1 certificate. No result until all kernel checks pass. -/
import NetHack.Sokoban41.Substitutions09
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem c0 (pattern : Ten) (guard : d350 pattern = 1) : d37 pattern ≤ (0 : Int) + d37 pattern := by
  omega
theorem c1 (pattern : Ten) (guard : d1 pattern = 1) : d192 pattern ≤ (0 : Int) + d192 pattern := by
  omega
theorem c2 (pattern : Ten) (guard : d352 pattern = 1) : d23 pattern ≤ (0 : Int) + d23 pattern := by
  omega
theorem c3 (pattern : Ten) (guard : d352 pattern = 1) : d0 pattern ≤ (0 : Int) + d0 pattern := by
  omega
theorem c4 (pattern : Ten) (guard : d1 pattern = 1) : d9 pattern ≤ (0 : Int) + d9 pattern := by
  omega
theorem c5 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6 (pattern : Ten) (guard : d351 pattern = 1) : d11 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d351, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4 pattern childGuard
    simpa only [d351, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d351, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5 pattern childGuard
    simpa only [d351, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7 (pattern : Ten) (guard : d0 pattern = 1) : d11 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c8 (pattern : Ten) (guard : d352 pattern = 1) : d11 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6 pattern childGuard
    simpa only [d352, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7 pattern childGuard
    simpa only [d352, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9 (pattern : Ten) (guard : d352 pattern = 1) : d13 pattern ≤ (0 : Int) + d67 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d352 pattern = 1 := by simpa only [d13, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3 pattern childGuard
    simpa only [d13, d67, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d352 pattern = 1 := by simpa only [d13, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8 pattern childGuard
    simpa only [d13, d67, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c10 (pattern : Ten) (guard : d352 pattern = 1) : d10 pattern ≤ (0 : Int) + d10 pattern := by
  omega
theorem c11 (pattern : Ten) (guard : d352 pattern = 1) : d14 pattern ≤ (0 : Int) + d68 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d352 pattern = 1 := by simpa only [d14, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8 pattern childGuard
    simpa only [d14, d68, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d352 pattern = 1 := by simpa only [d14, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10 pattern childGuard
    simpa only [d14, d68, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c12 (pattern : Ten) (guard : d352 pattern = 1) : d19 pattern ≤ (0 : Int) + d69 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d352 pattern = 1 := by simpa only [d19, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9 pattern childGuard
    simpa only [d19, d69, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d352 pattern = 1 := by simpa only [d19, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11 pattern childGuard
    simpa only [d19, d69, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c13 (pattern : Ten) (guard : d352 pattern = 1) : d20 pattern ≤ (0 : Int) + d70 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d352 pattern = 1 := by simpa only [d20, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11 pattern childGuard
    simpa only [d20, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d352 pattern = 1 := by simpa only [d20, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10 pattern childGuard
    simpa only [d20, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14 (pattern : Ten) (guard : d352 pattern = 1) : d24 pattern ≤ (0 : Int) + d71 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d352 pattern = 1 := by simpa only [d24, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12 pattern childGuard
    simpa only [d24, d71, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d352 pattern = 1 := by simpa only [d24, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13 pattern childGuard
    simpa only [d24, d71, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c15 (pattern : Ten) (guard : d352 pattern = 1) : d29 pattern ≤ (0 : Int) + d73 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d352 pattern = 1 := by simpa only [d29, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2 pattern childGuard
    simpa only [d29, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d352 pattern = 1 := by simpa only [d29, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14 pattern childGuard
    simpa only [d29, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c16 (pattern : Ten) (guard : d352 pattern = 1) : d25 pattern ≤ (0 : Int) + d25 pattern := by
  omega
theorem c17 (pattern : Ten) (guard : d352 pattern = 1) : d30 pattern ≤ (0 : Int) + d74 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d352 pattern = 1 := by simpa only [d30, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16 pattern childGuard
    simpa only [d30, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d352 pattern = 1 := by simpa only [d30, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14 pattern childGuard
    simpa only [d30, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18 (pattern : Ten) (guard : d352 pattern = 1) : d33 pattern ≤ (0 : Int) + d77 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d352 pattern = 1 := by simpa only [d33, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c15 pattern childGuard
    simpa only [d33, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d352 pattern = 1 := by simpa only [d33, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17 pattern childGuard
    simpa only [d33, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c19 (pattern : Ten) (guard : d352 pattern = 1) : d26 pattern ≤ (0 : Int) + d26 pattern := by
  omega
theorem c20 (pattern : Ten) (guard : d352 pattern = 1) : d27 pattern ≤ (0 : Int) + d72 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d352 pattern = 1 := by simpa only [d27, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13 pattern childGuard
    simpa only [d27, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d352 pattern = 1 := by simpa only [d27, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10 pattern childGuard
    simpa only [d27, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21 (pattern : Ten) (guard : d352 pattern = 1) : d31 pattern ≤ (0 : Int) + d75 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d352 pattern = 1 := by simpa only [d31, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19 pattern childGuard
    simpa only [d31, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d352 pattern = 1 := by simpa only [d31, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20 pattern childGuard
    simpa only [d31, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22 (pattern : Ten) (guard : d352 pattern = 1) : d28 pattern ≤ (0 : Int) + d28 pattern := by
  omega
theorem c23 (pattern : Ten) (guard : d352 pattern = 1) : d32 pattern ≤ (0 : Int) + d76 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d352 pattern = 1 := by simpa only [d32, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22 pattern childGuard
    simpa only [d32, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d352 pattern = 1 := by simpa only [d32, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20 pattern childGuard
    simpa only [d32, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c24 (pattern : Ten) (guard : d352 pattern = 1) : d34 pattern ≤ (0 : Int) + d78 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d352 pattern = 1 := by simpa only [d34, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21 pattern childGuard
    simpa only [d34, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d352 pattern = 1 := by simpa only [d34, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23 pattern childGuard
    simpa only [d34, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c25 (pattern : Ten) (guard : d352 pattern = 1) : d35 pattern ≤ (0 : Int) + d79 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d352 pattern = 1 := by simpa only [d35, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18 pattern childGuard
    simpa only [d35, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d352 pattern = 1 := by simpa only [d35, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c24 pattern childGuard
    simpa only [d35, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c26 (pattern : Ten) (guard : d352 pattern = 1) : d36 pattern ≤ (0 : Int) + d80 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d352 pattern = 1 := by simpa only [d36, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c24 pattern childGuard
    simpa only [d36, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d352 pattern = 1 := by simpa only [d36, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10 pattern childGuard
    simpa only [d36, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c27 (pattern : Ten) (guard : d352 pattern = 1) : d37 pattern ≤ (0 : Int) + d81 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d352 pattern = 1 := by simpa only [d37, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c25 pattern childGuard
    simpa only [d37, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d352 pattern = 1 := by simpa only [d37, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c26 pattern childGuard
    simpa only [d37, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c28 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (0 : Int) + d0 pattern := by
  omega
theorem c29 (pattern : Ten) (guard : d0 pattern = 1) : d1 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c30 (pattern : Ten) (guard : d351 pattern = 1) : d171 pattern ≤ (0 : Int) + d221 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d351, d171, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c28 pattern childGuard
    simpa only [d351, d171, d221, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d351, d171, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c29 pattern childGuard
    simpa only [d351, d171, d221, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c31 (pattern : Ten) (guard : d0 pattern = 1) : d1 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c32 (pattern : Ten) (guard : d351 pattern = 1) : d171 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d351, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c28 pattern childGuard
    simpa only [d351, d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d351, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c31 pattern childGuard
    simpa only [d351, d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c33 (pattern : Ten) (guard : d351 pattern = 1) : d171 pattern ≤ (0 : Int) + d222 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c30 pattern childGuard
    simpa only [d222, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c32 pattern childGuard
    simpa only [d222, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c34 (pattern : Ten) (guard : d351 pattern = 1) : d171 pattern ≤ (0 : Int) + d223 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c33 pattern childGuard
    simpa only [d223, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c32 pattern childGuard
    simpa only [d223, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c35 (pattern : Ten) (guard : d351 pattern = 1) : d10 pattern ≤ (0 : Int) + d10 pattern := by
  omega
theorem c36 (pattern : Ten) (guard : d351 pattern = 1) : d173 pattern ≤ (0 : Int) + d12 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d173, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c32 pattern childGuard
    simpa only [d173, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d173, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c35 pattern childGuard
    simpa only [d173, d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c37 (pattern : Ten) (guard : d351 pattern = 1) : d176 pattern ≤ (0 : Int) + d224 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d176, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c34 pattern childGuard
    simpa only [d176, d224, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d176, d224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c36 pattern childGuard
    simpa only [d176, d224, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c38 (pattern : Ten) (guard : d351 pattern = 1) : d177 pattern ≤ (0 : Int) + d18 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d177, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c36 pattern childGuard
    simpa only [d177, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d177, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c35 pattern childGuard
    simpa only [d177, d18, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c39 (pattern : Ten) (guard : d351 pattern = 1) : d180 pattern ≤ (0 : Int) + d225 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d180, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c37 pattern childGuard
    simpa only [d180, d225, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d180, d225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c38 pattern childGuard
    simpa only [d180, d225, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c40 (pattern : Ten) (guard : d351 pattern = 1) : d181 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d181, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c38 pattern childGuard
    simpa only [d181, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d181, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c35 pattern childGuard
    simpa only [d181, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c41 (pattern : Ten) (guard : d351 pattern = 1) : d184 pattern ≤ (0 : Int) + d226 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d184, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c39 pattern childGuard
    simpa only [d184, d226, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d184, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c40 pattern childGuard
    simpa only [d184, d226, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c42 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (0 : Int) + d2 pattern := by
  omega
theorem c43 (pattern : Ten) (guard : d0 pattern = 1) : d3 pattern ≤ (0 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c44 (pattern : Ten) (guard : d351 pattern = 1) : d172 pattern ≤ (0 : Int) + d2 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d351, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c42 pattern childGuard
    simpa only [d351, d172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d351, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c43 pattern childGuard
    simpa only [d351, d172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c45 (pattern : Ten) (guard : d351 pattern = 1) : d174 pattern ≤ (0 : Int) + d15 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d174, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c32 pattern childGuard
    simpa only [d174, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d174, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c44 pattern childGuard
    simpa only [d174, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c46 (pattern : Ten) (guard : d351 pattern = 1) : d175 pattern ≤ (0 : Int) + d16 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d175, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c44 pattern childGuard
    simpa only [d175, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d175, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c35 pattern childGuard
    simpa only [d175, d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c47 (pattern : Ten) (guard : d351 pattern = 1) : d178 pattern ≤ (0 : Int) + d21 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d178, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c45 pattern childGuard
    simpa only [d178, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d178, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c46 pattern childGuard
    simpa only [d178, d21, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c48 (pattern : Ten) (guard : d351 pattern = 1) : d179 pattern ≤ (0 : Int) + d22 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d179, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c46 pattern childGuard
    simpa only [d179, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d179, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c35 pattern childGuard
    simpa only [d179, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c49 (pattern : Ten) (guard : d351 pattern = 1) : d182 pattern ≤ (0 : Int) + d25 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d182, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c47 pattern childGuard
    simpa only [d182, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d182, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c48 pattern childGuard
    simpa only [d182, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c50 (pattern : Ten) (guard : d351 pattern = 1) : d185 pattern ≤ (0 : Int) + d227 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d185, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c49 pattern childGuard
    simpa only [d185, d227, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d185, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c40 pattern childGuard
    simpa only [d185, d227, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c51 (pattern : Ten) (guard : d351 pattern = 1) : d188 pattern ≤ (0 : Int) + d230 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d188, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c41 pattern childGuard
    simpa only [d188, d230, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d188, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c50 pattern childGuard
    simpa only [d188, d230, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c52 (pattern : Ten) (guard : d351 pattern = 1) : d186 pattern ≤ (0 : Int) + d228 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d186, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c40 pattern childGuard
    simpa only [d186, d228, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d186, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c35 pattern childGuard
    simpa only [d186, d228, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c53 (pattern : Ten) (guard : d351 pattern = 1) : d183 pattern ≤ (0 : Int) + d28 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d183, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c48 pattern childGuard
    simpa only [d183, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d183, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c35 pattern childGuard
    simpa only [d183, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c54 (pattern : Ten) (guard : d351 pattern = 1) : d187 pattern ≤ (0 : Int) + d229 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d187, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c53 pattern childGuard
    simpa only [d187, d229, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d187, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c35 pattern childGuard
    simpa only [d187, d229, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c55 (pattern : Ten) (guard : d351 pattern = 1) : d189 pattern ≤ (0 : Int) + d231 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d189, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c52 pattern childGuard
    simpa only [d189, d231, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d189, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c54 pattern childGuard
    simpa only [d189, d231, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c56 (pattern : Ten) (guard : d351 pattern = 1) : d190 pattern ≤ (0 : Int) + d232 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d190, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c51 pattern childGuard
    simpa only [d190, d232, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d190, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c55 pattern childGuard
    simpa only [d190, d232, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c57 (pattern : Ten) (guard : d351 pattern = 1) : d191 pattern ≤ (0 : Int) + d233 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d191, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c55 pattern childGuard
    simpa only [d191, d233, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d191, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c35 pattern childGuard
    simpa only [d191, d233, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c58 (pattern : Ten) (guard : d351 pattern = 1) : d192 pattern ≤ (0 : Int) + d234 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d192, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c56 pattern childGuard
    simpa only [d192, d234, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d192, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c57 pattern childGuard
    simpa only [d192, d234, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c59 (pattern : Ten) (guard : d350 pattern = 1) : d66 pattern ≤ (0 : Int) + d66 pattern := by
  omega
theorem c60 (pattern : Ten) (guard : d1 pattern = 1) : d220 pattern ≤ (0 : Int) + d220 pattern := by
  omega
theorem c61 (pattern : Ten) (guard : d350 pattern = 1) : d54 pattern ≤ (0 : Int) + d54 pattern := by
  omega
theorem c62 (pattern : Ten) (guard : d0 pattern = 1) : d54 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c63 (pattern : Ten) (guard : d354 pattern = 1) : d54 pattern ≤ (0 : Int) + d82 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d354, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c61 pattern childGuard
    simpa only [d354, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d354, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c62 pattern childGuard
    simpa only [d354, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c64 (pattern : Ten) (guard : d350 pattern = 1) : d58 pattern ≤ (0 : Int) + d58 pattern := by
  omega
theorem c65 (pattern : Ten) (guard : d0 pattern = 1) : d59 pattern ≤ (0 : Int) + d58 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c66 (pattern : Ten) (guard : d354 pattern = 1) : d62 pattern ≤ (0 : Int) + d58 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d354, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c64 pattern childGuard
    simpa only [d354, d62, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d354, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c65 pattern childGuard
    simpa only [d354, d62, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c67 (pattern : Ten) (guard : d354 pattern = 1) : d64 pattern ≤ (0 : Int) + d83 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d354 pattern = 1 := by simpa only [d64, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c63 pattern childGuard
    simpa only [d64, d83, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d354 pattern = 1 := by simpa only [d64, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c66 pattern childGuard
    simpa only [d64, d83, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c68 (pattern : Ten) (guard : d354 pattern = 1) : d56 pattern ≤ (0 : Int) + d56 pattern := by
  omega
theorem c69 (pattern : Ten) (guard : d350 pattern = 1) : d60 pattern ≤ (0 : Int) + d60 pattern := by
  omega
theorem c70 (pattern : Ten) (guard : d0 pattern = 1) : d61 pattern ≤ (0 : Int) + d60 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c71 (pattern : Ten) (guard : d354 pattern = 1) : d63 pattern ≤ (0 : Int) + d60 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d354, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c69 pattern childGuard
    simpa only [d354, d63, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d354, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c70 pattern childGuard
    simpa only [d354, d63, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c72 (pattern : Ten) (guard : d354 pattern = 1) : d65 pattern ≤ (0 : Int) + d84 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d354 pattern = 1 := by simpa only [d65, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c68 pattern childGuard
    simpa only [d65, d84, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d354 pattern = 1 := by simpa only [d65, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c71 pattern childGuard
    simpa only [d65, d84, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c73 (pattern : Ten) (guard : d354 pattern = 1) : d66 pattern ≤ (0 : Int) + d85 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d354 pattern = 1 := by simpa only [d66, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c67 pattern childGuard
    simpa only [d66, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d354 pattern = 1 := by simpa only [d66, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c72 pattern childGuard
    simpa only [d66, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c74 (pattern : Ten) (guard : d1 pattern = 1) : d207 pattern ≤ (0 : Int) + d207 pattern := by
  omega
theorem c75 (pattern : Ten) (guard : d0 pattern = 1) : d207 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c76 (pattern : Ten) (guard : d353 pattern = 1) : d207 pattern ≤ (0 : Int) + d235 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d353, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c74 pattern childGuard
    simpa only [d353, d235, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d353, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c75 pattern childGuard
    simpa only [d353, d235, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c77 (pattern : Ten) (guard : d1 pattern = 1) : d211 pattern ≤ (0 : Int) + d211 pattern := by
  omega
theorem c78 (pattern : Ten) (guard : d0 pattern = 1) : d212 pattern ≤ (0 : Int) + d211 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c79 (pattern : Ten) (guard : d353 pattern = 1) : d215 pattern ≤ (0 : Int) + d211 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d353, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c77 pattern childGuard
    simpa only [d353, d215, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d353, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d353, d215, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c80 (pattern : Ten) (guard : d353 pattern = 1) : d218 pattern ≤ (0 : Int) + d236 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d353 pattern = 1 := by simpa only [d218, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c76 pattern childGuard
    simpa only [d218, d236, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d353 pattern = 1 := by simpa only [d218, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c79 pattern childGuard
    simpa only [d218, d236, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c81 (pattern : Ten) (guard : d1 pattern = 1) : d209 pattern ≤ (0 : Int) + d209 pattern := by
  omega
theorem c82 (pattern : Ten) (guard : d0 pattern = 1) : d213 pattern ≤ (0 : Int) + d209 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c83 (pattern : Ten) (guard : d353 pattern = 1) : d216 pattern ≤ (0 : Int) + d209 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d353, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c81 pattern childGuard
    simpa only [d353, d216, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d353, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c82 pattern childGuard
    simpa only [d353, d216, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c84 (pattern : Ten) (guard : d1 pattern = 1) : d214 pattern ≤ (0 : Int) + d214 pattern := by
  omega
theorem c85 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d214 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c86 (pattern : Ten) (guard : d353 pattern = 1) : d217 pattern ≤ (0 : Int) + d214 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d353, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c84 pattern childGuard
    simpa only [d353, d217, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d353, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c85 pattern childGuard
    simpa only [d353, d217, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c87 (pattern : Ten) (guard : d353 pattern = 1) : d219 pattern ≤ (0 : Int) + d237 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d353 pattern = 1 := by simpa only [d219, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c83 pattern childGuard
    simpa only [d219, d237, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d353 pattern = 1 := by simpa only [d219, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c86 pattern childGuard
    simpa only [d219, d237, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c88 (pattern : Ten) (guard : d353 pattern = 1) : d220 pattern ≤ (0 : Int) + d238 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d353 pattern = 1 := by simpa only [d220, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c80 pattern childGuard
    simpa only [d220, d238, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d353 pattern = 1 := by simpa only [d220, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c87 pattern childGuard
    simpa only [d220, d238, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c89 (pattern : Ten) (guard : d357 pattern = 1) : d37 pattern ≤ (0 : Int) + d37 pattern := by
  omega
theorem c90 (pattern : Ten) (guard : d0 pattern = 1) : d0 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c91 (pattern : Ten) (guard : d356 pattern = 1) : d0 pattern ≤ (0 : Int) + d239 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d356, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c28 pattern childGuard
    simpa only [d356, d239, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d356, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c90 pattern childGuard
    simpa only [d356, d239, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c92 (pattern : Ten) (guard : d356 pattern = 1) : d1 pattern ≤ (0 : Int) + d1 pattern := by
  omega
theorem c93 (pattern : Ten) (guard : d356 pattern = 1) : d171 pattern ≤ (0 : Int) + d240 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d356 pattern = 1 := by simpa only [d171, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c91 pattern childGuard
    simpa only [d171, d240, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d356 pattern = 1 := by simpa only [d171, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d171, d240, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c94 (pattern : Ten) (guard : d356 pattern = 1) : d171 pattern ≤ (0 : Int) + d171 pattern := by
  omega
theorem c95 (pattern : Ten) (guard : d356 pattern = 1) : d171 pattern ≤ (0 : Int) + d241 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d356 pattern = 1 := by simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c93 pattern childGuard
    simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d356 pattern = 1 := by simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c94 pattern childGuard
    simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c96 (pattern : Ten) (guard : d356 pattern = 1) : d171 pattern ≤ (0 : Int) + d242 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d356 pattern = 1 := by simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c95 pattern childGuard
    simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d356 pattern = 1 := by simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c94 pattern childGuard
    simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c97 (pattern : Ten) (guard : d356 pattern = 1) : d173 pattern ≤ (0 : Int) + d173 pattern := by
  omega
theorem c98 (pattern : Ten) (guard : d356 pattern = 1) : d176 pattern ≤ (0 : Int) + d243 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d356 pattern = 1 := by simpa only [d176, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c96 pattern childGuard
    simpa only [d176, d243, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d356 pattern = 1 := by simpa only [d176, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c97 pattern childGuard
    simpa only [d176, d243, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c99 (pattern : Ten) (guard : d356 pattern = 1) : d177 pattern ≤ (0 : Int) + d177 pattern := by
  omega
theorem c100 (pattern : Ten) (guard : d356 pattern = 1) : d180 pattern ≤ (0 : Int) + d244 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d356 pattern = 1 := by simpa only [d180, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c98 pattern childGuard
    simpa only [d180, d244, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d356 pattern = 1 := by simpa only [d180, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c99 pattern childGuard
    simpa only [d180, d244, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c101 (pattern : Ten) (guard : d356 pattern = 1) : d181 pattern ≤ (0 : Int) + d181 pattern := by
  omega
theorem c102 (pattern : Ten) (guard : d356 pattern = 1) : d184 pattern ≤ (0 : Int) + d245 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d356 pattern = 1 := by simpa only [d184, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c100 pattern childGuard
    simpa only [d184, d245, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d356 pattern = 1 := by simpa only [d184, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c101 pattern childGuard
    simpa only [d184, d245, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c103 (pattern : Ten) (guard : d356 pattern = 1) : d185 pattern ≤ (0 : Int) + d185 pattern := by
  omega
theorem c104 (pattern : Ten) (guard : d356 pattern = 1) : d188 pattern ≤ (0 : Int) + d246 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d356 pattern = 1 := by simpa only [d188, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c102 pattern childGuard
    simpa only [d188, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d356 pattern = 1 := by simpa only [d188, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c103 pattern childGuard
    simpa only [d188, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c105 (pattern : Ten) (guard : d356 pattern = 1) : d189 pattern ≤ (0 : Int) + d189 pattern := by
  omega
theorem c106 (pattern : Ten) (guard : d356 pattern = 1) : d190 pattern ≤ (0 : Int) + d247 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d356 pattern = 1 := by simpa only [d190, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c104 pattern childGuard
    simpa only [d190, d247, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d356 pattern = 1 := by simpa only [d190, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c105 pattern childGuard
    simpa only [d190, d247, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c107 (pattern : Ten) (guard : d356 pattern = 1) : d191 pattern ≤ (0 : Int) + d191 pattern := by
  omega
theorem c108 (pattern : Ten) (guard : d356 pattern = 1) : d192 pattern ≤ (0 : Int) + d248 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d356 pattern = 1 := by simpa only [d192, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c106 pattern childGuard
    simpa only [d192, d248, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d356 pattern = 1 := by simpa only [d192, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c107 pattern childGuard
    simpa only [d192, d248, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c109 (pattern : Ten) (guard : d0 pattern = 1) : d9 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c110 (pattern : Ten) (guard : d351 pattern = 1) : d9 pattern ≤ (0 : Int) + d11 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d351, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4 pattern childGuard
    simpa only [d351, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d351, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c109 pattern childGuard
    simpa only [d351, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c111 (pattern : Ten) (guard : d0 pattern = 1) : d9 pattern ≤ (0 : Int) + d11 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c112 (pattern : Ten) (guard : d352 pattern = 1) : d9 pattern ≤ (0 : Int) + d11 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c110 pattern childGuard
    simpa only [d352, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c111 pattern childGuard
    simpa only [d352, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c113 (pattern : Ten) (guard : d352 pattern = 1) : d67 pattern ≤ (0 : Int) + d13 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d352 pattern = 1 := by simpa only [d67, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3 pattern childGuard
    simpa only [d67, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d352 pattern = 1 := by simpa only [d67, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c112 pattern childGuard
    simpa only [d67, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c114 (pattern : Ten) (guard : d352 pattern = 1) : d68 pattern ≤ (0 : Int) + d14 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d352 pattern = 1 := by simpa only [d68, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c112 pattern childGuard
    simpa only [d68, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d352 pattern = 1 := by simpa only [d68, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10 pattern childGuard
    simpa only [d68, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c115 (pattern : Ten) (guard : d352 pattern = 1) : d69 pattern ≤ (0 : Int) + d19 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d352 pattern = 1 := by simpa only [d69, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c113 pattern childGuard
    simpa only [d69, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d352 pattern = 1 := by simpa only [d69, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c114 pattern childGuard
    simpa only [d69, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c116 (pattern : Ten) (guard : d352 pattern = 1) : d70 pattern ≤ (0 : Int) + d20 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d352 pattern = 1 := by simpa only [d70, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c114 pattern childGuard
    simpa only [d70, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d352 pattern = 1 := by simpa only [d70, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10 pattern childGuard
    simpa only [d70, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c117 (pattern : Ten) (guard : d352 pattern = 1) : d71 pattern ≤ (0 : Int) + d24 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d352 pattern = 1 := by simpa only [d71, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c115 pattern childGuard
    simpa only [d71, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d352 pattern = 1 := by simpa only [d71, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c116 pattern childGuard
    simpa only [d71, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c118 (pattern : Ten) (guard : d352 pattern = 1) : d73 pattern ≤ (0 : Int) + d29 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d352 pattern = 1 := by simpa only [d73, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2 pattern childGuard
    simpa only [d73, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d352 pattern = 1 := by simpa only [d73, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c117 pattern childGuard
    simpa only [d73, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c119 (pattern : Ten) (guard : d352 pattern = 1) : d74 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d352 pattern = 1 := by simpa only [d74, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16 pattern childGuard
    simpa only [d74, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d352 pattern = 1 := by simpa only [d74, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c117 pattern childGuard
    simpa only [d74, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c120 (pattern : Ten) (guard : d352 pattern = 1) : d77 pattern ≤ (0 : Int) + d33 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d352 pattern = 1 := by simpa only [d77, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c118 pattern childGuard
    simpa only [d77, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d352 pattern = 1 := by simpa only [d77, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c119 pattern childGuard
    simpa only [d77, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c121 (pattern : Ten) (guard : d352 pattern = 1) : d72 pattern ≤ (0 : Int) + d27 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d352 pattern = 1 := by simpa only [d72, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c116 pattern childGuard
    simpa only [d72, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d352 pattern = 1 := by simpa only [d72, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10 pattern childGuard
    simpa only [d72, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c122 (pattern : Ten) (guard : d352 pattern = 1) : d75 pattern ≤ (0 : Int) + d31 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d352 pattern = 1 := by simpa only [d75, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19 pattern childGuard
    simpa only [d75, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d352 pattern = 1 := by simpa only [d75, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c121 pattern childGuard
    simpa only [d75, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c123 (pattern : Ten) (guard : d352 pattern = 1) : d76 pattern ≤ (0 : Int) + d32 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d352 pattern = 1 := by simpa only [d76, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22 pattern childGuard
    simpa only [d76, d32, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d352 pattern = 1 := by simpa only [d76, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c121 pattern childGuard
    simpa only [d76, d32, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c124 (pattern : Ten) (guard : d352 pattern = 1) : d78 pattern ≤ (0 : Int) + d34 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d352 pattern = 1 := by simpa only [d78, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c122 pattern childGuard
    simpa only [d78, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d352 pattern = 1 := by simpa only [d78, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c123 pattern childGuard
    simpa only [d78, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c125 (pattern : Ten) (guard : d352 pattern = 1) : d79 pattern ≤ (0 : Int) + d35 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d352 pattern = 1 := by simpa only [d79, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c120 pattern childGuard
    simpa only [d79, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d352 pattern = 1 := by simpa only [d79, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c124 pattern childGuard
    simpa only [d79, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c126 (pattern : Ten) (guard : d352 pattern = 1) : d80 pattern ≤ (0 : Int) + d36 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d352 pattern = 1 := by simpa only [d80, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c124 pattern childGuard
    simpa only [d80, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d352 pattern = 1 := by simpa only [d80, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c10 pattern childGuard
    simpa only [d80, d36, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c127 (pattern : Ten) (guard : d352 pattern = 1) : d81 pattern ≤ (0 : Int) + d37 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d352 pattern = 1 := by simpa only [d81, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c125 pattern childGuard
    simpa only [d81, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d352 pattern = 1 := by simpa only [d81, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c126 pattern childGuard
    simpa only [d81, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c128 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c129 (pattern : Ten) (guard : d351 pattern = 1) : d221 pattern ≤ (0 : Int) + d171 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d351, d221, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c28 pattern childGuard
    simpa only [d351, d221, d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d351, d221, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c128 pattern childGuard
    simpa only [d351, d221, d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c130 (pattern : Ten) (guard : d0 pattern = 1) : d0 pattern ≤ (0 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c131 (pattern : Ten) (guard : d351 pattern = 1) : d0 pattern ≤ (0 : Int) + d171 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d351, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c28 pattern childGuard
    simpa only [d351, d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d351, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c130 pattern childGuard
    simpa only [d351, d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c132 (pattern : Ten) (guard : d351 pattern = 1) : d222 pattern ≤ (0 : Int) + d171 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c129 pattern childGuard
    simpa only [d222, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c131 pattern childGuard
    simpa only [d222, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c133 (pattern : Ten) (guard : d351 pattern = 1) : d223 pattern ≤ (0 : Int) + d171 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c132 pattern childGuard
    simpa only [d223, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c131 pattern childGuard
    simpa only [d223, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c134 (pattern : Ten) (guard : d351 pattern = 1) : d12 pattern ≤ (0 : Int) + d173 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d12, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c131 pattern childGuard
    simpa only [d12, d173, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d12, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c35 pattern childGuard
    simpa only [d12, d173, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c135 (pattern : Ten) (guard : d351 pattern = 1) : d224 pattern ≤ (0 : Int) + d176 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d224, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c133 pattern childGuard
    simpa only [d224, d176, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d224, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c134 pattern childGuard
    simpa only [d224, d176, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c136 (pattern : Ten) (guard : d351 pattern = 1) : d18 pattern ≤ (0 : Int) + d177 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d18, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c134 pattern childGuard
    simpa only [d18, d177, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d18, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c35 pattern childGuard
    simpa only [d18, d177, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c137 (pattern : Ten) (guard : d351 pattern = 1) : d225 pattern ≤ (0 : Int) + d180 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d225, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c135 pattern childGuard
    simpa only [d225, d180, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d225, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c136 pattern childGuard
    simpa only [d225, d180, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c138 (pattern : Ten) (guard : d351 pattern = 1) : d26 pattern ≤ (0 : Int) + d181 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d26, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c136 pattern childGuard
    simpa only [d26, d181, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d26, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c35 pattern childGuard
    simpa only [d26, d181, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c139 (pattern : Ten) (guard : d351 pattern = 1) : d226 pattern ≤ (0 : Int) + d184 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d226, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c137 pattern childGuard
    simpa only [d226, d184, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d226, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c138 pattern childGuard
    simpa only [d226, d184, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c140 (pattern : Ten) (guard : d0 pattern = 1) : d2 pattern ≤ (0 : Int) + d3 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c141 (pattern : Ten) (guard : d351 pattern = 1) : d2 pattern ≤ (0 : Int) + d172 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d351, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c42 pattern childGuard
    simpa only [d351, d172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d351, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c140 pattern childGuard
    simpa only [d351, d172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c142 (pattern : Ten) (guard : d351 pattern = 1) : d15 pattern ≤ (0 : Int) + d174 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c131 pattern childGuard
    simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c141 pattern childGuard
    simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c143 (pattern : Ten) (guard : d351 pattern = 1) : d16 pattern ≤ (0 : Int) + d175 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d16, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c141 pattern childGuard
    simpa only [d16, d175, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d16, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c35 pattern childGuard
    simpa only [d16, d175, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c144 (pattern : Ten) (guard : d351 pattern = 1) : d21 pattern ≤ (0 : Int) + d178 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d21, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c142 pattern childGuard
    simpa only [d21, d178, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d21, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c143 pattern childGuard
    simpa only [d21, d178, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c145 (pattern : Ten) (guard : d351 pattern = 1) : d22 pattern ≤ (0 : Int) + d179 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d22, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c143 pattern childGuard
    simpa only [d22, d179, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d22, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c35 pattern childGuard
    simpa only [d22, d179, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c146 (pattern : Ten) (guard : d351 pattern = 1) : d25 pattern ≤ (0 : Int) + d182 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d25, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c144 pattern childGuard
    simpa only [d25, d182, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d25, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c145 pattern childGuard
    simpa only [d25, d182, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c147 (pattern : Ten) (guard : d351 pattern = 1) : d227 pattern ≤ (0 : Int) + d185 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d227, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c146 pattern childGuard
    simpa only [d227, d185, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d227, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c138 pattern childGuard
    simpa only [d227, d185, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c148 (pattern : Ten) (guard : d351 pattern = 1) : d230 pattern ≤ (0 : Int) + d188 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d230, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c139 pattern childGuard
    simpa only [d230, d188, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d230, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c147 pattern childGuard
    simpa only [d230, d188, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c149 (pattern : Ten) (guard : d351 pattern = 1) : d228 pattern ≤ (0 : Int) + d186 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d228, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c138 pattern childGuard
    simpa only [d228, d186, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d228, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c35 pattern childGuard
    simpa only [d228, d186, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c150 (pattern : Ten) (guard : d351 pattern = 1) : d28 pattern ≤ (0 : Int) + d183 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d28, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c145 pattern childGuard
    simpa only [d28, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d28, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c35 pattern childGuard
    simpa only [d28, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c151 (pattern : Ten) (guard : d351 pattern = 1) : d229 pattern ≤ (0 : Int) + d187 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d229, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c150 pattern childGuard
    simpa only [d229, d187, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d229, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c35 pattern childGuard
    simpa only [d229, d187, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c152 (pattern : Ten) (guard : d351 pattern = 1) : d231 pattern ≤ (0 : Int) + d189 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d231, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c149 pattern childGuard
    simpa only [d231, d189, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d231, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c151 pattern childGuard
    simpa only [d231, d189, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c153 (pattern : Ten) (guard : d351 pattern = 1) : d232 pattern ≤ (0 : Int) + d190 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d232, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c148 pattern childGuard
    simpa only [d232, d190, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d232, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c152 pattern childGuard
    simpa only [d232, d190, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c154 (pattern : Ten) (guard : d351 pattern = 1) : d233 pattern ≤ (0 : Int) + d191 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d233, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c152 pattern childGuard
    simpa only [d233, d191, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d233, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c35 pattern childGuard
    simpa only [d233, d191, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c155 (pattern : Ten) (guard : d351 pattern = 1) : d234 pattern ≤ (0 : Int) + d192 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d234, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c153 pattern childGuard
    simpa only [d234, d192, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d234, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c154 pattern childGuard
    simpa only [d234, d192, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c156 (pattern : Ten) (guard : d359 pattern = 1) : d23 pattern ≤ (0 : Int) + d23 pattern := by
  omega
theorem c157 (pattern : Ten) (guard : d359 pattern = 1) : d0 pattern ≤ (0 : Int) + d0 pattern := by
  omega
theorem c158 (pattern : Ten) (guard : d356 pattern = 1) : d9 pattern ≤ (0 : Int) + d9 pattern := by
  omega
theorem c159 (pattern : Ten) (guard : d358 pattern = 1) : d9 pattern ≤ (0 : Int) + d11 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d356 pattern = 1 := by simpa only [d358, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c158 pattern childGuard
    simpa only [d358, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d358, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c109 pattern childGuard
    simpa only [d358, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban41.Diagram
