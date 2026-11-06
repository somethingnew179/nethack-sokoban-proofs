/- Staged soko4-1 certificate. No result until all kernel checks pass. -/
import NetHack.Sokoban41.Comparisons13
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem c2240 (pattern : Ten) (guard : d1 pattern = 1) : d172 pattern ≤ (8 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2238 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2239 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2241 (pattern : Ten) (guard : d1 pattern = 1) : d174 pattern ≤ (8 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2237 pattern childGuard
    simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2240 pattern childGuard
    simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2242 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (8 : Int) + d10 pattern := by
  change (4 : Int) ≤ (8 : Int) + 10
  decide
theorem c2243 (pattern : Ten) (guard : d1 pattern = 1) : d5 pattern ≤ (8 : Int) + d10 pattern := by
  change (5 : Int) ≤ (8 : Int) + 10
  decide
theorem c2244 (pattern : Ten) (guard : d1 pattern = 1) : d193 pattern ≤ (8 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2242 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2243 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2245 (pattern : Ten) (guard : d1 pattern = 1) : d10 pattern ≤ (8 : Int) + d10 pattern := by
  omega
theorem c2246 (pattern : Ten) (guard : d1 pattern = 1) : d197 pattern ≤ (8 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2244 pattern childGuard
    simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2245 pattern childGuard
    simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2247 (pattern : Ten) (guard : d1 pattern = 1) : d202 pattern ≤ (8 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2241 pattern childGuard
    simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2246 pattern childGuard
    simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2248 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (8 : Int) + d10 pattern := by
  change (6 : Int) ≤ (8 : Int) + 10
  decide
theorem c2249 (pattern : Ten) (guard : d1 pattern = 1) : d7 pattern ≤ (8 : Int) + d10 pattern := by
  change (7 : Int) ≤ (8 : Int) + 10
  decide
theorem c2250 (pattern : Ten) (guard : d1 pattern = 1) : d194 pattern ≤ (8 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2248 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2249 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2251 (pattern : Ten) (guard : d1 pattern = 1) : d198 pattern ≤ (8 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2250 pattern childGuard
    simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2245 pattern childGuard
    simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2252 (pattern : Ten) (guard : d1 pattern = 1) : d203 pattern ≤ (8 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2251 pattern childGuard
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2245 pattern childGuard
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2253 (pattern : Ten) (guard : d1 pattern = 1) : d207 pattern ≤ (8 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2247 pattern childGuard
    simpa only [d207, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2252 pattern childGuard
    simpa only [d207, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2254 (pattern : Ten) (guard : d355 pattern = 1) : d207 pattern ≤ (8 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2234 pattern childGuard
    simpa only [d355, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2253 pattern childGuard
    simpa only [d355, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2255 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (8 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2256 (pattern : Ten) (guard : d436 pattern = 1) : d290 pattern ≤ (8 : Int) + d10 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d355 pattern = 1 := by simpa only [d436, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2254 pattern childGuard
    simpa only [d436, d290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d436, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2255 pattern childGuard
    simpa only [d436, d290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2257 (pattern : Ten) (guard : d0 pattern = 1) : d209 pattern ≤ (8 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2258 (pattern : Ten) (guard : d1 pattern = 1) : d8 pattern ≤ (8 : Int) + d10 pattern := by
  change (8 : Int) ≤ (8 : Int) + 10
  decide
theorem c2259 (pattern : Ten) (guard : d1 pattern = 1) : d9 pattern ≤ (8 : Int) + d10 pattern := by
  change (9 : Int) ≤ (8 : Int) + 10
  decide
theorem c2260 (pattern : Ten) (guard : d1 pattern = 1) : d195 pattern ≤ (8 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2258 pattern childGuard
    simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2259 pattern childGuard
    simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2261 (pattern : Ten) (guard : d1 pattern = 1) : d200 pattern ≤ (8 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2260 pattern childGuard
    simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2245 pattern childGuard
    simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2262 (pattern : Ten) (guard : d1 pattern = 1) : d205 pattern ≤ (8 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2261 pattern childGuard
    simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2245 pattern childGuard
    simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2263 (pattern : Ten) (guard : d1 pattern = 1) : d209 pattern ≤ (8 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2262 pattern childGuard
    simpa only [d209, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2245 pattern childGuard
    simpa only [d209, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2264 (pattern : Ten) (guard : d355 pattern = 1) : d209 pattern ≤ (8 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2257 pattern childGuard
    simpa only [d355, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2263 pattern childGuard
    simpa only [d355, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2265 (pattern : Ten) (guard : d436 pattern = 1) : d209 pattern ≤ (8 : Int) + d10 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d355 pattern = 1 := by simpa only [d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2264 pattern childGuard
    simpa only [d436, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2257 pattern childGuard
    simpa only [d436, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2266 (pattern : Ten) (guard : d436 pattern = 1) : d291 pattern ≤ (8 : Int) + d10 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d436 pattern = 1 := by simpa only [d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2256 pattern childGuard
    simpa only [d291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d436 pattern = 1 := by simpa only [d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2265 pattern childGuard
    simpa only [d291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2267 (pattern : Ten) (guard : d0 pattern = 1) : d58 pattern ≤ (8 : Int) + d211 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2268 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (8 : Int) + d0 pattern := by
  change (2 : Int) ≤ (8 : Int) + 0
  decide
theorem c2269 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (8 : Int) + d1 pattern := by
  change (2 : Int) ≤ (8 : Int) + 1
  decide
theorem c2270 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (8 : Int) + d171 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2268 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2269 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2271 (pattern : Ten) (guard : d0 pattern = 1) : d2 pattern ≤ (8 : Int) + d171 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2272 (pattern : Ten) (guard : d350 pattern = 1) : d2 pattern ≤ (8 : Int) + d171 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2270 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2271 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2273 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (8 : Int) + d2 pattern := by
  change (4 : Int) ≤ (8 : Int) + 2
  decide
theorem c2274 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (8 : Int) + d3 pattern := by
  change (4 : Int) ≤ (8 : Int) + 3
  decide
theorem c2275 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (8 : Int) + d172 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2273 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2274 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2276 (pattern : Ten) (guard : d0 pattern = 1) : d4 pattern ≤ (8 : Int) + d172 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2277 (pattern : Ten) (guard : d350 pattern = 1) : d4 pattern ≤ (8 : Int) + d172 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2275 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2276 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2278 (pattern : Ten) (guard : d350 pattern = 1) : d44 pattern ≤ (8 : Int) + d174 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d44, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2272 pattern childGuard
    simpa only [d44, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d44, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2277 pattern childGuard
    simpa only [d44, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2279 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (8 : Int) + d4 pattern := by
  change (6 : Int) ≤ (8 : Int) + 4
  decide
theorem c2280 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (8 : Int) + d5 pattern := by
  change (6 : Int) ≤ (8 : Int) + 5
  decide
theorem c2281 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (8 : Int) + d193 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2279 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2280 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2282 (pattern : Ten) (guard : d0 pattern = 1) : d6 pattern ≤ (8 : Int) + d193 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2283 (pattern : Ten) (guard : d350 pattern = 1) : d6 pattern ≤ (8 : Int) + d193 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2281 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2282 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2284 (pattern : Ten) (guard : d350 pattern = 1) : d43 pattern ≤ (8 : Int) + d197 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d43, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2283 pattern childGuard
    simpa only [d43, d197, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d43, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2205 pattern childGuard
    simpa only [d43, d197, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2285 (pattern : Ten) (guard : d350 pattern = 1) : d50 pattern ≤ (8 : Int) + d202 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d50, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2278 pattern childGuard
    simpa only [d50, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d50, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2284 pattern childGuard
    simpa only [d50, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2286 (pattern : Ten) (guard : d1 pattern = 1) : d8 pattern ≤ (8 : Int) + d6 pattern := by
  change (8 : Int) ≤ (8 : Int) + 6
  decide
theorem c2287 (pattern : Ten) (guard : d1 pattern = 1) : d8 pattern ≤ (8 : Int) + d7 pattern := by
  change (8 : Int) ≤ (8 : Int) + 7
  decide
theorem c2288 (pattern : Ten) (guard : d1 pattern = 1) : d8 pattern ≤ (8 : Int) + d194 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2286 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2287 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2289 (pattern : Ten) (guard : d0 pattern = 1) : d8 pattern ≤ (8 : Int) + d194 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2290 (pattern : Ten) (guard : d350 pattern = 1) : d8 pattern ≤ (8 : Int) + d194 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2288 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2289 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2291 (pattern : Ten) (guard : d350 pattern = 1) : d45 pattern ≤ (8 : Int) + d198 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d45, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2290 pattern childGuard
    simpa only [d45, d198, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d45, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2205 pattern childGuard
    simpa only [d45, d198, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2292 (pattern : Ten) (guard : d350 pattern = 1) : d51 pattern ≤ (8 : Int) + d203 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d51, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2291 pattern childGuard
    simpa only [d51, d203, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d51, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2205 pattern childGuard
    simpa only [d51, d203, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2293 (pattern : Ten) (guard : d350 pattern = 1) : d55 pattern ≤ (8 : Int) + d207 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d55, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2285 pattern childGuard
    simpa only [d55, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d55, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2292 pattern childGuard
    simpa only [d55, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2294 (pattern : Ten) (guard : d1 pattern = 1) : d11 pattern ≤ (8 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2259 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2245 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2295 (pattern : Ten) (guard : d0 pattern = 1) : d11 pattern ≤ (8 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2296 (pattern : Ten) (guard : d350 pattern = 1) : d11 pattern ≤ (8 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2294 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2295 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2297 (pattern : Ten) (guard : d350 pattern = 1) : d14 pattern ≤ (8 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2296 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2205 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2298 (pattern : Ten) (guard : d350 pattern = 1) : d20 pattern ≤ (8 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2297 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2205 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2299 (pattern : Ten) (guard : d350 pattern = 1) : d27 pattern ≤ (8 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2298 pattern childGuard
    simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2205 pattern childGuard
    simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2300 (pattern : Ten) (guard : d350 pattern = 1) : d59 pattern ≤ (8 : Int) + d211 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d59, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2293 pattern childGuard
    simpa only [d59, d211, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d59, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2299 pattern childGuard
    simpa only [d59, d211, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2301 (pattern : Ten) (guard : d432 pattern = 1) : d62 pattern ≤ (8 : Int) + d211 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d432, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2267 pattern childGuard
    simpa only [d432, d62, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d432, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2300 pattern childGuard
    simpa only [d432, d62, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2302 (pattern : Ten) (guard : d432 pattern = 1) : d64 pattern ≤ (8 : Int) + d434 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d432 pattern = 1 := by simpa only [d64, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2216 pattern childGuard
    simpa only [d64, d434, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d432 pattern = 1 := by simpa only [d64, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2301 pattern childGuard
    simpa only [d64, d434, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2303 (pattern : Ten) (guard : d0 pattern = 1) : d60 pattern ≤ (8 : Int) + d214 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2304 (pattern : Ten) (guard : d1 pattern = 1) : d9 pattern ≤ (8 : Int) + d8 pattern := by
  change (9 : Int) ≤ (8 : Int) + 8
  decide
theorem c2305 (pattern : Ten) (guard : d1 pattern = 1) : d10 pattern ≤ (8 : Int) + d8 pattern := by
  change (10 : Int) ≤ (8 : Int) + 8
  decide
theorem c2306 (pattern : Ten) (guard : d1 pattern = 1) : d39 pattern ≤ (8 : Int) + d8 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2304 pattern childGuard
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2305 pattern childGuard
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2307 (pattern : Ten) (guard : d1 pattern = 1) : d10 pattern ≤ (8 : Int) + d9 pattern := by
  change (10 : Int) ≤ (8 : Int) + 9
  decide
theorem c2308 (pattern : Ten) (guard : d1 pattern = 1) : d41 pattern ≤ (8 : Int) + d195 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2306 pattern childGuard
    simpa only [d41, d195, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2307 pattern childGuard
    simpa only [d41, d195, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2309 (pattern : Ten) (guard : d0 pattern = 1) : d41 pattern ≤ (8 : Int) + d195 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2310 (pattern : Ten) (guard : d350 pattern = 1) : d41 pattern ≤ (8 : Int) + d195 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2308 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2309 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2311 (pattern : Ten) (guard : d350 pattern = 1) : d47 pattern ≤ (8 : Int) + d200 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d47, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2310 pattern childGuard
    simpa only [d47, d200, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d47, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2205 pattern childGuard
    simpa only [d47, d200, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2312 (pattern : Ten) (guard : d350 pattern = 1) : d53 pattern ≤ (8 : Int) + d205 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d53, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2311 pattern childGuard
    simpa only [d53, d205, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d53, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2205 pattern childGuard
    simpa only [d53, d205, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2313 (pattern : Ten) (guard : d350 pattern = 1) : d57 pattern ≤ (8 : Int) + d209 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d57, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2312 pattern childGuard
    simpa only [d57, d209, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d57, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2205 pattern childGuard
    simpa only [d57, d209, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2314 (pattern : Ten) (guard : d350 pattern = 1) : d61 pattern ≤ (8 : Int) + d214 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d61, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2313 pattern childGuard
    simpa only [d61, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d61, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2205 pattern childGuard
    simpa only [d61, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2315 (pattern : Ten) (guard : d432 pattern = 1) : d63 pattern ≤ (8 : Int) + d214 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d432, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2303 pattern childGuard
    simpa only [d432, d63, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d432, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2314 pattern childGuard
    simpa only [d432, d63, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2316 (pattern : Ten) (guard : d432 pattern = 1) : d65 pattern ≤ (8 : Int) + d237 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d432 pattern = 1 := by simpa only [d65, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2230 pattern childGuard
    simpa only [d65, d237, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d432 pattern = 1 := by simpa only [d65, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2315 pattern childGuard
    simpa only [d65, d237, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2317 (pattern : Ten) (guard : d432 pattern = 1) : d66 pattern ≤ (8 : Int) + d435 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d432 pattern = 1 := by simpa only [d66, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2302 pattern childGuard
    simpa only [d66, d435, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d432 pattern = 1 := by simpa only [d66, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2316 pattern childGuard
    simpa only [d66, d435, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2318 (pattern : Ten) (guard : d0 pattern = 1) : d211 pattern ≤ (8 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2319 (pattern : Ten) (guard : d1 pattern = 1) : d199 pattern ≤ (8 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2240 pattern childGuard
    simpa only [d199, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2244 pattern childGuard
    simpa only [d199, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2320 (pattern : Ten) (guard : d1 pattern = 1) : d204 pattern ≤ (8 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2319 pattern childGuard
    simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2251 pattern childGuard
    simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2321 (pattern : Ten) (guard : d1 pattern = 1) : d208 pattern ≤ (8 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2320 pattern childGuard
    simpa only [d208, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2262 pattern childGuard
    simpa only [d208, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2322 (pattern : Ten) (guard : d1 pattern = 1) : d212 pattern ≤ (8 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2321 pattern childGuard
    simpa only [d212, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2245 pattern childGuard
    simpa only [d212, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2323 (pattern : Ten) (guard : d355 pattern = 1) : d215 pattern ≤ (8 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d355, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2318 pattern childGuard
    simpa only [d355, d215, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d355, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2322 pattern childGuard
    simpa only [d355, d215, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2324 (pattern : Ten) (guard : d355 pattern = 1) : d218 pattern ≤ (8 : Int) + d10 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d355 pattern = 1 := by simpa only [d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2254 pattern childGuard
    simpa only [d218, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d355 pattern = 1 := by simpa only [d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2323 pattern childGuard
    simpa only [d218, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2325 (pattern : Ten) (guard : d1 pattern = 1) : d196 pattern ≤ (8 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2260 pattern childGuard
    simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2294 pattern childGuard
    simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2326 (pattern : Ten) (guard : d1 pattern = 1) : d201 pattern ≤ (8 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2325 pattern childGuard
    simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2245 pattern childGuard
    simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2327 (pattern : Ten) (guard : d1 pattern = 1) : d206 pattern ≤ (8 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2326 pattern childGuard
    simpa only [d206, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2245 pattern childGuard
    simpa only [d206, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2328 (pattern : Ten) (guard : d1 pattern = 1) : d210 pattern ≤ (8 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2327 pattern childGuard
    simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2245 pattern childGuard
    simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2329 (pattern : Ten) (guard : d1 pattern = 1) : d213 pattern ≤ (8 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2263 pattern childGuard
    simpa only [d213, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2328 pattern childGuard
    simpa only [d213, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2330 (pattern : Ten) (guard : d355 pattern = 1) : d216 pattern ≤ (8 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d355, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2257 pattern childGuard
    simpa only [d355, d216, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d355, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2329 pattern childGuard
    simpa only [d355, d216, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2331 (pattern : Ten) (guard : d0 pattern = 1) : d214 pattern ≤ (8 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2332 (pattern : Ten) (guard : d355 pattern = 1) : d217 pattern ≤ (8 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d355, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2331 pattern childGuard
    simpa only [d355, d217, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d355, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2245 pattern childGuard
    simpa only [d355, d217, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2333 (pattern : Ten) (guard : d355 pattern = 1) : d219 pattern ≤ (8 : Int) + d10 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d355 pattern = 1 := by simpa only [d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2330 pattern childGuard
    simpa only [d219, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d355 pattern = 1 := by simpa only [d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2332 pattern childGuard
    simpa only [d219, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2334 (pattern : Ten) (guard : d355 pattern = 1) : d220 pattern ≤ (8 : Int) + d10 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d355 pattern = 1 := by simpa only [d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2324 pattern childGuard
    simpa only [d220, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d355 pattern = 1 := by simpa only [d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2333 pattern childGuard
    simpa only [d220, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2335 (pattern : Ten) (guard : d0 pattern = 1) : d54 pattern ≤ (0 : Int) + d58 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2336 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) ≤ (0 : Int) + 10
  decide
theorem c2337 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (0 : Int) + d11 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2166 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2336 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2338 (pattern : Ten) (guard : d350 pattern = 1) : d0 pattern ≤ (0 : Int) + d11 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2337 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c607 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2339 (pattern : Ten) (guard : d350 pattern = 1) : d15 pattern ≤ (0 : Int) + d14 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2338 pattern childGuard
    simpa only [d15, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2116 pattern childGuard
    simpa only [d15, d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2340 (pattern : Ten) (guard : d350 pattern = 1) : d48 pattern ≤ (0 : Int) + d20 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d48, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2339 pattern childGuard
    simpa only [d48, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d48, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2119 pattern childGuard
    simpa only [d48, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2341 (pattern : Ten) (guard : d350 pattern = 1) : d54 pattern ≤ (0 : Int) + d27 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d54, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2340 pattern childGuard
    simpa only [d54, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d54, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2123 pattern childGuard
    simpa only [d54, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2342 (pattern : Ten) (guard : d350 pattern = 1) : d54 pattern ≤ (0 : Int) + d58 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c61 pattern childGuard
    simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2341 pattern childGuard
    simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2343 (pattern : Ten) (guard : d432 pattern = 1) : d54 pattern ≤ (0 : Int) + d58 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2335 pattern childGuard
    simpa only [d432, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2342 pattern childGuard
    simpa only [d432, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2344 (pattern : Ten) (guard : d0 pattern = 1) : d62 pattern ≤ (0 : Int) + d58 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2345 (pattern : Ten) (guard : d433 pattern = 1) : d64 pattern ≤ (0 : Int) + d58 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d432 pattern = 1 := by simpa only [d433, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2343 pattern childGuard
    simpa only [d433, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d433, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2344 pattern childGuard
    simpa only [d433, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2346 (pattern : Ten) (guard : d1 pattern = 1) : d38 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2161 pattern childGuard
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2178 pattern childGuard
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2347 (pattern : Ten) (guard : d1 pattern = 1) : d40 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2346 pattern childGuard
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2178 pattern childGuard
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2348 (pattern : Ten) (guard : d0 pattern = 1) : d40 pattern ≤ (0 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2349 (pattern : Ten) (guard : d350 pattern = 1) : d40 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2347 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2348 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2350 (pattern : Ten) (guard : d350 pattern = 1) : d46 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2349 pattern childGuard
    simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c322 pattern childGuard
    simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2351 (pattern : Ten) (guard : d350 pattern = 1) : d52 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2350 pattern childGuard
    simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c322 pattern childGuard
    simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2352 (pattern : Ten) (guard : d350 pattern = 1) : d56 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2351 pattern childGuard
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c322 pattern childGuard
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2353 (pattern : Ten) (guard : d350 pattern = 1) : d56 pattern ≤ (0 : Int) + d60 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c331 pattern childGuard
    simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2352 pattern childGuard
    simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2354 (pattern : Ten) (guard : d432 pattern = 1) : d56 pattern ≤ (0 : Int) + d60 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c899 pattern childGuard
    simpa only [d432, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2353 pattern childGuard
    simpa only [d432, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2355 (pattern : Ten) (guard : d0 pattern = 1) : d63 pattern ≤ (0 : Int) + d60 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2356 (pattern : Ten) (guard : d433 pattern = 1) : d65 pattern ≤ (0 : Int) + d60 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d432 pattern = 1 := by simpa only [d433, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2354 pattern childGuard
    simpa only [d433, d65, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d433, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2355 pattern childGuard
    simpa only [d433, d65, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2357 (pattern : Ten) (guard : d433 pattern = 1) : d66 pattern ≤ (0 : Int) + d437 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d433 pattern = 1 := by simpa only [d66, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2345 pattern childGuard
    simpa only [d66, d437, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d433 pattern = 1 := by simpa only [d66, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2356 pattern childGuard
    simpa only [d66, d437, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2358 (pattern : Ten) (guard : d0 pattern = 1) : d207 pattern ≤ (0 : Int) + d211 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2359 (pattern : Ten) (guard : d1 pattern = 1) : d171 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2336 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2167 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2360 (pattern : Ten) (guard : d1 pattern = 1) : d174 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2359 pattern childGuard
    simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2153 pattern childGuard
    simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2361 (pattern : Ten) (guard : d1 pattern = 1) : d202 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2360 pattern childGuard
    simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2158 pattern childGuard
    simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2362 (pattern : Ten) (guard : d1 pattern = 1) : d207 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2361 pattern childGuard
    simpa only [d207, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2164 pattern childGuard
    simpa only [d207, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2363 (pattern : Ten) (guard : d1 pattern = 1) : d207 pattern ≤ (0 : Int) + d211 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c74 pattern childGuard
    simpa only [d211, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2362 pattern childGuard
    simpa only [d211, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2364 (pattern : Ten) (guard : d355 pattern = 1) : d207 pattern ≤ (0 : Int) + d211 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2358 pattern childGuard
    simpa only [d355, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2363 pattern childGuard
    simpa only [d355, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2365 (pattern : Ten) (guard : d0 pattern = 1) : d215 pattern ≤ (0 : Int) + d211 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2366 (pattern : Ten) (guard : d436 pattern = 1) : d218 pattern ≤ (0 : Int) + d211 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d355 pattern = 1 := by simpa only [d436, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2364 pattern childGuard
    simpa only [d436, d218, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d436, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2365 pattern childGuard
    simpa only [d436, d218, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2367 (pattern : Ten) (guard : d1 pattern = 1) : d196 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2179 pattern childGuard
    simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2127 pattern childGuard
    simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2368 (pattern : Ten) (guard : d1 pattern = 1) : d201 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2367 pattern childGuard
    simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2126 pattern childGuard
    simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2369 (pattern : Ten) (guard : d1 pattern = 1) : d206 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2368 pattern childGuard
    simpa only [d206, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2126 pattern childGuard
    simpa only [d206, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2370 (pattern : Ten) (guard : d1 pattern = 1) : d210 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2369 pattern childGuard
    simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2126 pattern childGuard
    simpa only [d210, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2371 (pattern : Ten) (guard : d1 pattern = 1) : d213 pattern ≤ (0 : Int) + d214 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d213, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c81 pattern childGuard
    simpa only [d213, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d213, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2370 pattern childGuard
    simpa only [d213, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2372 (pattern : Ten) (guard : d355 pattern = 1) : d216 pattern ≤ (0 : Int) + d214 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d355, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c904 pattern childGuard
    simpa only [d355, d216, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d355, d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2371 pattern childGuard
    simpa only [d355, d216, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2373 (pattern : Ten) (guard : d0 pattern = 1) : d217 pattern ≤ (0 : Int) + d214 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2374 (pattern : Ten) (guard : d436 pattern = 1) : d219 pattern ≤ (0 : Int) + d214 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d355 pattern = 1 := by simpa only [d436, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2372 pattern childGuard
    simpa only [d436, d219, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d436, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2373 pattern childGuard
    simpa only [d436, d219, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2375 (pattern : Ten) (guard : d436 pattern = 1) : d220 pattern ≤ (0 : Int) + d438 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d436 pattern = 1 := by simpa only [d220, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2366 pattern childGuard
    simpa only [d220, d438, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d436 pattern = 1 := by simpa only [d220, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2374 pattern childGuard
    simpa only [d220, d438, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2376 (pattern : Ten) (guard : d432 pattern = 1) : d54 pattern ≤ (2 : Int) + d54 pattern := by
  omega
theorem c2377 (pattern : Ten) (guard : d0 pattern = 1) : d58 pattern ≤ (2 : Int) + d58 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2378 (pattern : Ten) (guard : d350 pattern = 1) : d2 pattern ≤ (2 : Int) + d0 pattern := by
  change (2 : Int) ≤ (2 : Int) + 0
  decide
theorem c2379 (pattern : Ten) (guard : d350 pattern = 1) : d4 pattern ≤ (2 : Int) + d2 pattern := by
  change (4 : Int) ≤ (2 : Int) + 2
  decide
theorem c2380 (pattern : Ten) (guard : d350 pattern = 1) : d44 pattern ≤ (2 : Int) + d15 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d44, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2378 pattern childGuard
    simpa only [d44, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d44, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2379 pattern childGuard
    simpa only [d44, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2381 (pattern : Ten) (guard : d350 pattern = 1) : d6 pattern ≤ (2 : Int) + d4 pattern := by
  change (6 : Int) ≤ (2 : Int) + 4
  decide
theorem c2382 (pattern : Ten) (guard : d350 pattern = 1) : d43 pattern ≤ (2 : Int) + d42 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d43, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2381 pattern childGuard
    simpa only [d43, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d43, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d43, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2383 (pattern : Ten) (guard : d350 pattern = 1) : d50 pattern ≤ (2 : Int) + d48 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d50, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2380 pattern childGuard
    simpa only [d50, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d50, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2382 pattern childGuard
    simpa only [d50, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2384 (pattern : Ten) (guard : d350 pattern = 1) : d8 pattern ≤ (2 : Int) + d6 pattern := by
  change (8 : Int) ≤ (2 : Int) + 6
  decide
theorem c2385 (pattern : Ten) (guard : d350 pattern = 1) : d45 pattern ≤ (2 : Int) + d43 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d45, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2384 pattern childGuard
    simpa only [d45, d43, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d45, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d45, d43, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2386 (pattern : Ten) (guard : d350 pattern = 1) : d51 pattern ≤ (2 : Int) + d49 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d51, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2385 pattern childGuard
    simpa only [d51, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d51, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d51, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2387 (pattern : Ten) (guard : d350 pattern = 1) : d55 pattern ≤ (2 : Int) + d54 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d55, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2383 pattern childGuard
    simpa only [d55, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d55, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2386 pattern childGuard
    simpa only [d55, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2388 (pattern : Ten) (guard : d350 pattern = 1) : d27 pattern ≤ (2 : Int) + d27 pattern := by
  omega
theorem c2389 (pattern : Ten) (guard : d350 pattern = 1) : d59 pattern ≤ (2 : Int) + d58 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d59, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2387 pattern childGuard
    simpa only [d59, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d59, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2388 pattern childGuard
    simpa only [d59, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2390 (pattern : Ten) (guard : d432 pattern = 1) : d62 pattern ≤ (2 : Int) + d58 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d432, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2377 pattern childGuard
    simpa only [d432, d62, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d432, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2389 pattern childGuard
    simpa only [d432, d62, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2391 (pattern : Ten) (guard : d432 pattern = 1) : d64 pattern ≤ (2 : Int) + d439 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d432 pattern = 1 := by simpa only [d64, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2376 pattern childGuard
    simpa only [d64, d439, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d432 pattern = 1 := by simpa only [d64, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2390 pattern childGuard
    simpa only [d64, d439, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2392 (pattern : Ten) (guard : d432 pattern = 1) : d56 pattern ≤ (2 : Int) + d56 pattern := by
  omega
theorem c2393 (pattern : Ten) (guard : d0 pattern = 1) : d60 pattern ≤ (2 : Int) + d60 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2394 (pattern : Ten) (guard : d1 pattern = 1) : d9 pattern ≤ (2 : Int) + d7 pattern := by
  change (9 : Int) ≤ (2 : Int) + 7
  decide
theorem c2395 (pattern : Ten) (guard : d1 pattern = 1) : d10 pattern ≤ (2 : Int) + d8 pattern := by
  change (10 : Int) ≤ (2 : Int) + 8
  decide
theorem c2396 (pattern : Ten) (guard : d1 pattern = 1) : d39 pattern ≤ (2 : Int) + d38 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2394 pattern childGuard
    simpa only [d39, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2395 pattern childGuard
    simpa only [d39, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2397 (pattern : Ten) (guard : d1 pattern = 1) : d41 pattern ≤ (2 : Int) + d40 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2396 pattern childGuard
    simpa only [d41, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2395 pattern childGuard
    simpa only [d41, d40, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2398 (pattern : Ten) (guard : d0 pattern = 1) : d41 pattern ≤ (2 : Int) + d40 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2399 (pattern : Ten) (guard : d350 pattern = 1) : d41 pattern ≤ (2 : Int) + d40 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2397 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2398 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban41.Diagram
