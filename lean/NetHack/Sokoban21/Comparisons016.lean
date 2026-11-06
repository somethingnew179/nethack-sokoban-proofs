/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons015
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c2240 (pattern : Twelve) (guard : d1858 pattern = 1) : d335 pattern ≤ (0 : Int) + d468 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d335, d468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2238 pattern childGuard
    simpa only [d335, d468, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d335, d468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2239 pattern childGuard
    simpa only [d335, d468, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2241 (pattern : Twelve) (guard : d1858 pattern = 1) : d339 pattern ≤ (0 : Int) + d472 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d339, d472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2229 pattern childGuard
    simpa only [d339, d472, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d339, d472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2240 pattern childGuard
    simpa only [d339, d472, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2242 (pattern : Twelve) (guard : d1858 pattern = 1) : d341 pattern ≤ (0 : Int) + d474 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d341, d474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2214 pattern childGuard
    simpa only [d341, d474, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d341, d474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2241 pattern childGuard
    simpa only [d341, d474, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2243 (pattern : Twelve) (guard : d0 pattern = 1) : d53 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2244 (pattern : Twelve) (guard : d1852 pattern = 1) : d74 pattern ≤ (0 : Int) + d439 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d74, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2180 pattern childGuard
    simpa only [d1852, d74, d439, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d74, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2243 pattern childGuard
    simpa only [d1852, d74, d439, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2245 (pattern : Twelve) (guard : d1858 pattern = 1) : d316 pattern ≤ (0 : Int) + d451 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d316, d451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2244 pattern childGuard
    simpa only [d1858, d316, d451, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d316, d451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2221 pattern childGuard
    simpa only [d1858, d316, d451, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2246 (pattern : Twelve) (guard : d1858 pattern = 1) : d328 pattern ≤ (0 : Int) + d459 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d328, d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2218 pattern childGuard
    simpa only [d328, d459, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d328, d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2245 pattern childGuard
    simpa only [d328, d459, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2247 (pattern : Twelve) (guard : d0 pattern = 1) : d57 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2248 (pattern : Twelve) (guard : d1852 pattern = 1) : d77 pattern ≤ (0 : Int) + d432 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d77, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2190 pattern childGuard
    simpa only [d1852, d77, d432, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d77, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2247 pattern childGuard
    simpa only [d1852, d77, d432, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2249 (pattern : Twelve) (guard : d1858 pattern = 1) : d317 pattern ≤ (0 : Int) + d432 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2248 pattern childGuard
    simpa only [d1858, d317, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2226 pattern childGuard
    simpa only [d1858, d317, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2250 (pattern : Twelve) (guard : d1858 pattern = 1) : d329 pattern ≤ (0 : Int) + d460 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d329, d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2218 pattern childGuard
    simpa only [d329, d460, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d329, d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2249 pattern childGuard
    simpa only [d329, d460, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2251 (pattern : Twelve) (guard : d1858 pattern = 1) : d336 pattern ≤ (0 : Int) + d467 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d336, d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2246 pattern childGuard
    simpa only [d336, d467, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d336, d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2250 pattern childGuard
    simpa only [d336, d467, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2252 (pattern : Twelve) (guard : d0 pattern = 1) : d58 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2253 (pattern : Twelve) (guard : d1852 pattern = 1) : d79 pattern ≤ (0 : Int) + d441 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d79, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1852, d79, d441, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d79, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2252 pattern childGuard
    simpa only [d1852, d79, d441, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2254 (pattern : Twelve) (guard : d1858 pattern = 1) : d318 pattern ≤ (0 : Int) + d441 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2253 pattern childGuard
    simpa only [d1858, d318, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2232 pattern childGuard
    simpa only [d1858, d318, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2255 (pattern : Twelve) (guard : d0 pattern = 1) : d60 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2256 (pattern : Twelve) (guard : d1852 pattern = 1) : d81 pattern ≤ (0 : Int) + d436 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d81, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2201 pattern childGuard
    simpa only [d1852, d81, d436, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d81, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2255 pattern childGuard
    simpa only [d1852, d81, d436, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2257 (pattern : Twelve) (guard : d1858 pattern = 1) : d319 pattern ≤ (0 : Int) + d436 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2256 pattern childGuard
    simpa only [d1858, d319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2236 pattern childGuard
    simpa only [d1858, d319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2258 (pattern : Twelve) (guard : d1858 pattern = 1) : d330 pattern ≤ (0 : Int) + d461 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d330, d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2254 pattern childGuard
    simpa only [d330, d461, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d330, d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2257 pattern childGuard
    simpa only [d330, d461, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2259 (pattern : Twelve) (guard : d1858 pattern = 1) : d331 pattern ≤ (0 : Int) + d462 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d331, d462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2249 pattern childGuard
    simpa only [d331, d462, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d331, d462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2211 pattern childGuard
    simpa only [d331, d462, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2260 (pattern : Twelve) (guard : d1858 pattern = 1) : d337 pattern ≤ (0 : Int) + d468 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d337, d468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2258 pattern childGuard
    simpa only [d337, d468, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d337, d468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2259 pattern childGuard
    simpa only [d337, d468, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2261 (pattern : Twelve) (guard : d1858 pattern = 1) : d340 pattern ≤ (0 : Int) + d472 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d340, d472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2251 pattern childGuard
    simpa only [d340, d472, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d340, d472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2260 pattern childGuard
    simpa only [d340, d472, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2262 (pattern : Twelve) (guard : d1858 pattern = 1) : d342 pattern ≤ (0 : Int) + d472 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2261 pattern childGuard
    simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2241 pattern childGuard
    simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2263 (pattern : Twelve) (guard : d1858 pattern = 1) : d343 pattern ≤ (0 : Int) + d475 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d343, d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2242 pattern childGuard
    simpa only [d343, d475, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d343, d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2262 pattern childGuard
    simpa only [d343, d475, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2264 (pattern : Twelve) (guard : d1858 pattern = 1) : d316 pattern ≤ (0 : Int) + d452 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d316, d452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2244 pattern childGuard
    simpa only [d1858, d316, d452, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d316, d452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2226 pattern childGuard
    simpa only [d1858, d316, d452, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2265 (pattern : Twelve) (guard : d1858 pattern = 1) : d328 pattern ≤ (0 : Int) + d463 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d328, d463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2218 pattern childGuard
    simpa only [d328, d463, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d328, d463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2264 pattern childGuard
    simpa only [d328, d463, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2266 (pattern : Twelve) (guard : d1858 pattern = 1) : d336 pattern ≤ (0 : Int) + d469 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d336, d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2265 pattern childGuard
    simpa only [d336, d469, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d336, d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2250 pattern childGuard
    simpa only [d336, d469, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2267 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d442 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2268 (pattern : Twelve) (guard : d1858 pattern = 1) : d318 pattern ≤ (0 : Int) + d453 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d318, d453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2253 pattern childGuard
    simpa only [d1858, d318, d453, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d318, d453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2267 pattern childGuard
    simpa only [d1858, d318, d453, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2269 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d443 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2270 (pattern : Twelve) (guard : d1858 pattern = 1) : d319 pattern ≤ (0 : Int) + d454 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d319, d454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2256 pattern childGuard
    simpa only [d1858, d319, d454, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d319, d454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2269 pattern childGuard
    simpa only [d1858, d319, d454, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2271 (pattern : Twelve) (guard : d1858 pattern = 1) : d330 pattern ≤ (0 : Int) + d464 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d330, d464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2268 pattern childGuard
    simpa only [d330, d464, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d330, d464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2270 pattern childGuard
    simpa only [d330, d464, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2272 (pattern : Twelve) (guard : d1858 pattern = 1) : d337 pattern ≤ (0 : Int) + d470 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d337, d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2271 pattern childGuard
    simpa only [d337, d470, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d337, d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2259 pattern childGuard
    simpa only [d337, d470, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2273 (pattern : Twelve) (guard : d1858 pattern = 1) : d340 pattern ≤ (0 : Int) + d473 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d340, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2266 pattern childGuard
    simpa only [d340, d473, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d340, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2272 pattern childGuard
    simpa only [d340, d473, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2274 (pattern : Twelve) (guard : d1858 pattern = 1) : d312 pattern ≤ (0 : Int) + d452 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d312, d452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2220 pattern childGuard
    simpa only [d1858, d312, d452, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d312, d452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2226 pattern childGuard
    simpa only [d1858, d312, d452, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2275 (pattern : Twelve) (guard : d1858 pattern = 1) : d324 pattern ≤ (0 : Int) + d463 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d324, d463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2218 pattern childGuard
    simpa only [d324, d463, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d324, d463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2274 pattern childGuard
    simpa only [d324, d463, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2276 (pattern : Twelve) (guard : d1858 pattern = 1) : d334 pattern ≤ (0 : Int) + d469 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d334, d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2275 pattern childGuard
    simpa only [d334, d469, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d334, d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2228 pattern childGuard
    simpa only [d334, d469, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2277 (pattern : Twelve) (guard : d1858 pattern = 1) : d314 pattern ≤ (0 : Int) + d453 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d314, d453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2231 pattern childGuard
    simpa only [d1858, d314, d453, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d314, d453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2267 pattern childGuard
    simpa only [d1858, d314, d453, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2278 (pattern : Twelve) (guard : d1858 pattern = 1) : d315 pattern ≤ (0 : Int) + d454 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d315, d454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2235 pattern childGuard
    simpa only [d1858, d315, d454, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d315, d454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2269 pattern childGuard
    simpa only [d1858, d315, d454, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2279 (pattern : Twelve) (guard : d1858 pattern = 1) : d326 pattern ≤ (0 : Int) + d464 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d326, d464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2277 pattern childGuard
    simpa only [d326, d464, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d326, d464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2278 pattern childGuard
    simpa only [d326, d464, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2280 (pattern : Twelve) (guard : d1858 pattern = 1) : d335 pattern ≤ (0 : Int) + d470 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d335, d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2279 pattern childGuard
    simpa only [d335, d470, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d335, d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2239 pattern childGuard
    simpa only [d335, d470, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2281 (pattern : Twelve) (guard : d1858 pattern = 1) : d339 pattern ≤ (0 : Int) + d473 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d339, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2276 pattern childGuard
    simpa only [d339, d473, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d339, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2280 pattern childGuard
    simpa only [d339, d473, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2282 (pattern : Twelve) (guard : d1858 pattern = 1) : d342 pattern ≤ (0 : Int) + d473 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2273 pattern childGuard
    simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2281 pattern childGuard
    simpa only [d342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2283 (pattern : Twelve) (guard : d1858 pattern = 1) : d344 pattern ≤ (0 : Int) + d476 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d344, d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2263 pattern childGuard
    simpa only [d344, d476, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d344, d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2282 pattern childGuard
    simpa only [d344, d476, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2284 (pattern : Twelve) (guard : d0 pattern = 1) : d824 pattern ≤ (0 : Int) + d186 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2285 (pattern : Twelve) (guard : d1852 pattern = 1) : d838 pattern ≤ (0 : Int) + d426 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d838, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1852, d838, d426, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d838, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2284 pattern childGuard
    simpa only [d1852, d838, d426, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2286 (pattern : Twelve) (guard : d0 pattern = 1) : d909 pattern ≤ (0 : Int) + d1070 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2287 (pattern : Twelve) (guard : d1858 pattern = 1) : d980 pattern ≤ (0 : Int) + d1078 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d980, d1078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2285 pattern childGuard
    simpa only [d1858, d980, d1078, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d980, d1078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2286 pattern childGuard
    simpa only [d1858, d980, d1078, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2288 (pattern : Twelve) (guard : d0 pattern = 1) : d826 pattern ≤ (0 : Int) + d189 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2289 (pattern : Twelve) (guard : d1852 pattern = 1) : d840 pattern ≤ (0 : Int) + d1071 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d840, d1071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2190 pattern childGuard
    simpa only [d1852, d840, d1071, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d840, d1071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2288 pattern childGuard
    simpa only [d1852, d840, d1071, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2290 (pattern : Twelve) (guard : d0 pattern = 1) : d910 pattern ≤ (0 : Int) + d1072 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2291 (pattern : Twelve) (guard : d1858 pattern = 1) : d981 pattern ≤ (0 : Int) + d1079 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d981, d1079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2289 pattern childGuard
    simpa only [d1858, d981, d1079, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d981, d1079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2290 pattern childGuard
    simpa only [d1858, d981, d1079, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2292 (pattern : Twelve) (guard : d1858 pattern = 1) : d991 pattern ≤ (0 : Int) + d1088 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d991, d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2287 pattern childGuard
    simpa only [d991, d1088, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d991, d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2291 pattern childGuard
    simpa only [d991, d1088, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2293 (pattern : Twelve) (guard : d0 pattern = 1) : d824 pattern ≤ (0 : Int) + d189 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2294 (pattern : Twelve) (guard : d1852 pattern = 1) : d838 pattern ≤ (0 : Int) + d430 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d838, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1852, d838, d430, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d838, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2293 pattern childGuard
    simpa only [d1852, d838, d430, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2295 (pattern : Twelve) (guard : d0 pattern = 1) : d910 pattern ≤ (0 : Int) + d1073 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2296 (pattern : Twelve) (guard : d1858 pattern = 1) : d982 pattern ≤ (0 : Int) + d1080 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d982, d1080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2294 pattern childGuard
    simpa only [d1858, d982, d1080, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d982, d1080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2295 pattern childGuard
    simpa only [d1858, d982, d1080, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2297 (pattern : Twelve) (guard : d0 pattern = 1) : d826 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2298 (pattern : Twelve) (guard : d1852 pattern = 1) : d840 pattern ≤ (0 : Int) + d432 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d840, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2190 pattern childGuard
    simpa only [d1852, d840, d432, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d840, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2297 pattern childGuard
    simpa only [d1852, d840, d432, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2299 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1072 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2300 (pattern : Twelve) (guard : d1858 pattern = 1) : d983 pattern ≤ (0 : Int) + d1081 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d983, d1081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2298 pattern childGuard
    simpa only [d1858, d983, d1081, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d983, d1081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2299 pattern childGuard
    simpa only [d1858, d983, d1081, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2301 (pattern : Twelve) (guard : d1858 pattern = 1) : d992 pattern ≤ (0 : Int) + d1089 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d992, d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2296 pattern childGuard
    simpa only [d992, d1089, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d992, d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2300 pattern childGuard
    simpa only [d992, d1089, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2302 (pattern : Twelve) (guard : d1858 pattern = 1) : d1000 pattern ≤ (0 : Int) + d1095 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1000, d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2292 pattern childGuard
    simpa only [d1000, d1095, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1000, d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2301 pattern childGuard
    simpa only [d1000, d1095, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2303 (pattern : Twelve) (guard : d0 pattern = 1) : d828 pattern ≤ (0 : Int) + d194 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2304 (pattern : Twelve) (guard : d1852 pattern = 1) : d842 pattern ≤ (0 : Int) + d434 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d842, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1852, d842, d434, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d842, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2303 pattern childGuard
    simpa only [d1852, d842, d434, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2305 (pattern : Twelve) (guard : d0 pattern = 1) : d911 pattern ≤ (0 : Int) + d1074 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2306 (pattern : Twelve) (guard : d1858 pattern = 1) : d984 pattern ≤ (0 : Int) + d1082 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d984, d1082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2304 pattern childGuard
    simpa only [d1858, d984, d1082, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d984, d1082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2305 pattern childGuard
    simpa only [d1858, d984, d1082, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2307 (pattern : Twelve) (guard : d0 pattern = 1) : d829 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2308 (pattern : Twelve) (guard : d1852 pattern = 1) : d844 pattern ≤ (0 : Int) + d436 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d844, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2201 pattern childGuard
    simpa only [d1852, d844, d436, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d844, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2307 pattern childGuard
    simpa only [d1852, d844, d436, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2309 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1075 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2310 (pattern : Twelve) (guard : d1858 pattern = 1) : d985 pattern ≤ (0 : Int) + d1083 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d985, d1083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2308 pattern childGuard
    simpa only [d1858, d985, d1083, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d985, d1083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2309 pattern childGuard
    simpa only [d1858, d985, d1083, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2311 (pattern : Twelve) (guard : d1858 pattern = 1) : d993 pattern ≤ (0 : Int) + d1090 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d993, d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2306 pattern childGuard
    simpa only [d993, d1090, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d993, d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2310 pattern childGuard
    simpa only [d993, d1090, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2312 (pattern : Twelve) (guard : d1858 pattern = 1) : d994 pattern ≤ (0 : Int) + d1091 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d994, d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2300 pattern childGuard
    simpa only [d994, d1091, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d994, d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2211 pattern childGuard
    simpa only [d994, d1091, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2313 (pattern : Twelve) (guard : d1858 pattern = 1) : d1001 pattern ≤ (0 : Int) + d1096 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1001, d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2311 pattern childGuard
    simpa only [d1001, d1096, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1001, d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2312 pattern childGuard
    simpa only [d1001, d1096, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2314 (pattern : Twelve) (guard : d1858 pattern = 1) : d1004 pattern ≤ (0 : Int) + d1099 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1004, d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2302 pattern childGuard
    simpa only [d1004, d1099, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1004, d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2313 pattern childGuard
    simpa only [d1004, d1099, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2315 (pattern : Twelve) (guard : d0 pattern = 1) : d824 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2316 (pattern : Twelve) (guard : d1852 pattern = 1) : d838 pattern ≤ (0 : Int) + d438 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d838, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1852, d838, d438, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d838, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2315 pattern childGuard
    simpa only [d1852, d838, d438, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2317 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1073 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2318 (pattern : Twelve) (guard : d1858 pattern = 1) : d986 pattern ≤ (0 : Int) + d1084 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d986, d1084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2316 pattern childGuard
    simpa only [d1858, d986, d1084, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d986, d1084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2317 pattern childGuard
    simpa only [d1858, d986, d1084, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2319 (pattern : Twelve) (guard : d0 pattern = 1) : d832 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2320 (pattern : Twelve) (guard : d1852 pattern = 1) : d847 pattern ≤ (0 : Int) + d432 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d847, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2190 pattern childGuard
    simpa only [d1852, d847, d432, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d847, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2319 pattern childGuard
    simpa only [d1852, d847, d432, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2321 (pattern : Twelve) (guard : d1858 pattern = 1) : d987 pattern ≤ (0 : Int) + d1081 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d987, d1081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2320 pattern childGuard
    simpa only [d1858, d987, d1081, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d987, d1081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2299 pattern childGuard
    simpa only [d1858, d987, d1081, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2322 (pattern : Twelve) (guard : d1858 pattern = 1) : d995 pattern ≤ (0 : Int) + d1092 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d995, d1092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2318 pattern childGuard
    simpa only [d995, d1092, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d995, d1092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2321 pattern childGuard
    simpa only [d995, d1092, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2323 (pattern : Twelve) (guard : d0 pattern = 1) : d834 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2324 (pattern : Twelve) (guard : d1852 pattern = 1) : d849 pattern ≤ (0 : Int) + d441 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d849, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1852, d849, d441, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d849, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2323 pattern childGuard
    simpa only [d1852, d849, d441, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2325 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1074 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2326 (pattern : Twelve) (guard : d1858 pattern = 1) : d988 pattern ≤ (0 : Int) + d1085 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d988, d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2324 pattern childGuard
    simpa only [d1858, d988, d1085, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d988, d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2325 pattern childGuard
    simpa only [d1858, d988, d1085, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2327 (pattern : Twelve) (guard : d0 pattern = 1) : d836 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2328 (pattern : Twelve) (guard : d1852 pattern = 1) : d851 pattern ≤ (0 : Int) + d436 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d851, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2201 pattern childGuard
    simpa only [d1852, d851, d436, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d851, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2327 pattern childGuard
    simpa only [d1852, d851, d436, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2329 (pattern : Twelve) (guard : d1858 pattern = 1) : d989 pattern ≤ (0 : Int) + d1083 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d989, d1083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2328 pattern childGuard
    simpa only [d1858, d989, d1083, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d989, d1083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2309 pattern childGuard
    simpa only [d1858, d989, d1083, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2330 (pattern : Twelve) (guard : d1858 pattern = 1) : d996 pattern ≤ (0 : Int) + d1093 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d996, d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2326 pattern childGuard
    simpa only [d996, d1093, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d996, d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2329 pattern childGuard
    simpa only [d996, d1093, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2331 (pattern : Twelve) (guard : d1858 pattern = 1) : d997 pattern ≤ (0 : Int) + d1091 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d997, d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2321 pattern childGuard
    simpa only [d997, d1091, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d997, d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2211 pattern childGuard
    simpa only [d997, d1091, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2332 (pattern : Twelve) (guard : d1858 pattern = 1) : d1002 pattern ≤ (0 : Int) + d1097 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1002, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2330 pattern childGuard
    simpa only [d1002, d1097, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1002, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2331 pattern childGuard
    simpa only [d1002, d1097, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2333 (pattern : Twelve) (guard : d1858 pattern = 1) : d1005 pattern ≤ (0 : Int) + d1100 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1005, d1100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2322 pattern childGuard
    simpa only [d1005, d1100, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1005, d1100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2332 pattern childGuard
    simpa only [d1005, d1100, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2334 (pattern : Twelve) (guard : d1858 pattern = 1) : d1007 pattern ≤ (0 : Int) + d1102 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1007, d1102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2314 pattern childGuard
    simpa only [d1007, d1102, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1007, d1102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2333 pattern childGuard
    simpa only [d1007, d1102, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2335 (pattern : Twelve) (guard : d1858 pattern = 1) : d998 pattern ≤ (0 : Int) + d1092 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d998, d1092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2318 pattern childGuard
    simpa only [d998, d1092, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d998, d1092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2300 pattern childGuard
    simpa only [d998, d1092, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2336 (pattern : Twelve) (guard : d0 pattern = 1) : d828 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2337 (pattern : Twelve) (guard : d1852 pattern = 1) : d842 pattern ≤ (0 : Int) + d441 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d842, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1852, d842, d441, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d842, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2336 pattern childGuard
    simpa only [d1852, d842, d441, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2338 (pattern : Twelve) (guard : d1858 pattern = 1) : d990 pattern ≤ (0 : Int) + d1085 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d990, d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2337 pattern childGuard
    simpa only [d1858, d990, d1085, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d990, d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2325 pattern childGuard
    simpa only [d1858, d990, d1085, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2339 (pattern : Twelve) (guard : d1858 pattern = 1) : d999 pattern ≤ (0 : Int) + d1093 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d999, d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2338 pattern childGuard
    simpa only [d999, d1093, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d999, d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2310 pattern childGuard
    simpa only [d999, d1093, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2340 (pattern : Twelve) (guard : d1858 pattern = 1) : d1003 pattern ≤ (0 : Int) + d1097 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1003, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2339 pattern childGuard
    simpa only [d1003, d1097, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1003, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2312 pattern childGuard
    simpa only [d1003, d1097, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2341 (pattern : Twelve) (guard : d1858 pattern = 1) : d1006 pattern ≤ (0 : Int) + d1100 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1006, d1100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2335 pattern childGuard
    simpa only [d1006, d1100, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1006, d1100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2340 pattern childGuard
    simpa only [d1006, d1100, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2342 (pattern : Twelve) (guard : d1858 pattern = 1) : d1008 pattern ≤ (0 : Int) + d1100 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2341 pattern childGuard
    simpa only [d1008, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2333 pattern childGuard
    simpa only [d1008, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2343 (pattern : Twelve) (guard : d1858 pattern = 1) : d1009 pattern ≤ (0 : Int) + d1103 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1009, d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2334 pattern childGuard
    simpa only [d1009, d1103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1009, d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2342 pattern childGuard
    simpa only [d1009, d1103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2344 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1076 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2345 (pattern : Twelve) (guard : d1858 pattern = 1) : d990 pattern ≤ (0 : Int) + d1086 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d990, d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2337 pattern childGuard
    simpa only [d1858, d990, d1086, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d990, d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2344 pattern childGuard
    simpa only [d1858, d990, d1086, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2346 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1077 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2347 (pattern : Twelve) (guard : d1858 pattern = 1) : d985 pattern ≤ (0 : Int) + d1087 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d985, d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2308 pattern childGuard
    simpa only [d1858, d985, d1087, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d985, d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2346 pattern childGuard
    simpa only [d1858, d985, d1087, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2348 (pattern : Twelve) (guard : d1858 pattern = 1) : d999 pattern ≤ (0 : Int) + d1094 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d999, d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2345 pattern childGuard
    simpa only [d999, d1094, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d999, d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2347 pattern childGuard
    simpa only [d999, d1094, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2349 (pattern : Twelve) (guard : d1858 pattern = 1) : d1003 pattern ≤ (0 : Int) + d1098 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1003, d1098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2348 pattern childGuard
    simpa only [d1003, d1098, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1003, d1098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2312 pattern childGuard
    simpa only [d1003, d1098, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2350 (pattern : Twelve) (guard : d1858 pattern = 1) : d1006 pattern ≤ (0 : Int) + d1101 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1006, d1101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2335 pattern childGuard
    simpa only [d1006, d1101, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1006, d1101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2349 pattern childGuard
    simpa only [d1006, d1101, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2351 (pattern : Twelve) (guard : d1858 pattern = 1) : d988 pattern ≤ (0 : Int) + d1086 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d988, d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2324 pattern childGuard
    simpa only [d1858, d988, d1086, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d988, d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2344 pattern childGuard
    simpa only [d1858, d988, d1086, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2352 (pattern : Twelve) (guard : d1858 pattern = 1) : d989 pattern ≤ (0 : Int) + d1087 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d989, d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2328 pattern childGuard
    simpa only [d1858, d989, d1087, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d989, d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2346 pattern childGuard
    simpa only [d1858, d989, d1087, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2353 (pattern : Twelve) (guard : d1858 pattern = 1) : d996 pattern ≤ (0 : Int) + d1094 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d996, d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2351 pattern childGuard
    simpa only [d996, d1094, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d996, d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2352 pattern childGuard
    simpa only [d996, d1094, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2354 (pattern : Twelve) (guard : d1858 pattern = 1) : d1002 pattern ≤ (0 : Int) + d1098 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1002, d1098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2353 pattern childGuard
    simpa only [d1002, d1098, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1002, d1098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2331 pattern childGuard
    simpa only [d1002, d1098, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2355 (pattern : Twelve) (guard : d1858 pattern = 1) : d1005 pattern ≤ (0 : Int) + d1101 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1005, d1101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2322 pattern childGuard
    simpa only [d1005, d1101, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1005, d1101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2354 pattern childGuard
    simpa only [d1005, d1101, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2356 (pattern : Twelve) (guard : d1858 pattern = 1) : d1008 pattern ≤ (0 : Int) + d1101 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2350 pattern childGuard
    simpa only [d1008, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2355 pattern childGuard
    simpa only [d1008, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2357 (pattern : Twelve) (guard : d1858 pattern = 1) : d1010 pattern ≤ (0 : Int) + d1104 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1010, d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2343 pattern childGuard
    simpa only [d1010, d1104, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1010, d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2356 pattern childGuard
    simpa only [d1010, d1104, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2358 (pattern : Twelve) (guard : d0 pattern = 1) : d1284 pattern ≤ (0 : Int) + d908 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2359 (pattern : Twelve) (guard : d1852 pattern = 1) : d1293 pattern ≤ (0 : Int) + d1070 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1293, d1070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1852, d1293, d1070, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1293, d1070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2358 pattern childGuard
    simpa only [d1852, d1293, d1070, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2360 (pattern : Twelve) (guard : d1858 pattern = 1) : d1412 pattern ≤ (0 : Int) + d1472 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d1412, d1472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2359 pattern childGuard
    simpa only [d1858, d1412, d1472, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d1412, d1472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2129 pattern childGuard
    simpa only [d1858, d1412, d1472, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2361 (pattern : Twelve) (guard : d1 pattern = 1) : d827 pattern ≤ (0 : Int) + d827 pattern := by
  omega
theorem c2362 (pattern : Twelve) (guard : d0 pattern = 1) : d1285 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2363 (pattern : Twelve) (guard : d1852 pattern = 1) : d1295 pattern ≤ (0 : Int) + d1072 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1295, d1072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2361 pattern childGuard
    simpa only [d1852, d1295, d1072, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1295, d1072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2362 pattern childGuard
    simpa only [d1852, d1295, d1072, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2364 (pattern : Twelve) (guard : d1858 pattern = 1) : d1413 pattern ≤ (0 : Int) + d1473 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d1413, d1473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2363 pattern childGuard
    simpa only [d1858, d1413, d1473, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d1413, d1473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2131 pattern childGuard
    simpa only [d1858, d1413, d1473, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2365 (pattern : Twelve) (guard : d1858 pattern = 1) : d1417 pattern ≤ (0 : Int) + d1479 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1417, d1479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2360 pattern childGuard
    simpa only [d1417, d1479, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1417, d1479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2364 pattern childGuard
    simpa only [d1417, d1479, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2366 (pattern : Twelve) (guard : d0 pattern = 1) : d1284 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2367 (pattern : Twelve) (guard : d1852 pattern = 1) : d1293 pattern ≤ (0 : Int) + d1073 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1293, d1073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1852, d1293, d1073, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1293, d1073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2366 pattern childGuard
    simpa only [d1852, d1293, d1073, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2368 (pattern : Twelve) (guard : d1858 pattern = 1) : d1414 pattern ≤ (0 : Int) + d1474 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d1414, d1474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2367 pattern childGuard
    simpa only [d1858, d1414, d1474, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d1414, d1474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2134 pattern childGuard
    simpa only [d1858, d1414, d1474, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2369 (pattern : Twelve) (guard : d1858 pattern = 1) : d1418 pattern ≤ (0 : Int) + d1480 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1418, d1480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2368 pattern childGuard
    simpa only [d1418, d1480, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1418, d1480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2364 pattern childGuard
    simpa only [d1418, d1480, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2370 (pattern : Twelve) (guard : d1858 pattern = 1) : d1421 pattern ≤ (0 : Int) + d1484 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1421, d1484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2365 pattern childGuard
    simpa only [d1421, d1484, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1421, d1484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2369 pattern childGuard
    simpa only [d1421, d1484, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2371 (pattern : Twelve) (guard : d0 pattern = 1) : d1287 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2372 (pattern : Twelve) (guard : d1852 pattern = 1) : d1297 pattern ≤ (0 : Int) + d1074 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1297, d1074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c100 pattern childGuard
    simpa only [d1852, d1297, d1074, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1297, d1074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2371 pattern childGuard
    simpa only [d1852, d1297, d1074, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2373 (pattern : Twelve) (guard : d1858 pattern = 1) : d1415 pattern ≤ (0 : Int) + d1475 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d1415, d1475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2372 pattern childGuard
    simpa only [d1858, d1415, d1475, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d1415, d1475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2138 pattern childGuard
    simpa only [d1858, d1415, d1475, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2374 (pattern : Twelve) (guard : d1 pattern = 1) : d830 pattern ≤ (0 : Int) + d830 pattern := by
  omega
theorem c2375 (pattern : Twelve) (guard : d0 pattern = 1) : d1288 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2376 (pattern : Twelve) (guard : d1852 pattern = 1) : d1299 pattern ≤ (0 : Int) + d1075 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1299, d1075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2374 pattern childGuard
    simpa only [d1852, d1299, d1075, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1299, d1075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2375 pattern childGuard
    simpa only [d1852, d1299, d1075, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2377 (pattern : Twelve) (guard : d1858 pattern = 1) : d1416 pattern ≤ (0 : Int) + d1476 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d1416, d1476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2376 pattern childGuard
    simpa only [d1858, d1416, d1476, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d1416, d1476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2140 pattern childGuard
    simpa only [d1858, d1416, d1476, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2378 (pattern : Twelve) (guard : d1858 pattern = 1) : d1419 pattern ≤ (0 : Int) + d1481 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1419, d1481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2373 pattern childGuard
    simpa only [d1419, d1481, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1419, d1481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2377 pattern childGuard
    simpa only [d1419, d1481, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2379 (pattern : Twelve) (guard : d1858 pattern = 1) : d1420 pattern ≤ (0 : Int) + d1482 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1420, d1482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2364 pattern childGuard
    simpa only [d1420, d1482, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d1420, d1482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2211 pattern childGuard
    simpa only [d1420, d1482, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
