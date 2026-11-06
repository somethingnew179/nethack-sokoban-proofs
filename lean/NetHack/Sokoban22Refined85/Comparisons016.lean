/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons015
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare2240 (p : Pattern) (guard : d1 p = 1) : d94 p ≤ (0 : Int) + d94 p := by
  omega
theorem compare2241 (p : Pattern) (guard : d0 p = 1) : d95 p ≤ (0 : Int) + d411 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2242 (p : Pattern) (guard : d4077 p = 1) : d96 p ≤ (0 : Int) + d657 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d96, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2240 p hg
    simpa only [d4077, d96, d657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d96, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2241 p hg
    simpa only [d4077, d96, d657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2243 (p : Pattern) (guard : d4077 p = 1) : d97 p ≤ (0 : Int) + d658 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d97, d658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2239 p hg
    simpa only [d97, d658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d97, d658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2242 p hg
    simpa only [d97, d658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2244 (p : Pattern) (guard : d4077 p = 1) : d98 p ≤ (0 : Int) + d659 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d98, d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2237 p hg
    simpa only [d98, d659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d98, d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2243 p hg
    simpa only [d98, d659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2245 (p : Pattern) (guard : d0 p = 1) : d76 p ≤ (0 : Int) + d397 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2246 (p : Pattern) (guard : d4077 p = 1) : d77 p ≤ (0 : Int) + d660 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d77, d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2231 p hg
    simpa only [d4077, d77, d660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d77, d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2245 p hg
    simpa only [d4077, d77, d660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2247 (p : Pattern) (guard : d0 p = 1) : d86 p ≤ (0 : Int) + d421 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2248 (p : Pattern) (guard : d4077 p = 1) : d87 p ≤ (0 : Int) + d661 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d87, d661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2234 p hg
    simpa only [d4077, d87, d661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d87, d661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2247 p hg
    simpa only [d4077, d87, d661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2249 (p : Pattern) (guard : d4077 p = 1) : d88 p ≤ (0 : Int) + d662 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d88, d662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2246 p hg
    simpa only [d88, d662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d88, d662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2248 p hg
    simpa only [d88, d662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2250 (p : Pattern) (guard : d0 p = 1) : d86 p ≤ (0 : Int) + d410 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2251 (p : Pattern) (guard : d4077 p = 1) : d87 p ≤ (0 : Int) + d663 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d87, d663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2234 p hg
    simpa only [d4077, d87, d663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d87, d663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2250 p hg
    simpa only [d4077, d87, d663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2252 (p : Pattern) (guard : d4077 p = 1) : d99 p ≤ (0 : Int) + d664 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d99, d664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2251 p hg
    simpa only [d99, d664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d99, d664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1242 p hg
    simpa only [d99, d664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2253 (p : Pattern) (guard : d4077 p = 1) : d100 p ≤ (0 : Int) + d665 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d100, d665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2249 p hg
    simpa only [d100, d665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d100, d665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2252 p hg
    simpa only [d100, d665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2254 (p : Pattern) (guard : d4077 p = 1) : d101 p ≤ (0 : Int) + d666 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d101, d666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2244 p hg
    simpa only [d101, d666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d101, d666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2253 p hg
    simpa only [d101, d666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2255 (p : Pattern) (guard : d0 p = 1) : d76 p ≤ (0 : Int) + d418 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2256 (p : Pattern) (guard : d4077 p = 1) : d77 p ≤ (0 : Int) + d667 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d77, d667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2231 p hg
    simpa only [d4077, d77, d667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d77, d667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2255 p hg
    simpa only [d4077, d77, d667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2257 (p : Pattern) (guard : d0 p = 1) : d86 p ≤ (0 : Int) + d420 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2258 (p : Pattern) (guard : d4077 p = 1) : d87 p ≤ (0 : Int) + d668 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d87, d668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2234 p hg
    simpa only [d4077, d87, d668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d87, d668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2257 p hg
    simpa only [d4077, d87, d668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2259 (p : Pattern) (guard : d4077 p = 1) : d88 p ≤ (0 : Int) + d669 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d88, d669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2256 p hg
    simpa only [d88, d669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d88, d669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2258 p hg
    simpa only [d88, d669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2260 (p : Pattern) (guard : d0 p = 1) : d95 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2261 (p : Pattern) (guard : d4077 p = 1) : d96 p ≤ (0 : Int) + d670 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d96, d670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2240 p hg
    simpa only [d4077, d96, d670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d96, d670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2260 p hg
    simpa only [d4077, d96, d670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2262 (p : Pattern) (guard : d4077 p = 1) : d97 p ≤ (0 : Int) + d671 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d97, d671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2236 p hg
    simpa only [d97, d671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d97, d671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2261 p hg
    simpa only [d97, d671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2263 (p : Pattern) (guard : d4077 p = 1) : d98 p ≤ (0 : Int) + d672 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d98, d672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2259 p hg
    simpa only [d98, d672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d98, d672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2262 p hg
    simpa only [d98, d672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2264 (p : Pattern) (guard : d0 p = 1) : d76 p ≤ (0 : Int) + d407 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2265 (p : Pattern) (guard : d4077 p = 1) : d77 p ≤ (0 : Int) + d673 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d77, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2231 p hg
    simpa only [d4077, d77, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d77, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2264 p hg
    simpa only [d4077, d77, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2266 (p : Pattern) (guard : d0 p = 1) : d86 p ≤ (0 : Int) + d411 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2267 (p : Pattern) (guard : d4077 p = 1) : d87 p ≤ (0 : Int) + d674 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d87, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2234 p hg
    simpa only [d4077, d87, d674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d87, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2266 p hg
    simpa only [d4077, d87, d674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2268 (p : Pattern) (guard : d4077 p = 1) : d88 p ≤ (0 : Int) + d675 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d88, d675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2265 p hg
    simpa only [d88, d675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d88, d675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2267 p hg
    simpa only [d88, d675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2269 (p : Pattern) (guard : d4077 p = 1) : d99 p ≤ (0 : Int) + d676 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d99, d676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2248 p hg
    simpa only [d99, d676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d99, d676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1242 p hg
    simpa only [d99, d676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2270 (p : Pattern) (guard : d4077 p = 1) : d100 p ≤ (0 : Int) + d677 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d100, d677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2268 p hg
    simpa only [d100, d677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d100, d677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2269 p hg
    simpa only [d100, d677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2271 (p : Pattern) (guard : d4077 p = 1) : d101 p ≤ (0 : Int) + d678 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d101, d678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2263 p hg
    simpa only [d101, d678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d101, d678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2270 p hg
    simpa only [d101, d678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2272 (p : Pattern) (guard : d4077 p = 1) : d101 p ≤ (0 : Int) + d679 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2254 p hg
    simpa only [d679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2271 p hg
    simpa only [d679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2273 (p : Pattern) (guard : d1 p = 1) : d131 p ≤ (0 : Int) + d131 p := by
  omega
theorem compare2274 (p : Pattern) (guard : d0 p = 1) : d146 p ≤ (0 : Int) + d418 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2275 (p : Pattern) (guard : d4077 p = 1) : d147 p ≤ (0 : Int) + d680 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d147, d680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2273 p hg
    simpa only [d4077, d147, d680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d147, d680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2274 p hg
    simpa only [d4077, d147, d680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2276 (p : Pattern) (guard : d1 p = 1) : d152 p ≤ (0 : Int) + d152 p := by
  omega
theorem compare2277 (p : Pattern) (guard : d0 p = 1) : d156 p ≤ (0 : Int) + d420 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2278 (p : Pattern) (guard : d4077 p = 1) : d157 p ≤ (0 : Int) + d681 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d157, d681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2276 p hg
    simpa only [d4077, d157, d681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d157, d681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2277 p hg
    simpa only [d4077, d157, d681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2279 (p : Pattern) (guard : d4077 p = 1) : d158 p ≤ (0 : Int) + d682 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d158, d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2275 p hg
    simpa only [d158, d682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d158, d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2278 p hg
    simpa only [d158, d682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2280 (p : Pattern) (guard : d0 p = 1) : d156 p ≤ (0 : Int) + d399 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2281 (p : Pattern) (guard : d4077 p = 1) : d157 p ≤ (0 : Int) + d683 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d157, d683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2276 p hg
    simpa only [d4077, d157, d683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d157, d683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2280 p hg
    simpa only [d4077, d157, d683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2282 (p : Pattern) (guard : d4077 p = 1) : d162 p ≤ (0 : Int) + d162 p := by
  omega
theorem compare2283 (p : Pattern) (guard : d4077 p = 1) : d163 p ≤ (0 : Int) + d684 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d163, d684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2281 p hg
    simpa only [d163, d684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d163, d684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2282 p hg
    simpa only [d163, d684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2284 (p : Pattern) (guard : d4077 p = 1) : d164 p ≤ (0 : Int) + d685 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d164, d685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2279 p hg
    simpa only [d164, d685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d164, d685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2283 p hg
    simpa only [d164, d685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2285 (p : Pattern) (guard : d0 p = 1) : d146 p ≤ (0 : Int) + d407 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2286 (p : Pattern) (guard : d4077 p = 1) : d147 p ≤ (0 : Int) + d686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d147, d686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2273 p hg
    simpa only [d4077, d147, d686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d147, d686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2285 p hg
    simpa only [d4077, d147, d686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2287 (p : Pattern) (guard : d0 p = 1) : d156 p ≤ (0 : Int) + d411 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2288 (p : Pattern) (guard : d4077 p = 1) : d157 p ≤ (0 : Int) + d687 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d157, d687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2276 p hg
    simpa only [d4077, d157, d687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d157, d687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2287 p hg
    simpa only [d4077, d157, d687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2289 (p : Pattern) (guard : d4077 p = 1) : d158 p ≤ (0 : Int) + d688 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d158, d688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2286 p hg
    simpa only [d158, d688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d158, d688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2288 p hg
    simpa only [d158, d688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2290 (p : Pattern) (guard : d0 p = 1) : d156 p ≤ (0 : Int) + d421 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2291 (p : Pattern) (guard : d4077 p = 1) : d157 p ≤ (0 : Int) + d689 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d157, d689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2276 p hg
    simpa only [d4077, d157, d689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d157, d689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2290 p hg
    simpa only [d4077, d157, d689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2292 (p : Pattern) (guard : d4077 p = 1) : d165 p ≤ (0 : Int) + d690 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d165, d690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2291 p hg
    simpa only [d165, d690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d165, d690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1242 p hg
    simpa only [d165, d690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2293 (p : Pattern) (guard : d4077 p = 1) : d166 p ≤ (0 : Int) + d691 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d166, d691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2289 p hg
    simpa only [d166, d691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d166, d691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2292 p hg
    simpa only [d166, d691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2294 (p : Pattern) (guard : d4077 p = 1) : d167 p ≤ (0 : Int) + d692 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d167, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2284 p hg
    simpa only [d167, d692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d167, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2293 p hg
    simpa only [d167, d692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2295 (p : Pattern) (guard : d4077 p = 1) : d168 p ≤ (0 : Int) + d693 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d168, d693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2254 p hg
    simpa only [d168, d693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d168, d693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2294 p hg
    simpa only [d168, d693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2296 (p : Pattern) (guard : d4077 p = 1) : d169 p ≤ (0 : Int) + d694 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d169, d694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2272 p hg
    simpa only [d169, d694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d169, d694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2295 p hg
    simpa only [d169, d694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2297 (p : Pattern) (guard : d0 p = 1) : d219 p ≤ (0 : Int) + d453 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2298 (p : Pattern) (guard : d4077 p = 1) : d220 p ≤ (0 : Int) + d695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d220, d695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2273 p hg
    simpa only [d4077, d220, d695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d220, d695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2297 p hg
    simpa only [d4077, d220, d695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2299 (p : Pattern) (guard : d0 p = 1) : d221 p ≤ (0 : Int) + d456 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2300 (p : Pattern) (guard : d4077 p = 1) : d222 p ≤ (0 : Int) + d696 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d222, d696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2276 p hg
    simpa only [d4077, d222, d696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d222, d696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2299 p hg
    simpa only [d4077, d222, d696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2301 (p : Pattern) (guard : d4077 p = 1) : d223 p ≤ (0 : Int) + d697 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d223, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2298 p hg
    simpa only [d223, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d223, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2300 p hg
    simpa only [d223, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2302 (p : Pattern) (guard : d0 p = 1) : d221 p ≤ (0 : Int) + d461 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2303 (p : Pattern) (guard : d4077 p = 1) : d222 p ≤ (0 : Int) + d698 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d222, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2276 p hg
    simpa only [d4077, d222, d698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d222, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2302 p hg
    simpa only [d4077, d222, d698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2304 (p : Pattern) (guard : d4077 p = 1) : d224 p ≤ (0 : Int) + d699 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d224, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2303 p hg
    simpa only [d224, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d224, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2282 p hg
    simpa only [d224, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2305 (p : Pattern) (guard : d4077 p = 1) : d225 p ≤ (0 : Int) + d700 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d225, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2301 p hg
    simpa only [d225, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d225, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2304 p hg
    simpa only [d225, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2306 (p : Pattern) (guard : d1 p = 1) : d281 p ≤ (0 : Int) + d281 p := by
  omega
theorem compare2307 (p : Pattern) (guard : d0 p = 1) : d289 p ≤ (0 : Int) + d471 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2308 (p : Pattern) (guard : d4077 p = 1) : d290 p ≤ (0 : Int) + d701 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d290, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2306 p hg
    simpa only [d4077, d290, d701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d290, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2307 p hg
    simpa only [d4077, d290, d701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2309 (p : Pattern) (guard : d1 p = 1) : d297 p ≤ (0 : Int) + d297 p := by
  omega
theorem compare2310 (p : Pattern) (guard : d0 p = 1) : d304 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2311 (p : Pattern) (guard : d4077 p = 1) : d305 p ≤ (0 : Int) + d702 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4077, d305, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2309 p hg
    simpa only [d4077, d305, d702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4077, d305, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2310 p hg
    simpa only [d4077, d305, d702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2312 (p : Pattern) (guard : d4077 p = 1) : d306 p ≤ (0 : Int) + d703 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d306, d703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2308 p hg
    simpa only [d306, d703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d306, d703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2311 p hg
    simpa only [d306, d703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2313 (p : Pattern) (guard : d4077 p = 1) : d307 p ≤ (0 : Int) + d704 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d307, d704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2311 p hg
    simpa only [d307, d704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d307, d704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1242 p hg
    simpa only [d307, d704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2314 (p : Pattern) (guard : d4077 p = 1) : d308 p ≤ (0 : Int) + d705 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d308, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2312 p hg
    simpa only [d308, d705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d308, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2313 p hg
    simpa only [d308, d705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2315 (p : Pattern) (guard : d4077 p = 1) : d309 p ≤ (0 : Int) + d706 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d309, d706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2305 p hg
    simpa only [d309, d706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d309, d706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2314 p hg
    simpa only [d309, d706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2316 (p : Pattern) (guard : d4077 p = 1) : d310 p ≤ (0 : Int) + d707 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d310, d707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2254 p hg
    simpa only [d310, d707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d310, d707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2315 p hg
    simpa only [d310, d707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2317 (p : Pattern) (guard : d4077 p = 1) : d311 p ≤ (0 : Int) + d708 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d311, d708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2272 p hg
    simpa only [d311, d708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d311, d708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2316 p hg
    simpa only [d311, d708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2318 (p : Pattern) (guard : d4077 p = 1) : d312 p ≤ (0 : Int) + d709 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4077 p = 1 := by simpa only [d312, d709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2296 p hg
    simpa only [d312, d709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4077 p = 1 := by simpa only [d312, d709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d312, d709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2319 (p : Pattern) (guard : d0 p = 1) : d52 p ≤ (0 : Int) + d4155 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2320 (p : Pattern) (guard : d0 p = 1) : d53 p ≤ (0 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2321 (p : Pattern) (guard : d4148 p = 1) : d54 p ≤ (0 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d4148, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2320 p hg
    simpa only [d4148, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2322 (p : Pattern) (guard : d0 p = 1) : d26 p ≤ (0 : Int) + d20 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2323 (p : Pattern) (guard : d4148 p = 1) : d55 p ≤ (0 : Int) + d20 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare847 p hg
    simpa only [d4148, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2322 p hg
    simpa only [d4148, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2324 (p : Pattern) (guard : d4148 p = 1) : d56 p ≤ (0 : Int) + d4150 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d56, d4150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2321 p hg
    simpa only [d56, d4150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d56, d4150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2323 p hg
    simpa only [d56, d4150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2325 (p : Pattern) (guard : d0 p = 1) : d60 p ≤ (0 : Int) + d20 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2326 (p : Pattern) (guard : d4148 p = 1) : d61 p ≤ (0 : Int) + d20 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare847 p hg
    simpa only [d4148, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2325 p hg
    simpa only [d4148, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2327 (p : Pattern) (guard : d4148 p = 1) : d63 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare734 p hg
    simpa only [d4148, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4148, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2328 (p : Pattern) (guard : d4148 p = 1) : d64 p ≤ (0 : Int) + d1100 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d64, d1100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2326 p hg
    simpa only [d64, d1100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d64, d1100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2327 p hg
    simpa only [d64, d1100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2329 (p : Pattern) (guard : d4148 p = 1) : d65 p ≤ (0 : Int) + d4151 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d65, d4151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2324 p hg
    simpa only [d65, d4151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d65, d4151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2328 p hg
    simpa only [d65, d4151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2330 (p : Pattern) (guard : d1 p = 1) : d37 p ≤ (0 : Int) + d37 p := by
  omega
theorem compare2331 (p : Pattern) (guard : d0 p = 1) : d66 p ≤ (0 : Int) + d37 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2332 (p : Pattern) (guard : d4148 p = 1) : d67 p ≤ (0 : Int) + d37 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2330 p hg
    simpa only [d4148, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2331 p hg
    simpa only [d4148, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2333 (p : Pattern) (guard : d1 p = 1) : d43 p ≤ (0 : Int) + d43 p := by
  omega
theorem compare2334 (p : Pattern) (guard : d0 p = 1) : d48 p ≤ (0 : Int) + d43 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2335 (p : Pattern) (guard : d4148 p = 1) : d68 p ≤ (0 : Int) + d43 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2333 p hg
    simpa only [d4148, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2334 p hg
    simpa only [d4148, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2336 (p : Pattern) (guard : d4148 p = 1) : d69 p ≤ (0 : Int) + d4152 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d69, d4152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2332 p hg
    simpa only [d69, d4152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d69, d4152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2335 p hg
    simpa only [d69, d4152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2337 (p : Pattern) (guard : d0 p = 1) : d70 p ≤ (0 : Int) + d43 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2338 (p : Pattern) (guard : d4148 p = 1) : d71 p ≤ (0 : Int) + d43 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2333 p hg
    simpa only [d4148, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2337 p hg
    simpa only [d4148, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2339 (p : Pattern) (guard : d4148 p = 1) : d73 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare744 p hg
    simpa only [d4148, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4148, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2340 (p : Pattern) (guard : d4148 p = 1) : d74 p ≤ (0 : Int) + d4153 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d74, d4153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2338 p hg
    simpa only [d74, d4153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d74, d4153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2339 p hg
    simpa only [d74, d4153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2341 (p : Pattern) (guard : d4148 p = 1) : d75 p ≤ (0 : Int) + d4154 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d75, d4154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2336 p hg
    simpa only [d75, d4154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d75, d4154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2340 p hg
    simpa only [d75, d4154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2342 (p : Pattern) (guard : d4148 p = 1) : d76 p ≤ (0 : Int) + d4155 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d76, d4155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2329 p hg
    simpa only [d76, d4155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d76, d4155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2341 p hg
    simpa only [d76, d4155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2343 (p : Pattern) (guard : d4149 p = 1) : d77 p ≤ (0 : Int) + d4155 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4149, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2319 p hg
    simpa only [d4149, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4149, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2342 p hg
    simpa only [d4149, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2344 (p : Pattern) (guard : d0 p = 1) : d82 p ≤ (0 : Int) + d4158 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2345 (p : Pattern) (guard : d1 p = 1) : d78 p ≤ (0 : Int) + d78 p := by
  omega
theorem compare2346 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d78 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2347 (p : Pattern) (guard : d4148 p = 1) : d83 p ≤ (0 : Int) + d78 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2345 p hg
    simpa only [d4148, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2346 p hg
    simpa only [d4148, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2348 (p : Pattern) (guard : d4148 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare2349 (p : Pattern) (guard : d4148 p = 1) : d84 p ≤ (0 : Int) + d4156 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d84, d4156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2347 p hg
    simpa only [d84, d4156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d84, d4156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d84, d4156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2350 (p : Pattern) (guard : d4148 p = 1) : d85 p ≤ (0 : Int) + d4157 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d85, d4157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2349 p hg
    simpa only [d85, d4157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d85, d4157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d85, d4157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2351 (p : Pattern) (guard : d4148 p = 1) : d86 p ≤ (0 : Int) + d4158 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d86, d4158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2329 p hg
    simpa only [d86, d4158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d86, d4158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2350 p hg
    simpa only [d86, d4158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2352 (p : Pattern) (guard : d4149 p = 1) : d87 p ≤ (0 : Int) + d4158 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4149, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2344 p hg
    simpa only [d4149, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4149, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2351 p hg
    simpa only [d4149, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2353 (p : Pattern) (guard : d4149 p = 1) : d88 p ≤ (0 : Int) + d4159 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d88, d4159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2343 p hg
    simpa only [d88, d4159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d88, d4159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2352 p hg
    simpa only [d88, d4159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2354 (p : Pattern) (guard : d0 p = 1) : d94 p ≤ (0 : Int) + d4162 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2355 (p : Pattern) (guard : d1 p = 1) : d62 p ≤ (0 : Int) + d62 p := by
  omega
theorem compare2356 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d62 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2357 (p : Pattern) (guard : d4148 p = 1) : d63 p ≤ (0 : Int) + d62 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2355 p hg
    simpa only [d4148, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2356 p hg
    simpa only [d4148, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2358 (p : Pattern) (guard : d4148 p = 1) : d91 p ≤ (0 : Int) + d4160 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d91, d4160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2357 p hg
    simpa only [d91, d4160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d91, d4160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d91, d4160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2359 (p : Pattern) (guard : d4148 p = 1) : d93 p ≤ (0 : Int) + d4161 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d93, d4161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2358 p hg
    simpa only [d93, d4161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d93, d4161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d93, d4161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2360 (p : Pattern) (guard : d4148 p = 1) : d95 p ≤ (0 : Int) + d4162 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d95, d4162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2359 p hg
    simpa only [d95, d4162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d95, d4162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d95, d4162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2361 (p : Pattern) (guard : d4149 p = 1) : d96 p ≤ (0 : Int) + d4162 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4149, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2354 p hg
    simpa only [d4149, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d4149, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2360 p hg
    simpa only [d4149, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2362 (p : Pattern) (guard : d4149 p = 1) : d97 p ≤ (0 : Int) + d4163 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d97, d4163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2352 p hg
    simpa only [d97, d4163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d97, d4163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2361 p hg
    simpa only [d97, d4163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2363 (p : Pattern) (guard : d4149 p = 1) : d98 p ≤ (0 : Int) + d4164 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d98, d4164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2353 p hg
    simpa only [d98, d4164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d98, d4164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2362 p hg
    simpa only [d98, d4164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2364 (p : Pattern) (guard : d4149 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare2365 (p : Pattern) (guard : d4149 p = 1) : d99 p ≤ (0 : Int) + d4165 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d99, d4165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2352 p hg
    simpa only [d99, d4165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d99, d4165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2364 p hg
    simpa only [d99, d4165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2366 (p : Pattern) (guard : d4149 p = 1) : d100 p ≤ (0 : Int) + d4166 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d100, d4166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2353 p hg
    simpa only [d100, d4166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d100, d4166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2365 p hg
    simpa only [d100, d4166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2367 (p : Pattern) (guard : d4149 p = 1) : d101 p ≤ (0 : Int) + d4167 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4149 p = 1 := by simpa only [d101, d4167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2363 p hg
    simpa only [d101, d4167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4149 p = 1 := by simpa only [d101, d4167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2366 p hg
    simpa only [d101, d4167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2368 (p : Pattern) (guard : d0 p = 1) : d131 p ≤ (0 : Int) + d4173 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2369 (p : Pattern) (guard : d0 p = 1) : d132 p ≤ (0 : Int) + d105 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2370 (p : Pattern) (guard : d4148 p = 1) : d133 p ≤ (0 : Int) + d105 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1246 p hg
    simpa only [d4148, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2369 p hg
    simpa only [d4148, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2371 (p : Pattern) (guard : d1 p = 1) : d109 p ≤ (0 : Int) + d109 p := by
  omega
theorem compare2372 (p : Pattern) (guard : d0 p = 1) : d60 p ≤ (0 : Int) + d109 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2373 (p : Pattern) (guard : d4148 p = 1) : d134 p ≤ (0 : Int) + d109 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2371 p hg
    simpa only [d4148, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2372 p hg
    simpa only [d4148, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2374 (p : Pattern) (guard : d4148 p = 1) : d135 p ≤ (0 : Int) + d4168 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d135, d4168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2370 p hg
    simpa only [d135, d4168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d135, d4168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2373 p hg
    simpa only [d135, d4168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2375 (p : Pattern) (guard : d0 p = 1) : d62 p ≤ (0 : Int) + d109 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2376 (p : Pattern) (guard : d4148 p = 1) : d136 p ≤ (0 : Int) + d109 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4148, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2371 p hg
    simpa only [d4148, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4148, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2375 p hg
    simpa only [d4148, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2377 (p : Pattern) (guard : d4148 p = 1) : d137 p ≤ (0 : Int) + d1140 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d137, d1140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2376 p hg
    simpa only [d137, d1140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d137, d1140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d137, d1140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2378 (p : Pattern) (guard : d4148 p = 1) : d138 p ≤ (0 : Int) + d4169 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4148 p = 1 := by simpa only [d138, d4169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2374 p hg
    simpa only [d138, d4169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4148 p = 1 := by simpa only [d138, d4169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2377 p hg
    simpa only [d138, d4169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2379 (p : Pattern) (guard : d1 p = 1) : d122 p ≤ (0 : Int) + d122 p := by
  omega
end NetHack.Sokoban22Refined85
