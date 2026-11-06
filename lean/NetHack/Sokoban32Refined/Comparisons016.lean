/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons015
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare2240 (p : Pattern) (guard : d1095 p = 1) : d83 p ≤ (0 : Int) + d526 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d83, d526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1848 p hg
    simpa only [d1095, d83, d526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d83, d526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2239 p hg
    simpa only [d1095, d83, d526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2241 (p : Pattern) (guard : d1095 p = 1) : d117 p ≤ (0 : Int) + d527 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d117, d527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2238 p hg
    simpa only [d117, d527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d117, d527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2240 p hg
    simpa only [d117, d527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2242 (p : Pattern) (guard : d1095 p = 1) : d118 p ≤ (0 : Int) + d528 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d118, d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2236 p hg
    simpa only [d118, d528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d118, d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2241 p hg
    simpa only [d118, d528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2243 (p : Pattern) (guard : d0 p = 1) : d123 p ≤ (0 : Int) + d529 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2244 (p : Pattern) (guard : d1095 p = 1) : d124 p ≤ (0 : Int) + d530 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d124, d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1716 p hg
    simpa only [d1095, d124, d530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d124, d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2243 p hg
    simpa only [d1095, d124, d530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2245 (p : Pattern) (guard : d0 p = 1) : d126 p ≤ (0 : Int) + d126 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2246 (p : Pattern) (guard : d1095 p = 1) : d127 p ≤ (0 : Int) + d531 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d127, d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1856 p hg
    simpa only [d1095, d127, d531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d127, d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2245 p hg
    simpa only [d1095, d127, d531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2247 (p : Pattern) (guard : d1095 p = 1) : d128 p ≤ (0 : Int) + d532 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d128, d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2244 p hg
    simpa only [d128, d532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d128, d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2246 p hg
    simpa only [d128, d532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2248 (p : Pattern) (guard : d1095 p = 1) : d129 p ≤ (0 : Int) + d533 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1095, d129, d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1729 p hg
    simpa only [d1095, d129, d533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, d129, d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2239 p hg
    simpa only [d1095, d129, d533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2249 (p : Pattern) (guard : d1095 p = 1) : d131 p ≤ (0 : Int) + d534 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d131, d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2248 p hg
    simpa only [d131, d534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d131, d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1862 p hg
    simpa only [d131, d534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2250 (p : Pattern) (guard : d1095 p = 1) : d132 p ≤ (0 : Int) + d535 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d132, d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2247 p hg
    simpa only [d132, d535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d132, d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2249 p hg
    simpa only [d132, d535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2251 (p : Pattern) (guard : d1095 p = 1) : d133 p ≤ (0 : Int) + d536 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d133, d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2242 p hg
    simpa only [d133, d536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d133, d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2250 p hg
    simpa only [d133, d536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2252 (p : Pattern) (guard : d1095 p = 1) : d134 p ≤ (0 : Int) + d537 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d134, d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2231 p hg
    simpa only [d134, d537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d134, d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2251 p hg
    simpa only [d134, d537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2253 (p : Pattern) (guard : d0 p = 1) : d28 p ≤ (0 : Int) + d27 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2254 (p : Pattern) (guard : d1 p = 1) : d30 p ≤ (0 : Int) + d17 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d30, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare984 p hg
    simpa only [d30, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d30, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare201 p hg
    simpa only [d30, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2255 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (0 : Int) + d18 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d31, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare659 p hg
    simpa only [d31, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d31, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2254 p hg
    simpa only [d31, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2256 (p : Pattern) (guard : d1 p = 1) : d32 p ≤ (0 : Int) + d19 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d32, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2254 p hg
    simpa only [d32, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d32, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare201 p hg
    simpa only [d32, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2257 (p : Pattern) (guard : d1 p = 1) : d33 p ≤ (0 : Int) + d20 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d33, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2255 p hg
    simpa only [d33, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d33, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2256 p hg
    simpa only [d33, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2258 (p : Pattern) (guard : d1 p = 1) : d34 p ≤ (0 : Int) + d25 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d34, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2257 p hg
    simpa only [d34, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d34, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1453 p hg
    simpa only [d34, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2259 (p : Pattern) (guard : d1 p = 1) : d35 p ≤ (0 : Int) + d26 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d35, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2257 p hg
    simpa only [d35, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d35, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2258 p hg
    simpa only [d35, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2260 (p : Pattern) (guard : d1 p = 1) : d36 p ≤ (0 : Int) + d27 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d36, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare787 p hg
    simpa only [d36, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d36, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2259 p hg
    simpa only [d36, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2261 (p : Pattern) (guard : d0 p = 1) : d43 p ≤ (0 : Int) + d27 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2262 (p : Pattern) (guard : d910 p = 1) : d44 p ≤ (0 : Int) + d27 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d910, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2260 p hg
    simpa only [d910, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d910, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2261 p hg
    simpa only [d910, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2263 (p : Pattern) (guard : d1132 p = 1) : d45 p ≤ (0 : Int) + d27 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1132, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2253 p hg
    simpa only [d1132, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d910 p = 1 := by simpa only [d1132, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2262 p hg
    simpa only [d1132, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2264 (p : Pattern) (guard : d0 p = 1) : d47 p ≤ (0 : Int) + d46 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2265 (p : Pattern) (guard : d1 p = 1) : d48 p ≤ (0 : Int) + d46 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d48, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare209 p hg
    simpa only [d48, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d48, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2258 p hg
    simpa only [d48, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2266 (p : Pattern) (guard : d0 p = 1) : d49 p ≤ (0 : Int) + d46 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2267 (p : Pattern) (guard : d910 p = 1) : d50 p ≤ (0 : Int) + d46 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d910, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2265 p hg
    simpa only [d910, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d910, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2266 p hg
    simpa only [d910, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2268 (p : Pattern) (guard : d1132 p = 1) : d51 p ≤ (0 : Int) + d46 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1132, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2264 p hg
    simpa only [d1132, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d910 p = 1 := by simpa only [d1132, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2267 p hg
    simpa only [d1132, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2269 (p : Pattern) (guard : d0 p = 1) : d57 p ≤ (0 : Int) + d56 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2270 (p : Pattern) (guard : d1 p = 1) : d58 p ≤ (0 : Int) + d54 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d58, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2257 p hg
    simpa only [d58, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d58, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare201 p hg
    simpa only [d58, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2271 (p : Pattern) (guard : d1 p = 1) : d59 p ≤ (0 : Int) + d55 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d59, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2258 p hg
    simpa only [d59, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d59, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2270 p hg
    simpa only [d59, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2272 (p : Pattern) (guard : d1 p = 1) : d60 p ≤ (0 : Int) + d56 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d60, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare796 p hg
    simpa only [d60, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d60, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2271 p hg
    simpa only [d60, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2273 (p : Pattern) (guard : d0 p = 1) : d63 p ≤ (0 : Int) + d56 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2274 (p : Pattern) (guard : d910 p = 1) : d64 p ≤ (0 : Int) + d56 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d910, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2272 p hg
    simpa only [d910, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d910, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2273 p hg
    simpa only [d910, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2275 (p : Pattern) (guard : d1132 p = 1) : d65 p ≤ (0 : Int) + d56 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1132, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2269 p hg
    simpa only [d1132, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d910 p = 1 := by simpa only [d1132, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2274 p hg
    simpa only [d1132, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2276 (p : Pattern) (guard : d1132 p = 1) : d66 p ≤ (0 : Int) + d1133 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d66, d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2268 p hg
    simpa only [d66, d1133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1132 p = 1 := by simpa only [d66, d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2275 p hg
    simpa only [d66, d1133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2277 (p : Pattern) (guard : d1132 p = 1) : d67 p ≤ (0 : Int) + d1134 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d67, d1134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2263 p hg
    simpa only [d67, d1134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1132 p = 1 := by simpa only [d67, d1134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2276 p hg
    simpa only [d67, d1134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2278 (p : Pattern) (guard : d1 p = 1) : d27 p ≤ (0 : Int) + d27 p := by
  omega
theorem compare2279 (p : Pattern) (guard : d0 p = 1) : d72 p ≤ (0 : Int) + d27 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2280 (p : Pattern) (guard : d910 p = 1) : d73 p ≤ (0 : Int) + d27 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d910, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2278 p hg
    simpa only [d910, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d910, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2279 p hg
    simpa only [d910, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2281 (p : Pattern) (guard : d1132 p = 1) : d74 p ≤ (0 : Int) + d27 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1132, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2253 p hg
    simpa only [d1132, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d910 p = 1 := by simpa only [d1132, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2280 p hg
    simpa only [d1132, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2282 (p : Pattern) (guard : d0 p = 1) : d75 p ≤ (0 : Int) + d27 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2283 (p : Pattern) (guard : d910 p = 1) : d76 p ≤ (0 : Int) + d27 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d910, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2278 p hg
    simpa only [d910, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d910, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2282 p hg
    simpa only [d910, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2284 (p : Pattern) (guard : d1132 p = 1) : d77 p ≤ (0 : Int) + d27 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1132, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2253 p hg
    simpa only [d1132, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d910 p = 1 := by simpa only [d1132, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2283 p hg
    simpa only [d1132, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2285 (p : Pattern) (guard : d1132 p = 1) : d78 p ≤ (0 : Int) + d27 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2281 p hg
    simpa only [d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1132 p = 1 := by simpa only [d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2284 p hg
    simpa only [d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2286 (p : Pattern) (guard : d1 p = 1) : d46 p ≤ (0 : Int) + d46 p := by
  omega
theorem compare2287 (p : Pattern) (guard : d0 p = 1) : d75 p ≤ (0 : Int) + d46 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2288 (p : Pattern) (guard : d910 p = 1) : d79 p ≤ (0 : Int) + d46 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d910, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2286 p hg
    simpa only [d910, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d910, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2287 p hg
    simpa only [d910, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2289 (p : Pattern) (guard : d1132 p = 1) : d80 p ≤ (0 : Int) + d46 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1132, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2264 p hg
    simpa only [d1132, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d910 p = 1 := by simpa only [d1132, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2288 p hg
    simpa only [d1132, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2290 (p : Pattern) (guard : d1 p = 1) : d56 p ≤ (0 : Int) + d56 p := by
  omega
theorem compare2291 (p : Pattern) (guard : d0 p = 1) : d75 p ≤ (0 : Int) + d56 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2292 (p : Pattern) (guard : d910 p = 1) : d81 p ≤ (0 : Int) + d56 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d910, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2290 p hg
    simpa only [d910, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d910, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2291 p hg
    simpa only [d910, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2293 (p : Pattern) (guard : d1132 p = 1) : d82 p ≤ (0 : Int) + d56 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1132, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2269 p hg
    simpa only [d1132, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d910 p = 1 := by simpa only [d1132, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2292 p hg
    simpa only [d1132, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2294 (p : Pattern) (guard : d1132 p = 1) : d83 p ≤ (0 : Int) + d1133 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d83, d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2289 p hg
    simpa only [d83, d1133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1132 p = 1 := by simpa only [d83, d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2293 p hg
    simpa only [d83, d1133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2295 (p : Pattern) (guard : d1132 p = 1) : d84 p ≤ (0 : Int) + d1134 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d84, d1134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2285 p hg
    simpa only [d84, d1134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1132 p = 1 := by simpa only [d84, d1134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2294 p hg
    simpa only [d84, d1134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2296 (p : Pattern) (guard : d1132 p = 1) : d85 p ≤ (0 : Int) + d1134 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2277 p hg
    simpa only [d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1132 p = 1 := by simpa only [d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2295 p hg
    simpa only [d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2297 (p : Pattern) (guard : d0 p = 1) : d89 p ≤ (0 : Int) + d88 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2298 (p : Pattern) (guard : d1 p = 1) : d90 p ≤ (0 : Int) + d87 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d90, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2257 p hg
    simpa only [d90, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d90, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2270 p hg
    simpa only [d90, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2299 (p : Pattern) (guard : d1 p = 1) : d91 p ≤ (0 : Int) + d88 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d91, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare805 p hg
    simpa only [d91, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d91, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2298 p hg
    simpa only [d91, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2300 (p : Pattern) (guard : d0 p = 1) : d93 p ≤ (0 : Int) + d88 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2301 (p : Pattern) (guard : d910 p = 1) : d94 p ≤ (0 : Int) + d88 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d910, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2299 p hg
    simpa only [d910, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d910, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2300 p hg
    simpa only [d910, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2302 (p : Pattern) (guard : d1132 p = 1) : d95 p ≤ (0 : Int) + d88 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1132, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2297 p hg
    simpa only [d1132, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d910 p = 1 := by simpa only [d1132, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2301 p hg
    simpa only [d1132, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2303 (p : Pattern) (guard : d1132 p = 1) : d96 p ≤ (0 : Int) + d1135 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d96, d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2263 p hg
    simpa only [d96, d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1132 p = 1 := by simpa only [d96, d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2302 p hg
    simpa only [d96, d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2304 (p : Pattern) (guard : d0 p = 1) : d100 p ≤ (0 : Int) + d99 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2305 (p : Pattern) (guard : d1 p = 1) : d99 p ≤ (0 : Int) + d99 p := by
  omega
theorem compare2306 (p : Pattern) (guard : d0 p = 1) : d72 p ≤ (0 : Int) + d99 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2307 (p : Pattern) (guard : d910 p = 1) : d101 p ≤ (0 : Int) + d99 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d910, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2305 p hg
    simpa only [d910, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d910, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2306 p hg
    simpa only [d910, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2308 (p : Pattern) (guard : d1132 p = 1) : d102 p ≤ (0 : Int) + d99 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1132, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2304 p hg
    simpa only [d1132, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d910 p = 1 := by simpa only [d1132, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2307 p hg
    simpa only [d1132, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2309 (p : Pattern) (guard : d1132 p = 1) : d103 p ≤ (0 : Int) + d1136 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d103, d1136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2303 p hg
    simpa only [d103, d1136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1132 p = 1 := by simpa only [d103, d1136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2308 p hg
    simpa only [d103, d1136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2310 (p : Pattern) (guard : d1 p = 1) : d88 p ≤ (0 : Int) + d88 p := by
  omega
theorem compare2311 (p : Pattern) (guard : d0 p = 1) : d75 p ≤ (0 : Int) + d88 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2312 (p : Pattern) (guard : d910 p = 1) : d104 p ≤ (0 : Int) + d88 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d910, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2310 p hg
    simpa only [d910, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d910, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2311 p hg
    simpa only [d910, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2313 (p : Pattern) (guard : d1132 p = 1) : d105 p ≤ (0 : Int) + d88 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1132, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2297 p hg
    simpa only [d1132, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d910 p = 1 := by simpa only [d1132, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2312 p hg
    simpa only [d1132, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2314 (p : Pattern) (guard : d1132 p = 1) : d106 p ≤ (0 : Int) + d1135 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d106, d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2284 p hg
    simpa only [d106, d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1132 p = 1 := by simpa only [d106, d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2313 p hg
    simpa only [d106, d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2315 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d99 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2316 (p : Pattern) (guard : d910 p = 1) : d107 p ≤ (0 : Int) + d99 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d910, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2305 p hg
    simpa only [d910, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d910, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2315 p hg
    simpa only [d910, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2317 (p : Pattern) (guard : d1132 p = 1) : d108 p ≤ (0 : Int) + d99 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1132, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2304 p hg
    simpa only [d1132, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d910 p = 1 := by simpa only [d1132, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2316 p hg
    simpa only [d1132, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2318 (p : Pattern) (guard : d0 p = 1) : d110 p ≤ (0 : Int) + d109 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2319 (p : Pattern) (guard : d1 p = 1) : d109 p ≤ (0 : Int) + d109 p := by
  omega
theorem compare2320 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d109 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2321 (p : Pattern) (guard : d910 p = 1) : d111 p ≤ (0 : Int) + d109 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d910, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2319 p hg
    simpa only [d910, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d910, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2320 p hg
    simpa only [d910, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2322 (p : Pattern) (guard : d1132 p = 1) : d112 p ≤ (0 : Int) + d109 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1132, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2318 p hg
    simpa only [d1132, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d910 p = 1 := by simpa only [d1132, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2321 p hg
    simpa only [d1132, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2323 (p : Pattern) (guard : d1132 p = 1) : d113 p ≤ (0 : Int) + d1137 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d113, d1137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2317 p hg
    simpa only [d113, d1137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1132 p = 1 := by simpa only [d113, d1137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2322 p hg
    simpa only [d113, d1137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2324 (p : Pattern) (guard : d1132 p = 1) : d114 p ≤ (0 : Int) + d1138 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d114, d1138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2314 p hg
    simpa only [d114, d1138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1132 p = 1 := by simpa only [d114, d1138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2323 p hg
    simpa only [d114, d1138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2325 (p : Pattern) (guard : d1132 p = 1) : d115 p ≤ (0 : Int) + d1139 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d115, d1139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2309 p hg
    simpa only [d115, d1139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1132 p = 1 := by simpa only [d115, d1139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2324 p hg
    simpa only [d115, d1139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2326 (p : Pattern) (guard : d1132 p = 1) : d116 p ≤ (0 : Int) + d1140 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d116, d1140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2296 p hg
    simpa only [d116, d1140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1132 p = 1 := by simpa only [d116, d1140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2325 p hg
    simpa only [d116, d1140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2327 (p : Pattern) (guard : d1132 p = 1) : d117 p ≤ (0 : Int) + d1134 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d117, d1134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2284 p hg
    simpa only [d117, d1134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1132 p = 1 := by simpa only [d117, d1134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2294 p hg
    simpa only [d117, d1134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2328 (p : Pattern) (guard : d1132 p = 1) : d118 p ≤ (0 : Int) + d1134 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2277 p hg
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1132 p = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2327 p hg
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2329 (p : Pattern) (guard : d1 p = 1) : d119 p ≤ (0 : Int) + d20 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2257 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare211 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2330 (p : Pattern) (guard : d1 p = 1) : d120 p ≤ (0 : Int) + d87 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d120, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2329 p hg
    simpa only [d120, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d120, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2270 p hg
    simpa only [d120, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2331 (p : Pattern) (guard : d1 p = 1) : d121 p ≤ (0 : Int) + d88 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d121, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare805 p hg
    simpa only [d121, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d121, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2330 p hg
    simpa only [d121, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2332 (p : Pattern) (guard : d910 p = 1) : d122 p ≤ (0 : Int) + d88 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d910, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2331 p hg
    simpa only [d910, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d910, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2300 p hg
    simpa only [d910, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2333 (p : Pattern) (guard : d1132 p = 1) : d123 p ≤ (0 : Int) + d88 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1132, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2297 p hg
    simpa only [d1132, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d910 p = 1 := by simpa only [d1132, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2332 p hg
    simpa only [d1132, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2334 (p : Pattern) (guard : d1132 p = 1) : d124 p ≤ (0 : Int) + d1135 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d124, d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2263 p hg
    simpa only [d124, d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1132 p = 1 := by simpa only [d124, d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2333 p hg
    simpa only [d124, d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2335 (p : Pattern) (guard : d0 p = 1) : d75 p ≤ (0 : Int) + d109 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2336 (p : Pattern) (guard : d910 p = 1) : d125 p ≤ (0 : Int) + d109 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d910, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2319 p hg
    simpa only [d910, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d910, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2335 p hg
    simpa only [d910, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2337 (p : Pattern) (guard : d1132 p = 1) : d126 p ≤ (0 : Int) + d109 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1132, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2318 p hg
    simpa only [d1132, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d910 p = 1 := by simpa only [d1132, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2336 p hg
    simpa only [d1132, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2338 (p : Pattern) (guard : d1132 p = 1) : d127 p ≤ (0 : Int) + d1137 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d127, d1137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2308 p hg
    simpa only [d127, d1137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1132 p = 1 := by simpa only [d127, d1137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2337 p hg
    simpa only [d127, d1137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2339 (p : Pattern) (guard : d1132 p = 1) : d128 p ≤ (0 : Int) + d1138 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d128, d1138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2334 p hg
    simpa only [d128, d1138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1132 p = 1 := by simpa only [d128, d1138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2338 p hg
    simpa only [d128, d1138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2340 (p : Pattern) (guard : d1132 p = 1) : d129 p ≤ (0 : Int) + d1141 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d129, d1141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2284 p hg
    simpa only [d129, d1141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1132 p = 1 := by simpa only [d129, d1141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2293 p hg
    simpa only [d129, d1141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2341 (p : Pattern) (guard : d1132 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare2342 (p : Pattern) (guard : d1132 p = 1) : d130 p ≤ (0 : Int) + d1142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d130, d1142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2322 p hg
    simpa only [d130, d1142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1132 p = 1 := by simpa only [d130, d1142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2341 p hg
    simpa only [d130, d1142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2343 (p : Pattern) (guard : d1132 p = 1) : d131 p ≤ (0 : Int) + d1143 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d131, d1143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2340 p hg
    simpa only [d131, d1143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1132 p = 1 := by simpa only [d131, d1143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2342 p hg
    simpa only [d131, d1143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2344 (p : Pattern) (guard : d1132 p = 1) : d132 p ≤ (0 : Int) + d1144 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d132, d1144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2339 p hg
    simpa only [d132, d1144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1132 p = 1 := by simpa only [d132, d1144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2343 p hg
    simpa only [d132, d1144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2345 (p : Pattern) (guard : d1132 p = 1) : d133 p ≤ (0 : Int) + d1145 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d133, d1145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2328 p hg
    simpa only [d133, d1145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1132 p = 1 := by simpa only [d133, d1145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2344 p hg
    simpa only [d133, d1145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2346 (p : Pattern) (guard : d1132 p = 1) : d134 p ≤ (0 : Int) + d1146 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d134, d1146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2326 p hg
    simpa only [d134, d1146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1132 p = 1 := by simpa only [d134, d1146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2345 p hg
    simpa only [d134, d1146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2347 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (0 : Int) + d6 p := by
  omega
theorem compare2348 (p : Pattern) (guard : d0 p = 1) : d7 p ≤ (0 : Int) + d23 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2349 (p : Pattern) (guard : d873 p = 1) : d8 p ≤ (0 : Int) + d538 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d873, d8, d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2347 p hg
    simpa only [d873, d8, d538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d873, d8, d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d873, d8, d538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2350 (p : Pattern) (guard : d0 p = 1) : d7 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2351 (p : Pattern) (guard : d873 p = 1) : d8 p ≤ (0 : Int) + d539 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d873, d8, d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2347 p hg
    simpa only [d873, d8, d539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d873, d8, d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2350 p hg
    simpa only [d873, d8, d539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2352 (p : Pattern) (guard : d1 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare2353 (p : Pattern) (guard : d0 p = 1) : d13 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2354 (p : Pattern) (guard : d873 p = 1) : d14 p ≤ (0 : Int) + d540 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d873, d14, d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2352 p hg
    simpa only [d873, d14, d540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d873, d14, d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2353 p hg
    simpa only [d873, d14, d540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2355 (p : Pattern) (guard : d873 p = 1) : d15 p ≤ (0 : Int) + d541 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d15, d541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2351 p hg
    simpa only [d15, d541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d15, d541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2354 p hg
    simpa only [d15, d541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2356 (p : Pattern) (guard : d873 p = 1) : d16 p ≤ (0 : Int) + d542 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d16, d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2349 p hg
    simpa only [d16, d542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d16, d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2355 p hg
    simpa only [d16, d542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2357 (p : Pattern) (guard : d873 p = 1) : d16 p ≤ (0 : Int) + d543 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d16, d543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2351 p hg
    simpa only [d16, d543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d16, d543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2355 p hg
    simpa only [d16, d543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2358 (p : Pattern) (guard : d873 p = 1) : d16 p ≤ (0 : Int) + d544 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2356 p hg
    simpa only [d544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2357 p hg
    simpa only [d544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2359 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (0 : Int) + d18 p := by
  omega
theorem compare2360 (p : Pattern) (guard : d0 p = 1) : d19 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2361 (p : Pattern) (guard : d873 p = 1) : d20 p ≤ (0 : Int) + d545 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d873, d20, d545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2359 p hg
    simpa only [d873, d20, d545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d873, d20, d545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2360 p hg
    simpa only [d873, d20, d545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2362 (p : Pattern) (guard : d1 p = 1) : d22 p ≤ (0 : Int) + d22 p := by
  omega
theorem compare2363 (p : Pattern) (guard : d0 p = 1) : d23 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2364 (p : Pattern) (guard : d873 p = 1) : d24 p ≤ (0 : Int) + d546 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d873, d24, d546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2362 p hg
    simpa only [d873, d24, d546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d873, d24, d546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2363 p hg
    simpa only [d873, d24, d546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2365 (p : Pattern) (guard : d873 p = 1) : d25 p ≤ (0 : Int) + d547 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d25, d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2361 p hg
    simpa only [d25, d547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d25, d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2364 p hg
    simpa only [d25, d547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2366 (p : Pattern) (guard : d873 p = 1) : d26 p ≤ (0 : Int) + d548 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d26, d548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2361 p hg
    simpa only [d26, d548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d26, d548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2365 p hg
    simpa only [d26, d548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2367 (p : Pattern) (guard : d873 p = 1) : d27 p ≤ (0 : Int) + d549 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d27, d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2357 p hg
    simpa only [d27, d549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d27, d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2366 p hg
    simpa only [d27, d549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2368 (p : Pattern) (guard : d873 p = 1) : d28 p ≤ (0 : Int) + d550 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d28, d550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2358 p hg
    simpa only [d28, d550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d28, d550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2367 p hg
    simpa only [d28, d550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2369 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (0 : Int) + d31 p := by
  omega
theorem compare2370 (p : Pattern) (guard : d0 p = 1) : d32 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2371 (p : Pattern) (guard : d873 p = 1) : d33 p ≤ (0 : Int) + d551 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d873, d33, d551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2369 p hg
    simpa only [d873, d33, d551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d873, d33, d551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2370 p hg
    simpa only [d873, d33, d551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2372 (p : Pattern) (guard : d873 p = 1) : d34 p ≤ (0 : Int) + d552 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d34, d552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2371 p hg
    simpa only [d34, d552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d34, d552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2364 p hg
    simpa only [d34, d552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2373 (p : Pattern) (guard : d873 p = 1) : d35 p ≤ (0 : Int) + d553 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d35, d553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2371 p hg
    simpa only [d35, d553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d35, d553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2372 p hg
    simpa only [d35, d553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2374 (p : Pattern) (guard : d873 p = 1) : d36 p ≤ (0 : Int) + d554 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d36, d554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2356 p hg
    simpa only [d36, d554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d36, d554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2373 p hg
    simpa only [d36, d554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2375 (p : Pattern) (guard : d0 p = 1) : d37 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2376 (p : Pattern) (guard : d873 p = 1) : d38 p ≤ (0 : Int) + d539 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d873, d38, d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2347 p hg
    simpa only [d873, d38, d539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d873, d38, d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2375 p hg
    simpa only [d873, d38, d539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2377 (p : Pattern) (guard : d0 p = 1) : d39 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2378 (p : Pattern) (guard : d873 p = 1) : d40 p ≤ (0 : Int) + d540 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d873, d40, d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2352 p hg
    simpa only [d873, d40, d540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d873, d40, d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2377 p hg
    simpa only [d873, d40, d540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2379 (p : Pattern) (guard : d873 p = 1) : d41 p ≤ (0 : Int) + d541 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d41, d541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2376 p hg
    simpa only [d41, d541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d41, d541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2378 p hg
    simpa only [d41, d541, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
