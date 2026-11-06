/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons130
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare18340 (p : Pattern) (guard : d4902 p = 1) : d2217 p ≤ (2 : Int) + d41 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2217, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18339 p hg
    simpa only [d2217, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2217, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2217, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18341 (p : Pattern) (guard : d4902 p = 1) : d2218 p ≤ (2 : Int) + d42 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2218, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18305 p hg
    simpa only [d2218, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2218, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18340 p hg
    simpa only [d2218, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18342 (p : Pattern) (guard : d4902 p = 1) : d2219 p ≤ (2 : Int) + d43 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2219, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18319 p hg
    simpa only [d2219, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2219, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2219, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18343 (p : Pattern) (guard : d4902 p = 1) : d2220 p ≤ (2 : Int) + d44 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2220, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18341 p hg
    simpa only [d2220, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2220, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18342 p hg
    simpa only [d2220, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18344 (p : Pattern) (guard : d4902 p = 1) : d2221 p ≤ (2 : Int) + d45 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2221, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18338 p hg
    simpa only [d2221, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2221, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18343 p hg
    simpa only [d2221, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18345 (p : Pattern) (guard : d4902 p = 1) : d2222 p ≤ (2 : Int) + d46 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2222, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18305 p hg
    simpa only [d2222, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2222, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2222, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18346 (p : Pattern) (guard : d4902 p = 1) : d2223 p ≤ (2 : Int) + d47 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2223, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18345 p hg
    simpa only [d2223, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2223, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18342 p hg
    simpa only [d2223, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18347 (p : Pattern) (guard : d4902 p = 1) : d2224 p ≤ (2 : Int) + d48 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2224, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18326 p hg
    simpa only [d2224, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2224, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2224, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18348 (p : Pattern) (guard : d4902 p = 1) : d2225 p ≤ (2 : Int) + d49 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2225, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18347 p hg
    simpa only [d2225, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2225, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2225, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18349 (p : Pattern) (guard : d4902 p = 1) : d2226 p ≤ (2 : Int) + d50 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2226, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18346 p hg
    simpa only [d2226, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2226, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18348 p hg
    simpa only [d2226, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18350 (p : Pattern) (guard : d4902 p = 1) : d2227 p ≤ (2 : Int) + d51 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2227, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18344 p hg
    simpa only [d2227, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2227, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18349 p hg
    simpa only [d2227, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18351 (p : Pattern) (guard : d4902 p = 1) : d2228 p ≤ (2 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2228, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18331 p hg
    simpa only [d2228, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2228, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18350 p hg
    simpa only [d2228, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18352 (p : Pattern) (guard : d0 p = 1) : d357 p ≤ (2 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare18353 (p : Pattern) (guard : d4902 p = 1) : d2229 p ≤ (2 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4688 p hg
    simpa only [d4902, d2229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18352 p hg
    simpa only [d4902, d2229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18354 (p : Pattern) (guard : d4902 p = 1) : d2230 p ≤ (2 : Int) + d14 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18353 p hg
    simpa only [d2230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18305 p hg
    simpa only [d2230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18355 (p : Pattern) (guard : d4902 p = 1) : d2231 p ≤ (2 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2231, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18354 p hg
    simpa only [d2231, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2231, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18308 p hg
    simpa only [d2231, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18356 (p : Pattern) (guard : d4902 p = 1) : d2232 p ≤ (2 : Int) + d53 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2232, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18332 p hg
    simpa only [d2232, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2232, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18333 p hg
    simpa only [d2232, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18357 (p : Pattern) (guard : d4902 p = 1) : d2233 p ≤ (2 : Int) + d54 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2233, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18355 p hg
    simpa only [d2233, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2233, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18356 p hg
    simpa only [d2233, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18358 (p : Pattern) (guard : d4902 p = 1) : d2234 p ≤ (2 : Int) + d55 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2234, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18321 p hg
    simpa only [d2234, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2234, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18328 p hg
    simpa only [d2234, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18359 (p : Pattern) (guard : d4902 p = 1) : d2235 p ≤ (2 : Int) + d56 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2235, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18357 p hg
    simpa only [d2235, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2235, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18358 p hg
    simpa only [d2235, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18360 (p : Pattern) (guard : d4902 p = 1) : d2236 p ≤ (2 : Int) + d58 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2175 p hg
    simpa only [d4902, d2236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15728 p hg
    simpa only [d4902, d2236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18361 (p : Pattern) (guard : d4902 p = 1) : d2237 p ≤ (2 : Int) + d59 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2237, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18360 p hg
    simpa only [d2237, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2237, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2237, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18362 (p : Pattern) (guard : d4902 p = 1) : d2238 p ≤ (2 : Int) + d60 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2238, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18360 p hg
    simpa only [d2238, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2238, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18361 p hg
    simpa only [d2238, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18363 (p : Pattern) (guard : d4902 p = 1) : d2239 p ≤ (2 : Int) + d61 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2239, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18321 p hg
    simpa only [d2239, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2239, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18362 p hg
    simpa only [d2239, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18364 (p : Pattern) (guard : d4902 p = 1) : d2240 p ≤ (2 : Int) + d62 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2240, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18339 p hg
    simpa only [d2240, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2240, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18340 p hg
    simpa only [d2240, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18365 (p : Pattern) (guard : d4902 p = 1) : d2241 p ≤ (2 : Int) + d63 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2241, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18364 p hg
    simpa only [d2241, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2241, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2241, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18366 (p : Pattern) (guard : d4902 p = 1) : d2242 p ≤ (2 : Int) + d64 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2242, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18363 p hg
    simpa only [d2242, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2242, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18365 p hg
    simpa only [d2242, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18367 (p : Pattern) (guard : d4902 p = 1) : d2243 p ≤ (2 : Int) + d65 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2243, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18359 p hg
    simpa only [d2243, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2243, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18366 p hg
    simpa only [d2243, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18368 (p : Pattern) (guard : d4902 p = 1) : d2244 p ≤ (2 : Int) + d66 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2244, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18332 p hg
    simpa only [d2244, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2244, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2244, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18369 (p : Pattern) (guard : d4902 p = 1) : d2245 p ≤ (2 : Int) + d67 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2245, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18337 p hg
    simpa only [d2245, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2245, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18368 p hg
    simpa only [d2245, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18370 (p : Pattern) (guard : d4902 p = 1) : d2246 p ≤ (2 : Int) + d68 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2246, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18342 p hg
    simpa only [d2246, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2246, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18347 p hg
    simpa only [d2246, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18371 (p : Pattern) (guard : d4902 p = 1) : d2247 p ≤ (2 : Int) + d69 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2247, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18369 p hg
    simpa only [d2247, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2247, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18370 p hg
    simpa only [d2247, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18372 (p : Pattern) (guard : d4902 p = 1) : d2248 p ≤ (2 : Int) + d70 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2248, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18360 p hg
    simpa only [d2248, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2248, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2248, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18373 (p : Pattern) (guard : d4902 p = 1) : d2249 p ≤ (2 : Int) + d71 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2249, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18342 p hg
    simpa only [d2249, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2249, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18372 p hg
    simpa only [d2249, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18374 (p : Pattern) (guard : d4902 p = 1) : d2250 p ≤ (2 : Int) + d72 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2250, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18339 p hg
    simpa only [d2250, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2250, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2250, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18375 (p : Pattern) (guard : d4902 p = 1) : d2251 p ≤ (2 : Int) + d73 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2251, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18374 p hg
    simpa only [d2251, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2251, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2251, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18376 (p : Pattern) (guard : d4902 p = 1) : d2252 p ≤ (2 : Int) + d74 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2252, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18373 p hg
    simpa only [d2252, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2252, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18375 p hg
    simpa only [d2252, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18377 (p : Pattern) (guard : d4902 p = 1) : d2253 p ≤ (2 : Int) + d75 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2253, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18371 p hg
    simpa only [d2253, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2253, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18376 p hg
    simpa only [d2253, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18378 (p : Pattern) (guard : d4902 p = 1) : d2254 p ≤ (2 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2254, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18367 p hg
    simpa only [d2254, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2254, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18377 p hg
    simpa only [d2254, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18379 (p : Pattern) (guard : d4902 p = 1) : d2255 p ≤ (2 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2255, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18351 p hg
    simpa only [d2255, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2255, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18378 p hg
    simpa only [d2255, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18380 (p : Pattern) (guard : d4902 p = 1) : d2256 p ≤ (2 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2256, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18324 p hg
    simpa only [d2256, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2256, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18325 p hg
    simpa only [d2256, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18381 (p : Pattern) (guard : d4902 p = 1) : d2257 p ≤ (2 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2257, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18380 p hg
    simpa only [d2257, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2257, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18330 p hg
    simpa only [d2257, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18382 (p : Pattern) (guard : d4902 p = 1) : d2258 p ≤ (2 : Int) + d78 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2258, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18335 p hg
    simpa only [d2258, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2258, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18336 p hg
    simpa only [d2258, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18383 (p : Pattern) (guard : d4902 p = 1) : d2259 p ≤ (2 : Int) + d79 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2259, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18356 p hg
    simpa only [d2259, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2259, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18382 p hg
    simpa only [d2259, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18384 (p : Pattern) (guard : d4902 p = 1) : d2260 p ≤ (2 : Int) + d80 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2260, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18383 p hg
    simpa only [d2260, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2260, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18365 p hg
    simpa only [d2260, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18385 (p : Pattern) (guard : d4902 p = 1) : d2261 p ≤ (2 : Int) + d81 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2261, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18384 p hg
    simpa only [d2261, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2261, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2261, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18386 (p : Pattern) (guard : d4902 p = 1) : d2262 p ≤ (2 : Int) + d82 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2262, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18381 p hg
    simpa only [d2262, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2262, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18385 p hg
    simpa only [d2262, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18387 (p : Pattern) (guard : d4902 p = 1) : d2263 p ≤ (2 : Int) + d54 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2263, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18324 p hg
    simpa only [d2263, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2263, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18356 p hg
    simpa only [d2263, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18388 (p : Pattern) (guard : d4902 p = 1) : d2264 p ≤ (2 : Int) + d56 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2264, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18387 p hg
    simpa only [d2264, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2264, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18358 p hg
    simpa only [d2264, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18389 (p : Pattern) (guard : d4902 p = 1) : d2265 p ≤ (2 : Int) + d65 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2265, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18388 p hg
    simpa only [d2265, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2265, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18366 p hg
    simpa only [d2265, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18390 (p : Pattern) (guard : d4902 p = 1) : d2266 p ≤ (2 : Int) + d83 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2266, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18382 p hg
    simpa only [d2266, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2266, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2266, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18391 (p : Pattern) (guard : d4902 p = 1) : d2267 p ≤ (2 : Int) + d84 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2267, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18390 p hg
    simpa only [d2267, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2267, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2267, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18392 (p : Pattern) (guard : d4902 p = 1) : d2268 p ≤ (2 : Int) + d85 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2268, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18391 p hg
    simpa only [d2268, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2268, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2268, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18393 (p : Pattern) (guard : d4902 p = 1) : d2269 p ≤ (2 : Int) + d86 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2269, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18389 p hg
    simpa only [d2269, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2269, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18392 p hg
    simpa only [d2269, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18394 (p : Pattern) (guard : d4902 p = 1) : d2270 p ≤ (2 : Int) + d87 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2270, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18386 p hg
    simpa only [d2270, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2270, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18393 p hg
    simpa only [d2270, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18395 (p : Pattern) (guard : d4902 p = 1) : d2271 p ≤ (2 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2271, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18379 p hg
    simpa only [d2271, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2271, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18394 p hg
    simpa only [d2271, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18396 (p : Pattern) (guard : d4902 p = 1) : d2272 p ≤ (2 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18318 p hg
    simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18324 p hg
    simpa only [d2272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18397 (p : Pattern) (guard : d4902 p = 1) : d2273 p ≤ (2 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2273, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18396 p hg
    simpa only [d2273, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2273, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18325 p hg
    simpa only [d2273, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18398 (p : Pattern) (guard : d4902 p = 1) : d2274 p ≤ (2 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2274, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18397 p hg
    simpa only [d2274, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2274, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18330 p hg
    simpa only [d2274, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18399 (p : Pattern) (guard : d4902 p = 1) : d2275 p ≤ (2 : Int) + d82 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2275, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18398 p hg
    simpa only [d2275, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2275, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18385 p hg
    simpa only [d2275, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18400 (p : Pattern) (guard : d4902 p = 1) : d2276 p ≤ (2 : Int) + d87 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2276, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18399 p hg
    simpa only [d2276, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2276, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18393 p hg
    simpa only [d2276, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18401 (p : Pattern) (guard : d4902 p = 1) : d2277 p ≤ (2 : Int) + d89 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2277, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18328 p hg
    simpa only [d2277, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2277, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18364 p hg
    simpa only [d2277, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18402 (p : Pattern) (guard : d4902 p = 1) : d2278 p ≤ (2 : Int) + d90 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2278, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18401 p hg
    simpa only [d2278, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2278, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18365 p hg
    simpa only [d2278, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18403 (p : Pattern) (guard : d4902 p = 1) : d2279 p ≤ (2 : Int) + d91 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2279, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18365 p hg
    simpa only [d2279, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2279, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2279, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18404 (p : Pattern) (guard : d4902 p = 1) : d2280 p ≤ (2 : Int) + d92 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2280, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18402 p hg
    simpa only [d2280, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2280, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18403 p hg
    simpa only [d2280, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18405 (p : Pattern) (guard : d4902 p = 1) : d2281 p ≤ (2 : Int) + d93 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2281, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18403 p hg
    simpa only [d2281, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2281, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2281, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18406 (p : Pattern) (guard : d4902 p = 1) : d2282 p ≤ (2 : Int) + d94 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2282, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18404 p hg
    simpa only [d2282, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2282, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18405 p hg
    simpa only [d2282, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18407 (p : Pattern) (guard : d4902 p = 1) : d2283 p ≤ (2 : Int) + d95 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2283, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18405 p hg
    simpa only [d2283, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2283, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2283, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18408 (p : Pattern) (guard : d4902 p = 1) : d2284 p ≤ (2 : Int) + d96 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2284, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18406 p hg
    simpa only [d2284, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2284, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18407 p hg
    simpa only [d2284, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18409 (p : Pattern) (guard : d4902 p = 1) : d2285 p ≤ (2 : Int) + d97 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2285, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18400 p hg
    simpa only [d2285, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2285, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18408 p hg
    simpa only [d2285, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18410 (p : Pattern) (guard : d4902 p = 1) : d2286 p ≤ (2 : Int) + d98 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2286, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18395 p hg
    simpa only [d2286, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2286, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18409 p hg
    simpa only [d2286, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18411 (p : Pattern) (guard : d4902 p = 1) : d2287 p ≤ (2 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18313 p hg
    simpa only [d2287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18324 p hg
    simpa only [d2287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18412 (p : Pattern) (guard : d4902 p = 1) : d2288 p ≤ (2 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2288, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18411 p hg
    simpa only [d2288, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2288, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18325 p hg
    simpa only [d2288, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18413 (p : Pattern) (guard : d4902 p = 1) : d2289 p ≤ (2 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2289, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18412 p hg
    simpa only [d2289, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2289, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18330 p hg
    simpa only [d2289, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18414 (p : Pattern) (guard : d4902 p = 1) : d2290 p ≤ (2 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2290, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18413 p hg
    simpa only [d2290, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2290, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18350 p hg
    simpa only [d2290, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18415 (p : Pattern) (guard : d4902 p = 1) : d2291 p ≤ (2 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2291, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18389 p hg
    simpa only [d2291, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2291, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18377 p hg
    simpa only [d2291, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18416 (p : Pattern) (guard : d4902 p = 1) : d2292 p ≤ (2 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2292, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18414 p hg
    simpa only [d2292, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2292, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18415 p hg
    simpa only [d2292, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18417 (p : Pattern) (guard : d4902 p = 1) : d2293 p ≤ (2 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2293, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18416 p hg
    simpa only [d2293, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2293, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18394 p hg
    simpa only [d2293, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18418 (p : Pattern) (guard : d4902 p = 1) : d2294 p ≤ (2 : Int) + d99 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2294, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18394 p hg
    simpa only [d2294, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2294, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2294, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18419 (p : Pattern) (guard : d4902 p = 1) : d2295 p ≤ (2 : Int) + d100 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2295, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18417 p hg
    simpa only [d2295, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2295, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18418 p hg
    simpa only [d2295, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18420 (p : Pattern) (guard : d4902 p = 1) : d2296 p ≤ (2 : Int) + d101 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2296, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18410 p hg
    simpa only [d2296, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2296, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18419 p hg
    simpa only [d2296, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18421 (p : Pattern) (guard : d0 p = 1) : d320 p ≤ (2 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare18422 (p : Pattern) (guard : d4902 p = 1) : d2297 p ≤ (2 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4688 p hg
    simpa only [d4902, d2297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18421 p hg
    simpa only [d4902, d2297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18423 (p : Pattern) (guard : d4902 p = 1) : d2298 p ≤ (2 : Int) + d14 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18422 p hg
    simpa only [d2298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18305 p hg
    simpa only [d2298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18424 (p : Pattern) (guard : d4902 p = 1) : d2299 p ≤ (2 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2299, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18423 p hg
    simpa only [d2299, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2299, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18308 p hg
    simpa only [d2299, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18425 (p : Pattern) (guard : d4902 p = 1) : d2300 p ≤ (2 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18424 p hg
    simpa only [d2300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18318 p hg
    simpa only [d2300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18426 (p : Pattern) (guard : d4902 p = 1) : d2301 p ≤ (2 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2301, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18425 p hg
    simpa only [d2301, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2301, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18325 p hg
    simpa only [d2301, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18427 (p : Pattern) (guard : d4902 p = 1) : d2302 p ≤ (2 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2302, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18426 p hg
    simpa only [d2302, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2302, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18330 p hg
    simpa only [d2302, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18428 (p : Pattern) (guard : d4902 p = 1) : d2303 p ≤ (2 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2303, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18427 p hg
    simpa only [d2303, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2303, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18350 p hg
    simpa only [d2303, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18429 (p : Pattern) (guard : d4902 p = 1) : d2304 p ≤ (2 : Int) + d54 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2304, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18313 p hg
    simpa only [d2304, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2304, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18356 p hg
    simpa only [d2304, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18430 (p : Pattern) (guard : d4902 p = 1) : d2305 p ≤ (2 : Int) + d56 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2305, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18429 p hg
    simpa only [d2305, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2305, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18358 p hg
    simpa only [d2305, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18431 (p : Pattern) (guard : d4902 p = 1) : d2306 p ≤ (2 : Int) + d65 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2306, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18430 p hg
    simpa only [d2306, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2306, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18366 p hg
    simpa only [d2306, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18432 (p : Pattern) (guard : d4902 p = 1) : d2307 p ≤ (2 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2307, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18431 p hg
    simpa only [d2307, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2307, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18377 p hg
    simpa only [d2307, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18433 (p : Pattern) (guard : d4902 p = 1) : d2308 p ≤ (2 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2308, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18428 p hg
    simpa only [d2308, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2308, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18432 p hg
    simpa only [d2308, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18434 (p : Pattern) (guard : d4902 p = 1) : d2309 p ≤ (2 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2309, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18433 p hg
    simpa only [d2309, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2309, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18394 p hg
    simpa only [d2309, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18435 (p : Pattern) (guard : d4902 p = 1) : d2310 p ≤ (2 : Int) + d97 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2310, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18394 p hg
    simpa only [d2310, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2310, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18408 p hg
    simpa only [d2310, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18436 (p : Pattern) (guard : d4902 p = 1) : d2311 p ≤ (2 : Int) + d98 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2311, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18434 p hg
    simpa only [d2311, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2311, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18435 p hg
    simpa only [d2311, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18437 (p : Pattern) (guard : d4902 p = 1) : d2312 p ≤ (2 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2312, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18398 p hg
    simpa only [d2312, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2312, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18350 p hg
    simpa only [d2312, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18438 (p : Pattern) (guard : d4902 p = 1) : d2313 p ≤ (2 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2313, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18437 p hg
    simpa only [d2313, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2313, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18415 p hg
    simpa only [d2313, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18439 (p : Pattern) (guard : d4902 p = 1) : d2314 p ≤ (2 : Int) + d88 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2314, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18438 p hg
    simpa only [d2314, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2314, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18394 p hg
    simpa only [d2314, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18440 (p : Pattern) (guard : d4902 p = 1) : d2315 p ≤ (2 : Int) + d100 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2315, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18439 p hg
    simpa only [d2315, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2315, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18418 p hg
    simpa only [d2315, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18441 (p : Pattern) (guard : d4902 p = 1) : d2316 p ≤ (2 : Int) + d101 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2316, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18436 p hg
    simpa only [d2316, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2316, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18440 p hg
    simpa only [d2316, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18442 (p : Pattern) (guard : d4902 p = 1) : d2317 p ≤ (2 : Int) + d101 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18420 p hg
    simpa only [d2317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18441 p hg
    simpa only [d2317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18443 (p : Pattern) (guard : d0 p = 1) : d320 p ≤ (2 : Int) + d103 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare18444 (p : Pattern) (guard : d4902 p = 1) : d2318 p ≤ (2 : Int) + d103 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2156 p hg
    simpa only [d4902, d2318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18443 p hg
    simpa only [d4902, d2318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18445 (p : Pattern) (guard : d4902 p = 1) : d2319 p ≤ (2 : Int) + d103 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2156 p hg
    simpa only [d4902, d2319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15926 p hg
    simpa only [d4902, d2319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18446 (p : Pattern) (guard : d4902 p = 1) : d2320 p ≤ (2 : Int) + d103 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18444 p hg
    simpa only [d2320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18445 p hg
    simpa only [d2320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18447 (p : Pattern) (guard : d4902 p = 1) : d2321 p ≤ (2 : Int) + d104 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2321, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18445 p hg
    simpa only [d2321, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2321, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2321, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18448 (p : Pattern) (guard : d4902 p = 1) : d2322 p ≤ (2 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2322, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18446 p hg
    simpa only [d2322, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2322, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18447 p hg
    simpa only [d2322, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18449 (p : Pattern) (guard : d0 p = 1) : d332 p ≤ (2 : Int) + d103 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare18450 (p : Pattern) (guard : d4902 p = 1) : d2323 p ≤ (2 : Int) + d103 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2156 p hg
    simpa only [d4902, d2323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18449 p hg
    simpa only [d4902, d2323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18451 (p : Pattern) (guard : d4902 p = 1) : d2324 p ≤ (2 : Int) + d103 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18450 p hg
    simpa only [d2324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18445 p hg
    simpa only [d2324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18452 (p : Pattern) (guard : d4902 p = 1) : d2325 p ≤ (2 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2325, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18451 p hg
    simpa only [d2325, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2325, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18447 p hg
    simpa only [d2325, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18453 (p : Pattern) (guard : d4902 p = 1) : d2326 p ≤ (2 : Int) + d105 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18448 p hg
    simpa only [d2326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18452 p hg
    simpa only [d2326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18454 (p : Pattern) (guard : d4902 p = 1) : d2327 p ≤ (2 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2327, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18445 p hg
    simpa only [d2327, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2327, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18447 p hg
    simpa only [d2327, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18455 (p : Pattern) (guard : d4902 p = 1) : d2328 p ≤ (2 : Int) + d107 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2167 p hg
    simpa only [d4902, d2328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15938 p hg
    simpa only [d4902, d2328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18456 (p : Pattern) (guard : d4902 p = 1) : d2329 p ≤ (2 : Int) + d108 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2329, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18455 p hg
    simpa only [d2329, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2329, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2329, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18457 (p : Pattern) (guard : d4902 p = 1) : d2330 p ≤ (2 : Int) + d109 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2330, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18455 p hg
    simpa only [d2330, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2330, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18456 p hg
    simpa only [d2330, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18458 (p : Pattern) (guard : d4902 p = 1) : d2331 p ≤ (2 : Int) + d110 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2331, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18454 p hg
    simpa only [d2331, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2331, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18457 p hg
    simpa only [d2331, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18459 (p : Pattern) (guard : d4902 p = 1) : d2332 p ≤ (2 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2332, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18453 p hg
    simpa only [d2332, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2332, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18458 p hg
    simpa only [d2332, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18460 (p : Pattern) (guard : d4902 p = 1) : d2333 p ≤ (2 : Int) + d112 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2333, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18362 p hg
    simpa only [d2333, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2333, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2333, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18461 (p : Pattern) (guard : d4902 p = 1) : d2334 p ≤ (2 : Int) + d113 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2334, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18458 p hg
    simpa only [d2334, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2334, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18460 p hg
    simpa only [d2334, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18462 (p : Pattern) (guard : d4902 p = 1) : d2335 p ≤ (2 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2335, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18459 p hg
    simpa only [d2335, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2335, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18461 p hg
    simpa only [d2335, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18463 (p : Pattern) (guard : d4902 p = 1) : d2336 p ≤ (2 : Int) + d116 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2186 p hg
    simpa only [d4902, d2336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15956 p hg
    simpa only [d4902, d2336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18464 (p : Pattern) (guard : d4902 p = 1) : d2337 p ≤ (2 : Int) + d117 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2337, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18463 p hg
    simpa only [d2337, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2337, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2337, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18465 (p : Pattern) (guard : d4902 p = 1) : d2338 p ≤ (2 : Int) + d118 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2338, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18445 p hg
    simpa only [d2338, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2338, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18464 p hg
    simpa only [d2338, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18466 (p : Pattern) (guard : d4902 p = 1) : d2339 p ≤ (2 : Int) + d120 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13358 p hg
    simpa only [d4902, d2339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15992 p hg
    simpa only [d4902, d2339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18467 (p : Pattern) (guard : d4902 p = 1) : d2340 p ≤ (2 : Int) + d121 p := by
  cases selected : p 204 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2340, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18466 p hg
    simpa only [d2340, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2340, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2340, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18468 (p : Pattern) (guard : d4902 p = 1) : d2341 p ≤ (2 : Int) + d122 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2341, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18445 p hg
    simpa only [d2341, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2341, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18467 p hg
    simpa only [d2341, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18469 (p : Pattern) (guard : d4902 p = 1) : d2342 p ≤ (2 : Int) + d123 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2342, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18465 p hg
    simpa only [d2342, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2342, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18468 p hg
    simpa only [d2342, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18470 (p : Pattern) (guard : d4902 p = 1) : d2343 p ≤ (2 : Int) + d124 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2343, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18445 p hg
    simpa only [d2343, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2343, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2343, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18471 (p : Pattern) (guard : d4902 p = 1) : d2344 p ≤ (2 : Int) + d125 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2344, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18455 p hg
    simpa only [d2344, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2344, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2344, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18472 (p : Pattern) (guard : d4902 p = 1) : d2345 p ≤ (2 : Int) + d126 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2345, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18470 p hg
    simpa only [d2345, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2345, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18471 p hg
    simpa only [d2345, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18473 (p : Pattern) (guard : d4902 p = 1) : d2346 p ≤ (2 : Int) + d127 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2346, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18469 p hg
    simpa only [d2346, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2346, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18472 p hg
    simpa only [d2346, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18474 (p : Pattern) (guard : d4902 p = 1) : d2347 p ≤ (2 : Int) + d128 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2347, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18372 p hg
    simpa only [d2347, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2347, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d2347, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18475 (p : Pattern) (guard : d4902 p = 1) : d2348 p ≤ (2 : Int) + d129 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2348, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18472 p hg
    simpa only [d2348, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2348, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18474 p hg
    simpa only [d2348, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18476 (p : Pattern) (guard : d4902 p = 1) : d2349 p ≤ (2 : Int) + d130 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2349, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18473 p hg
    simpa only [d2349, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2349, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18475 p hg
    simpa only [d2349, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18477 (p : Pattern) (guard : d4902 p = 1) : d2350 p ≤ (2 : Int) + d131 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4902 p = 1 := by simpa only [d2350, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18462 p hg
    simpa only [d2350, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4902 p = 1 := by simpa only [d2350, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18476 p hg
    simpa only [d2350, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18478 (p : Pattern) (guard : d0 p = 1) : d330 p ≤ (2 : Int) + d103 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare18479 (p : Pattern) (guard : d4902 p = 1) : d2351 p ≤ (2 : Int) + d103 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4902, d2351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2156 p hg
    simpa only [d4902, d2351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4902, d2351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18478 p hg
    simpa only [d4902, d2351, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
