import NetHack.Soko22Hazard87.Compare080
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare20250 (p : Pattern) (guard : d5251 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d5250 p = 1 := by simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20249 p hg
    simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17949 p hg
    simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20251 (p : Pattern) (guard : d10411 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare20252 (p : Pattern) (guard : d10412 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10411 p = 1 := by simpa only [d10412, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20251 p hg
    simpa only [d10412, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10412, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d10412, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20253 (p : Pattern) (guard : d10414 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10412 p = 1 := by simpa only [d10414, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20252 p hg
    simpa only [d10414, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10414, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d10414, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20254 (p : Pattern) (guard : d15555 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15555, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d15555, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10414 p = 1 := by simpa only [d15555, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20253 p hg
    simpa only [d15555, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20255 (p : Pattern) (guard : d15556 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15555 p = 1 := by simpa only [d15556, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20254 p hg
    simpa only [d15556, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15556, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d15556, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20256 (p : Pattern) (guard : d15557 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15556 p = 1 := by simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20255 p hg
    simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17949 p hg
    simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20257 (p : Pattern) (guard : d15558 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d5251 p = 1 := by simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20250 p hg
    simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15557 p = 1 := by simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20256 p hg
    simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20258 (p : Pattern) (guard : d17165 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17161 p = 1 := by simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20241 p hg
    simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15558 p = 1 := by simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20257 p hg
    simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20259 (p : Pattern) (guard : d17166 p = 1) : d48346 p ≤ (1 : Int) + d173722 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17166, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17939 p hg
    simpa only [d17166, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17165 p = 1 := by simpa only [d17166, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20258 p hg
    simpa only [d17166, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20260 (p : Pattern) (guard : d17167 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17167, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17938 p hg
    simpa only [d17167, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17166 p = 1 := by simpa only [d17167, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20259 p hg
    simpa only [d17167, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20261 (p : Pattern) (guard : d17168 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17164 p = 1 := by simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20244 p hg
    simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17167 p = 1 := by simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20260 p hg
    simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20262 (p : Pattern) (guard : d17238 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17237 p = 1 := by simpa only [d17238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20229 p hg
    simpa only [d17238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17168 p = 1 := by simpa only [d17238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20261 p hg
    simpa only [d17238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20263 (p : Pattern) (guard : d17239 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17238 p = 1 := by simpa only [d17239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20262 p hg
    simpa only [d17239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17955 p hg
    simpa only [d17239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20264 (p : Pattern) (guard : d17240 p = 1) : d48356 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17239 p = 1 := by simpa only [d17240, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20263 p hg
    simpa only [d17240, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17240, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17959 p hg
    simpa only [d17240, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20265 (p : Pattern) (guard : d17241 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17241, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17937 p hg
    simpa only [d17241, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17240 p = 1 := by simpa only [d17241, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20264 p hg
    simpa only [d17241, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20266 (p : Pattern) (guard : d17242 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17167 p = 1 := by simpa only [d17242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20260 p hg
    simpa only [d17242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17955 p hg
    simpa only [d17242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20267 (p : Pattern) (guard : d17243 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17168 p = 1 := by simpa only [d17243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20261 p hg
    simpa only [d17243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17242 p = 1 := by simpa only [d17243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20266 p hg
    simpa only [d17243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20268 (p : Pattern) (guard : d17244 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17243 p = 1 := by simpa only [d17244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20267 p hg
    simpa only [d17244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17955 p hg
    simpa only [d17244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20269 (p : Pattern) (guard : d17245 p = 1) : d48356 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17244 p = 1 := by simpa only [d17245, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20268 p hg
    simpa only [d17245, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17245, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17959 p hg
    simpa only [d17245, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20270 (p : Pattern) (guard : d17246 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17246, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17937 p hg
    simpa only [d17246, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17245 p = 1 := by simpa only [d17246, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20269 p hg
    simpa only [d17246, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20271 (p : Pattern) (guard : d17247 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17241 p = 1 := by simpa only [d17247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20265 p hg
    simpa only [d17247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17246 p = 1 := by simpa only [d17247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20270 p hg
    simpa only [d17247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20272 (p : Pattern) (guard : d17248 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17247 p = 1 := by simpa only [d17248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20271 p hg
    simpa only [d17248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d17248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20273 (p : Pattern) (guard : d17249 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17248 p = 1 := by simpa only [d17249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20272 p hg
    simpa only [d17249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d17249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20274 (p : Pattern) (guard : d17323 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17249 p = 1 := by simpa only [d17323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20273 p hg
    simpa only [d17323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d17323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20275 (p : Pattern) (guard : d2064 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare20276 (p : Pattern) (guard : d2065 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2064 p = 1 := by simpa only [d2065, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20275 p hg
    simpa only [d2065, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2065, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d2065, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20277 (p : Pattern) (guard : d2066 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2065 p = 1 := by simpa only [d2066, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20276 p hg
    simpa only [d2066, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2066, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d2066, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20278 (p : Pattern) (guard : d2067 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2067, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d2067, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2066 p = 1 := by simpa only [d2067, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20277 p hg
    simpa only [d2067, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20279 (p : Pattern) (guard : d2068 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2067 p = 1 := by simpa only [d2068, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20278 p hg
    simpa only [d2068, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2068, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d2068, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20280 (p : Pattern) (guard : d2071 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2068 p = 1 := by simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20279 p hg
    simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17949 p hg
    simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20281 (p : Pattern) (guard : d15563 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2071 p = 1 := by simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20280 p hg
    simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15557 p = 1 := by simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20256 p hg
    simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20282 (p : Pattern) (guard : d17169 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17161 p = 1 := by simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20241 p hg
    simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15563 p = 1 := by simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20281 p hg
    simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20283 (p : Pattern) (guard : d17170 p = 1) : d48346 p ≤ (1 : Int) + d173722 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17170, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17939 p hg
    simpa only [d17170, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17169 p = 1 := by simpa only [d17170, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20282 p hg
    simpa only [d17170, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20284 (p : Pattern) (guard : d17171 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17171, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17938 p hg
    simpa only [d17171, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17170 p = 1 := by simpa only [d17171, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20283 p hg
    simpa only [d17171, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20285 (p : Pattern) (guard : d17172 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17171 p = 1 := by simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20284 p hg
    simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17955 p hg
    simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20286 (p : Pattern) (guard : d17177 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17172 p = 1 := by simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20285 p hg
    simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17955 p hg
    simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20287 (p : Pattern) (guard : d17178 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17177 p = 1 := by simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20286 p hg
    simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17955 p hg
    simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20288 (p : Pattern) (guard : d17179 p = 1) : d48356 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17178 p = 1 := by simpa only [d17179, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20287 p hg
    simpa only [d17179, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17179, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17959 p hg
    simpa only [d17179, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20289 (p : Pattern) (guard : d17180 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17180, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17937 p hg
    simpa only [d17180, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17179 p = 1 := by simpa only [d17180, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20288 p hg
    simpa only [d17180, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20290 (p : Pattern) (guard : d17251 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17246 p = 1 := by simpa only [d17251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20270 p hg
    simpa only [d17251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17180 p = 1 := by simpa only [d17251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20289 p hg
    simpa only [d17251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20291 (p : Pattern) (guard : d17252 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17251 p = 1 := by simpa only [d17252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20290 p hg
    simpa only [d17252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d17252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20292 (p : Pattern) (guard : d17253 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17252 p = 1 := by simpa only [d17253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20291 p hg
    simpa only [d17253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d17253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20293 (p : Pattern) (guard : d17324 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17253 p = 1 := by simpa only [d17324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20292 p hg
    simpa only [d17324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d17324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20294 (p : Pattern) (guard : d17325 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17323 p = 1 := by simpa only [d17325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20274 p hg
    simpa only [d17325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17324 p = 1 := by simpa only [d17325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20293 p hg
    simpa only [d17325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20295 (p : Pattern) (guard : d128401 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 90 with
  | false =>
    have hg : d17325 p = 1 := by simpa only [d128401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20294 p hg
    simpa only [d128401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d128401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20296 (p : Pattern) (guard : d13614 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2071 p = 1 := by simpa only [d13614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20280 p hg
    simpa only [d13614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17949 p hg
    simpa only [d13614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20297 (p : Pattern) (guard : d17294 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17161 p = 1 := by simpa only [d17294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20241 p hg
    simpa only [d17294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13614 p = 1 := by simpa only [d17294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20296 p hg
    simpa only [d17294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20298 (p : Pattern) (guard : d17295 p = 1) : d48346 p ≤ (1 : Int) + d173722 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17295, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17939 p hg
    simpa only [d17295, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17294 p = 1 := by simpa only [d17295, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20297 p hg
    simpa only [d17295, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20299 (p : Pattern) (guard : d17296 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17296, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17938 p hg
    simpa only [d17296, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17295 p = 1 := by simpa only [d17296, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20298 p hg
    simpa only [d17296, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20300 (p : Pattern) (guard : d17297 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17296 p = 1 := by simpa only [d17297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20299 p hg
    simpa only [d17297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17955 p hg
    simpa only [d17297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20301 (p : Pattern) (guard : d17298 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17168 p = 1 := by simpa only [d17298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20261 p hg
    simpa only [d17298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17297 p = 1 := by simpa only [d17298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20300 p hg
    simpa only [d17298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20302 (p : Pattern) (guard : d17299 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17298 p = 1 := by simpa only [d17299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20301 p hg
    simpa only [d17299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17955 p hg
    simpa only [d17299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20303 (p : Pattern) (guard : d17300 p = 1) : d48356 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17299 p = 1 := by simpa only [d17300, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20302 p hg
    simpa only [d17300, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17300, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17959 p hg
    simpa only [d17300, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20304 (p : Pattern) (guard : d17301 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17301, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17937 p hg
    simpa only [d17301, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17300 p = 1 := by simpa only [d17301, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20303 p hg
    simpa only [d17301, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20305 (p : Pattern) (guard : d17302 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17301 p = 1 := by simpa only [d17302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20304 p hg
    simpa only [d17302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d17302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20306 (p : Pattern) (guard : d17303 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17302 p = 1 := by simpa only [d17303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20305 p hg
    simpa only [d17303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d17303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20307 (p : Pattern) (guard : d17304 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17303 p = 1 := by simpa only [d17304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20306 p hg
    simpa only [d17304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d17304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20308 (p : Pattern) (guard : d17330 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17304 p = 1 := by simpa only [d17330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20307 p hg
    simpa only [d17330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d17330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20309 (p : Pattern) (guard : d17331 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17330 p = 1 := by simpa only [d17331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20308 p hg
    simpa only [d17331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d17331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20310 (p : Pattern) (guard : d17332 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 90 with
  | false =>
    have hg : d17331 p = 1 := by simpa only [d17332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20309 p hg
    simpa only [d17332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d17332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20311 (p : Pattern) (guard : d128402 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128401 p = 1 := by simpa only [d128402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20295 p hg
    simpa only [d128402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17332 p = 1 := by simpa only [d128402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20310 p hg
    simpa only [d128402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20312 (p : Pattern) (guard : d128410 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d128410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128402 p = 1 := by simpa only [d128410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20311 p hg
    simpa only [d128410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20313 (p : Pattern) (guard : d128411 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d128411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128410 p = 1 := by simpa only [d128411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20312 p hg
    simpa only [d128411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20314 (p : Pattern) (guard : d128412 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128412, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d128412, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128411 p = 1 := by simpa only [d128412, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20313 p hg
    simpa only [d128412, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20315 (p : Pattern) (guard : d128413 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17935 p hg
    simpa only [d128413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128412 p = 1 := by simpa only [d128413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20314 p hg
    simpa only [d128413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20316 (p : Pattern) (guard : d17185 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17180 p = 1 := by simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20289 p hg
    simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20317 (p : Pattern) (guard : d17186 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17185 p = 1 := by simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20316 p hg
    simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20318 (p : Pattern) (guard : d17187 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17186 p = 1 := by simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20317 p hg
    simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20319 (p : Pattern) (guard : d17198 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17187 p = 1 := by simpa only [d17198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20318 p hg
    simpa only [d17198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d17198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20320 (p : Pattern) (guard : d17349 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17198 p = 1 := by simpa only [d17349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20319 p hg
    simpa only [d17349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d17349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20321 (p : Pattern) (guard : d17350 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d17350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17349 p = 1 := by simpa only [d17350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20320 p hg
    simpa only [d17350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20322 (p : Pattern) (guard : d17351 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 89 with
  | false =>
    have hg : d17350 p = 1 := by simpa only [d17351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20321 p hg
    simpa only [d17351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d17351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20323 (p : Pattern) (guard : d17352 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d17352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17351 p = 1 := by simpa only [d17352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20322 p hg
    simpa only [d17352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20324 (p : Pattern) (guard : d17353 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d17353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17352 p = 1 := by simpa only [d17353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20323 p hg
    simpa only [d17353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20325 (p : Pattern) (guard : d17363 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17363, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d17363, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17353 p = 1 := by simpa only [d17363, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20324 p hg
    simpa only [d17363, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20326 (p : Pattern) (guard : d17364 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17935 p hg
    simpa only [d17364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17363 p = 1 := by simpa only [d17364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20325 p hg
    simpa only [d17364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20327 (p : Pattern) (guard : d128414 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 69 with
  | false =>
    have hg : d128413 p = 1 := by simpa only [d128414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20315 p hg
    simpa only [d128414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17364 p = 1 := by simpa only [d128414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20326 p hg
    simpa only [d128414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20328 (p : Pattern) (guard : d128415 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 51 with
  | false =>
    have hg : d128414 p = 1 := by simpa only [d128415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20327 p hg
    simpa only [d128415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17935 p hg
    simpa only [d128415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20329 (p : Pattern) (guard : d128416 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 50 with
  | false =>
    have hg : d128415 p = 1 := by simpa only [d128416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20328 p hg
    simpa only [d128416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17935 p hg
    simpa only [d128416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20330 (p : Pattern) (guard : d128417 p = 1) : d48359 p ≤ (1 : Int) + d173727 p := by
  cases selected : p 49 with
  | false =>
    have hg : d128409 p = 1 := by simpa only [d128417, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20184 p hg
    simpa only [d128417, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128416 p = 1 := by simpa only [d128417, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20329 p hg
    simpa only [d128417, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20331 (p : Pattern) (guard : d175495 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 48 with
  | false =>
    have hg : d128417 p = 1 := by simpa only [d175495, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20330 p hg
    simpa only [d175495, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175495, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17977 p hg
    simpa only [d175495, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20332 (p : Pattern) (guard : d175496 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175495 p = 1 := by simpa only [d175496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20331 p hg
    simpa only [d175496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20333 (p : Pattern) (guard : d175497 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175496 p = 1 := by simpa only [d175497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20332 p hg
    simpa only [d175497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20334 (p : Pattern) (guard : d175498 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175497 p = 1 := by simpa only [d175498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20333 p hg
    simpa only [d175498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20335 (p : Pattern) (guard : d175499 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175498 p = 1 := by simpa only [d175499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20334 p hg
    simpa only [d175499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20336 (p : Pattern) (guard : d175500 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175499 p = 1 := by simpa only [d175500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20335 p hg
    simpa only [d175500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20337 (p : Pattern) (guard : d175501 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175500 p = 1 := by simpa only [d175501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20336 p hg
    simpa only [d175501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20338 (p : Pattern) (guard : d175502 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175501 p = 1 := by simpa only [d175502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20337 p hg
    simpa only [d175502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20339 (p : Pattern) (guard : d175503 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175502 p = 1 := by simpa only [d175503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20338 p hg
    simpa only [d175503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20340 (p : Pattern) (guard : d175504 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175503 p = 1 := by simpa only [d175504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20339 p hg
    simpa only [d175504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20341 (p : Pattern) (guard : d175505 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175504 p = 1 := by simpa only [d175505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20340 p hg
    simpa only [d175505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20342 (p : Pattern) (guard : d175506 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10250 with
  | false =>
    have hg : d175494 p = 1 := by simpa only [d175506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19877 p hg
    simpa only [d175506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175505 p = 1 := by simpa only [d175506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20341 p hg
    simpa only [d175506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20343 (p : Pattern) (guard : d175507 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 260 with
  | false =>
    have hg : d175506 p = 1 := by simpa only [d175507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20342 p hg
    simpa only [d175507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20344 (p : Pattern) (guard : d175508 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 259 with
  | false =>
    have hg : d175507 p = 1 := by simpa only [d175508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20343 p hg
    simpa only [d175508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20345 (p : Pattern) (guard : d175509 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 258 with
  | false =>
    have hg : d175508 p = 1 := by simpa only [d175509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20344 p hg
    simpa only [d175509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20346 (p : Pattern) (guard : d175510 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 257 with
  | false =>
    have hg : d175509 p = 1 := by simpa only [d175510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20345 p hg
    simpa only [d175510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20347 (p : Pattern) (guard : d175511 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 256 with
  | false =>
    have hg : d175510 p = 1 := by simpa only [d175511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20346 p hg
    simpa only [d175511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20348 (p : Pattern) (guard : d175512 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 255 with
  | false =>
    have hg : d175511 p = 1 := by simpa only [d175512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20347 p hg
    simpa only [d175512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20349 (p : Pattern) (guard : d175513 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 254 with
  | false =>
    have hg : d175512 p = 1 := by simpa only [d175513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20348 p hg
    simpa only [d175513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20350 (p : Pattern) (guard : d175514 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 253 with
  | false =>
    have hg : d175513 p = 1 := by simpa only [d175514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20349 p hg
    simpa only [d175514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20351 (p : Pattern) (guard : d175515 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 252 with
  | false =>
    have hg : d175514 p = 1 := by simpa only [d175515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20350 p hg
    simpa only [d175515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20352 (p : Pattern) (guard : d175516 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 251 with
  | false =>
    have hg : d175515 p = 1 := by simpa only [d175516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20351 p hg
    simpa only [d175516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20353 (p : Pattern) (guard : d175517 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 250 with
  | false =>
    have hg : d175516 p = 1 := by simpa only [d175517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20352 p hg
    simpa only [d175517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20354 (p : Pattern) (guard : d175518 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 249 with
  | false =>
    have hg : d175517 p = 1 := by simpa only [d175518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20353 p hg
    simpa only [d175518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20355 (p : Pattern) (guard : d175519 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 245 with
  | false =>
    have hg : d175518 p = 1 := by simpa only [d175519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20354 p hg
    simpa only [d175519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20356 (p : Pattern) (guard : d175520 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 200 with
  | false =>
    have hg : d175519 p = 1 := by simpa only [d175520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20355 p hg
    simpa only [d175520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20357 (p : Pattern) (guard : d175521 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 199 with
  | false =>
    have hg : d175520 p = 1 := by simpa only [d175521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20356 p hg
    simpa only [d175521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20358 (p : Pattern) (guard : d175522 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 186 with
  | false =>
    have hg : d175521 p = 1 := by simpa only [d175522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20357 p hg
    simpa only [d175522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20359 (p : Pattern) (guard : d175523 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 185 with
  | false =>
    have hg : d175522 p = 1 := by simpa only [d175523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20358 p hg
    simpa only [d175523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20360 (p : Pattern) (guard : d175524 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 184 with
  | false =>
    have hg : d175523 p = 1 := by simpa only [d175524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20359 p hg
    simpa only [d175524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20361 (p : Pattern) (guard : d175525 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 181 with
  | false =>
    have hg : d175524 p = 1 := by simpa only [d175525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20360 p hg
    simpa only [d175525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20362 (p : Pattern) (guard : d175526 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 177 with
  | false =>
    have hg : d175525 p = 1 := by simpa only [d175526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20361 p hg
    simpa only [d175526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20363 (p : Pattern) (guard : d175527 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 164 with
  | false =>
    have hg : d175526 p = 1 := by simpa only [d175527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20362 p hg
    simpa only [d175527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20364 (p : Pattern) (guard : d175528 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 156 with
  | false =>
    have hg : d175527 p = 1 := by simpa only [d175528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20363 p hg
    simpa only [d175528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20365 (p : Pattern) (guard : d175529 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 155 with
  | false =>
    have hg : d175528 p = 1 := by simpa only [d175529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20364 p hg
    simpa only [d175529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20366 (p : Pattern) (guard : d175530 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 134 with
  | false =>
    have hg : d175529 p = 1 := by simpa only [d175530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20365 p hg
    simpa only [d175530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20367 (p : Pattern) (guard : d175531 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 133 with
  | false =>
    have hg : d175530 p = 1 := by simpa only [d175531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20366 p hg
    simpa only [d175531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20368 (p : Pattern) (guard : d175532 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 120 with
  | false =>
    have hg : d175531 p = 1 := by simpa only [d175532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20367 p hg
    simpa only [d175532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20369 (p : Pattern) (guard : d175533 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 118 with
  | false =>
    have hg : d175532 p = 1 := by simpa only [d175533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20368 p hg
    simpa only [d175533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20370 (p : Pattern) (guard : d175534 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 114 with
  | false =>
    have hg : d175533 p = 1 := by simpa only [d175534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20369 p hg
    simpa only [d175534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20371 (p : Pattern) (guard : d175535 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 111 with
  | false =>
    have hg : d175534 p = 1 := by simpa only [d175535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20370 p hg
    simpa only [d175535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20372 (p : Pattern) (guard : d175536 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 98 with
  | false =>
    have hg : d175535 p = 1 := by simpa only [d175536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20371 p hg
    simpa only [d175536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20373 (p : Pattern) (guard : d175537 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 97 with
  | false =>
    have hg : d175536 p = 1 := by simpa only [d175537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20372 p hg
    simpa only [d175537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20374 (p : Pattern) (guard : d175538 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 94 with
  | false =>
    have hg : d175537 p = 1 := by simpa only [d175538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20373 p hg
    simpa only [d175538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20375 (p : Pattern) (guard : d175539 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 76 with
  | false =>
    have hg : d175538 p = 1 := by simpa only [d175539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20374 p hg
    simpa only [d175539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20376 (p : Pattern) (guard : d175540 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 67 with
  | false =>
    have hg : d175539 p = 1 := by simpa only [d175540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20375 p hg
    simpa only [d175540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20377 (p : Pattern) (guard : d175541 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 52 with
  | false =>
    have hg : d175540 p = 1 := by simpa only [d175541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20376 p hg
    simpa only [d175541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20378 (p : Pattern) (guard : d175542 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 47 with
  | false =>
    have hg : d175541 p = 1 := by simpa only [d175542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20377 p hg
    simpa only [d175542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20379 (p : Pattern) (guard : d175543 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 46 with
  | false =>
    have hg : d175542 p = 1 := by simpa only [d175543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20378 p hg
    simpa only [d175543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20380 (p : Pattern) (guard : d175544 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 45 with
  | false =>
    have hg : d175543 p = 1 := by simpa only [d175544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20379 p hg
    simpa only [d175544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20381 (p : Pattern) (guard : d175545 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 30 with
  | false =>
    have hg : d175544 p = 1 := by simpa only [d175545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20380 p hg
    simpa only [d175545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20382 (p : Pattern) (guard : d175546 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 29 with
  | false =>
    have hg : d175545 p = 1 := by simpa only [d175546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20381 p hg
    simpa only [d175546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20383 (p : Pattern) (guard : d175547 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 28 with
  | false =>
    have hg : d175546 p = 1 := by simpa only [d175547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20382 p hg
    simpa only [d175547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20384 (p : Pattern) (guard : d175548 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 27 with
  | false =>
    have hg : d175547 p = 1 := by simpa only [d175548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20383 p hg
    simpa only [d175548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20385 (p : Pattern) (guard : d175549 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 25 with
  | false =>
    have hg : d175548 p = 1 := by simpa only [d175549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20384 p hg
    simpa only [d175549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20386 (p : Pattern) (guard : d0 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20387 (p : Pattern) (guard : d0 p = 1) : d48340 p ≤ (0 : Int) + d173717 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20388 (p : Pattern) (guard : d0 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20389 (p : Pattern) (guard : d0 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20390 (p : Pattern) (guard : d0 p = 1) : d48336 p ≤ (0 : Int) + d173714 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20391 (p : Pattern) (guard : d0 p = 1) : d48317 p ≤ (0 : Int) + d173707 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20392 (p : Pattern) (guard : d0 p = 1) : d48325 p ≤ (0 : Int) + d173705 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20393 (p : Pattern) (guard : d0 p = 1) : d47655 p ≤ (0 : Int) + d47654 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20394 (p : Pattern) (guard : d24 p = 1) : d47619 p ≤ (0 : Int) + d47619 p := by
  omega
theorem compare20395 (p : Pattern) (guard : d0 p = 1) : d47659 p ≤ (0 : Int) + d47625 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20396 (p : Pattern) (guard : d25 p = 1) : d47660 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d24 p = 1 := by simpa only [d25, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20394 p hg
    simpa only [d25, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20395 p hg
    simpa only [d25, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20397 (p : Pattern) (guard : d0 p = 1) : d47662 p ≤ (0 : Int) + d47654 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20398 (p : Pattern) (guard : d26 p = 1) : d47663 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d25 p = 1 := by simpa only [d26, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20396 p hg
    simpa only [d26, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d26, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20397 p hg
    simpa only [d26, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20399 (p : Pattern) (guard : d27 p = 1) : d47664 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d27, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20393 p hg
    simpa only [d27, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d26 p = 1 := by simpa only [d27, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20398 p hg
    simpa only [d27, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20400 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d48408 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20401 (p : Pattern) (guard : d28 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d27 p = 1 := by simpa only [d28, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20399 p hg
    simpa only [d28, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d28, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20400 p hg
    simpa only [d28, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20402 (p : Pattern) (guard : d0 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20403 (p : Pattern) (guard : d29 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d28 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20401 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20402 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20404 (p : Pattern) (guard : d30 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d29 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20403 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20402 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20405 (p : Pattern) (guard : d31 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 157 with
  | false =>
    have hg : d30 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20404 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20402 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20406 (p : Pattern) (guard : d32 p = 1) : d48326 p ≤ (0 : Int) + d173709 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d32, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20392 p hg
    simpa only [d32, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d31 p = 1 := by simpa only [d32, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20405 p hg
    simpa only [d32, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20407 (p : Pattern) (guard : d33 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d33, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20391 p hg
    simpa only [d33, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32 p = 1 := by simpa only [d33, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20406 p hg
    simpa only [d33, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20408 (p : Pattern) (guard : d0 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20409 (p : Pattern) (guard : d34 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d33 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20407 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20408 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20410 (p : Pattern) (guard : d35 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d34 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20409 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20408 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20411 (p : Pattern) (guard : d36 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d35 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20410 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20408 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20412 (p : Pattern) (guard : d0 p = 1) : d48328 p ≤ (0 : Int) + d173715 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20413 (p : Pattern) (guard : d37 p = 1) : d48338 p ≤ (0 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d36 p = 1 := by simpa only [d37, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20411 p hg
    simpa only [d37, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d37, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20412 p hg
    simpa only [d37, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20414 (p : Pattern) (guard : d38 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20390 p hg
    simpa only [d38, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d37 p = 1 := by simpa only [d38, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20413 p hg
    simpa only [d38, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20415 (p : Pattern) (guard : d39 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d38 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20414 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20416 (p : Pattern) (guard : d40 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d39 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20415 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20417 (p : Pattern) (guard : d41 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d40 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20416 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20418 (p : Pattern) (guard : d42 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d41 p = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20417 p hg
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20419 (p : Pattern) (guard : d43 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d42 p = 1 := by simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20418 p hg
    simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20420 (p : Pattern) (guard : d100 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d43 p = 1 := by simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20419 p hg
    simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20421 (p : Pattern) (guard : d101 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d100 p = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20420 p hg
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20422 (p : Pattern) (guard : d102 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101 p = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20421 p hg
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20423 (p : Pattern) (guard : d103 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d102 p = 1 := by simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20422 p hg
    simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20424 (p : Pattern) (guard : d104 p = 1) : d48340 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d104, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d104, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d103 p = 1 := by simpa only [d104, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20423 p hg
    simpa only [d104, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20425 (p : Pattern) (guard : d0 p = 1) : d48321 p ≤ (0 : Int) + d173714 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20426 (p : Pattern) (guard : d0 p = 1) : d48324 p ≤ (0 : Int) + d173707 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20427 (p : Pattern) (guard : d33 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d33, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20426 p hg
    simpa only [d33, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32 p = 1 := by simpa only [d33, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20406 p hg
    simpa only [d33, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20428 (p : Pattern) (guard : d0 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20429 (p : Pattern) (guard : d34 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d33 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20427 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20428 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20430 (p : Pattern) (guard : d35 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d34 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20429 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20428 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20431 (p : Pattern) (guard : d36 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d35 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20430 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20428 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20432 (p : Pattern) (guard : d37 p = 1) : d48329 p ≤ (0 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d36 p = 1 := by simpa only [d37, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20431 p hg
    simpa only [d37, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d37, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20412 p hg
    simpa only [d37, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20433 (p : Pattern) (guard : d38 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20425 p hg
    simpa only [d38, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d37 p = 1 := by simpa only [d38, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20432 p hg
    simpa only [d38, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20434 (p : Pattern) (guard : d39 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d38 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20433 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20435 (p : Pattern) (guard : d40 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d39 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20434 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20436 (p : Pattern) (guard : d41 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d40 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20435 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20437 (p : Pattern) (guard : d42 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d41 p = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20436 p hg
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20438 (p : Pattern) (guard : d43 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d42 p = 1 := by simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20437 p hg
    simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20439 (p : Pattern) (guard : d100 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d43 p = 1 := by simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20438 p hg
    simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20440 (p : Pattern) (guard : d101 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d100 p = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20439 p hg
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20441 (p : Pattern) (guard : d102 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101 p = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20440 p hg
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20442 (p : Pattern) (guard : d103 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d102 p = 1 := by simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20441 p hg
    simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20443 (p : Pattern) (guard : d49 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d41 p = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20417 p hg
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20444 (p : Pattern) (guard : d50 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d49 p = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20443 p hg
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20445 (p : Pattern) (guard : d107 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d50 p = 1 := by simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20444 p hg
    simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20446 (p : Pattern) (guard : d108 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d107 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20445 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20447 (p : Pattern) (guard : d109 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d108 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20446 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20448 (p : Pattern) (guard : d110 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d109 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20447 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20449 (p : Pattern) (guard : d111 p = 1) : d48340 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d103 p = 1 := by simpa only [d111, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20442 p hg
    simpa only [d111, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d110 p = 1 := by simpa only [d111, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20448 p hg
    simpa only [d111, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20450 (p : Pattern) (guard : d112 p = 1) : d48340 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 70 with
  | false =>
    have hg : d104 p = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20424 p hg
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d111 p = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20449 p hg
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20451 (p : Pattern) (guard : d113 p = 1) : d48340 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 69 with
  | false =>
    have hg : d112 p = 1 := by simpa only [d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20450 p hg
    simpa only [d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20387 p hg
    simpa only [d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20452 (p : Pattern) (guard : d53637 p = 1) : d48340 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 51 with
  | false =>
    have hg : d113 p = 1 := by simpa only [d53637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20451 p hg
    simpa only [d53637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20387 p hg
    simpa only [d53637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20453 (p : Pattern) (guard : d53638 p = 1) : d48340 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20387 p hg
    simpa only [d53638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53637 p = 1 := by simpa only [d53638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20452 p hg
    simpa only [d53638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20454 (p : Pattern) (guard : d0 p = 1) : d48358 p ≤ (0 : Int) + d173726 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20455 (p : Pattern) (guard : d0 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20456 (p : Pattern) (guard : d0 p = 1) : d48351 p ≤ (0 : Int) + d173725 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20457 (p : Pattern) (guard : d0 p = 1) : d48353 p ≤ (0 : Int) + d173720 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20458 (p : Pattern) (guard : d0 p = 1) : d48344 p ≤ (0 : Int) + d173718 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20459 (p : Pattern) (guard : d0 p = 1) : d47734 p ≤ (0 : Int) + d47733 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20460 (p : Pattern) (guard : d24 p = 1) : d47708 p ≤ (0 : Int) + d47708 p := by
  omega
theorem compare20461 (p : Pattern) (guard : d25 p = 1) : d47735 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d24 p = 1 := by simpa only [d25, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20460 p hg
    simpa only [d25, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d25, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20462 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d47733 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20463 (p : Pattern) (guard : d26 p = 1) : d47736 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d25 p = 1 := by simpa only [d26, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20461 p hg
    simpa only [d26, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d26, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20462 p hg
    simpa only [d26, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20464 (p : Pattern) (guard : d27 p = 1) : d47737 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d27, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20459 p hg
    simpa only [d27, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d26 p = 1 := by simpa only [d27, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20463 p hg
    simpa only [d27, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20465 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d47752 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20466 (p : Pattern) (guard : d28 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d27 p = 1 := by simpa only [d28, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20464 p hg
    simpa only [d28, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d28, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20465 p hg
    simpa only [d28, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20467 (p : Pattern) (guard : d0 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20468 (p : Pattern) (guard : d29 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d28 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20466 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20467 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20469 (p : Pattern) (guard : d30 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d29 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20468 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20467 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20470 (p : Pattern) (guard : d31 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 157 with
  | false =>
    have hg : d30 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20469 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20467 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20471 (p : Pattern) (guard : d32 p = 1) : d48346 p ≤ (0 : Int) + d173722 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d32, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20458 p hg
    simpa only [d32, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d31 p = 1 := by simpa only [d32, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20470 p hg
    simpa only [d32, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20472 (p : Pattern) (guard : d33 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d33, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20457 p hg
    simpa only [d33, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32 p = 1 := by simpa only [d33, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20471 p hg
    simpa only [d33, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20473 (p : Pattern) (guard : d0 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20474 (p : Pattern) (guard : d34 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 136 with
  | false =>
    have hg : d33 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20472 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20473 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20475 (p : Pattern) (guard : d35 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 135 with
  | false =>
    have hg : d34 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20474 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20473 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20476 (p : Pattern) (guard : d36 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 119 with
  | false =>
    have hg : d35 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20475 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20473 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20477 (p : Pattern) (guard : d0 p = 1) : d48355 p ≤ (0 : Int) + d173724 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20478 (p : Pattern) (guard : d37 p = 1) : d48356 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 116 with
  | false =>
    have hg : d36 p = 1 := by simpa only [d37, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20476 p hg
    simpa only [d37, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d37, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20477 p hg
    simpa only [d37, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20479 (p : Pattern) (guard : d38 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20456 p hg
    simpa only [d38, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d37 p = 1 := by simpa only [d38, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20478 p hg
    simpa only [d38, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20480 (p : Pattern) (guard : d39 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 113 with
  | false =>
    have hg : d38 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20479 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20481 (p : Pattern) (guard : d40 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 96 with
  | false =>
    have hg : d39 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20480 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20482 (p : Pattern) (guard : d41 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 95 with
  | false =>
    have hg : d40 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20481 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20483 (p : Pattern) (guard : d49 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 93 with
  | false =>
    have hg : d41 p = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20482 p hg
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20484 (p : Pattern) (guard : d50 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 91 with
  | false =>
    have hg : d49 p = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20483 p hg
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20485 (p : Pattern) (guard : d107 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d50 p = 1 := by simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20484 p hg
    simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20486 (p : Pattern) (guard : d108 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 89 with
  | false =>
    have hg : d107 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20485 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20487 (p : Pattern) (guard : d109 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d108 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20486 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20488 (p : Pattern) (guard : d110 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d109 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20487 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20489 (p : Pattern) (guard : d406 p = 1) : d48358 p ≤ (0 : Int) + d173726 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d406, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d406, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d110 p = 1 := by simpa only [d406, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20488 p hg
    simpa only [d406, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20490 (p : Pattern) (guard : d407 p = 1) : d48358 p ≤ (0 : Int) + d173726 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20454 p hg
    simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d406 p = 1 := by simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20489 p hg
    simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20491 (p : Pattern) (guard : d53639 p = 1) : d48358 p ≤ (0 : Int) + d173726 p := by
  cases selected : p 69 with
  | false =>
    have hg : d407 p = 1 := by simpa only [d53639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20490 p hg
    simpa only [d53639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20454 p hg
    simpa only [d53639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20492 (p : Pattern) (guard : d53640 p = 1) : d48358 p ≤ (0 : Int) + d173726 p := by
  cases selected : p 51 with
  | false =>
    have hg : d53639 p = 1 := by simpa only [d53640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20491 p hg
    simpa only [d53640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20454 p hg
    simpa only [d53640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20493 (p : Pattern) (guard : d53641 p = 1) : d48358 p ≤ (0 : Int) + d173726 p := by
  cases selected : p 50 with
  | false =>
    have hg : d53640 p = 1 := by simpa only [d53641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20492 p hg
    simpa only [d53641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20454 p hg
    simpa only [d53641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20494 (p : Pattern) (guard : d53642 p = 1) : d48359 p ≤ (0 : Int) + d173727 p := by
  cases selected : p 49 with
  | false =>
    have hg : d53638 p = 1 := by simpa only [d53642, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20453 p hg
    simpa only [d53642, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53641 p = 1 := by simpa only [d53642, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20493 p hg
    simpa only [d53642, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20495 (p : Pattern) (guard : d0 p = 1) : d48387 p ≤ (0 : Int) + d173754 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare20496 (p : Pattern) (guard : d54404 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 48 with
  | false =>
    have hg : d53642 p = 1 := by simpa only [d54404, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20494 p hg
    simpa only [d54404, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d54404, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20495 p hg
    simpa only [d54404, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20497 (p : Pattern) (guard : d54405 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d54405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54404 p = 1 := by simpa only [d54405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20496 p hg
    simpa only [d54405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20498 (p : Pattern) (guard : d54406 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d54406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54405 p = 1 := by simpa only [d54406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20497 p hg
    simpa only [d54406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare20499 (p : Pattern) (guard : d54407 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d54407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54406 p = 1 := by simpa only [d54407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20498 p hg
    simpa only [d54407, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
