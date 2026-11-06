import NetHack.Soko22Hazard87.Compare072
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare18250 (p : Pattern) (guard : d318 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare18251 (p : Pattern) (guard : d319 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d318 p = 1 := by simpa only [d319, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18250 p hg
    simpa only [d319, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d319, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d319, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18252 (p : Pattern) (guard : d320 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d319 p = 1 := by simpa only [d320, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18251 p hg
    simpa only [d320, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d320, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d320, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18253 (p : Pattern) (guard : d321 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d321, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d321, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d320 p = 1 := by simpa only [d321, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18252 p hg
    simpa only [d321, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18254 (p : Pattern) (guard : d322 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d321 p = 1 := by simpa only [d322, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18253 p hg
    simpa only [d322, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d322, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d322, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18255 (p : Pattern) (guard : d323 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d322 p = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18254 p hg
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d142 p = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18092 p hg
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18256 (p : Pattern) (guard : d9381 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare18257 (p : Pattern) (guard : d9382 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9381 p = 1 := by simpa only [d9382, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18256 p hg
    simpa only [d9382, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9382, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d9382, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18258 (p : Pattern) (guard : d9384 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9382 p = 1 := by simpa only [d9384, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18257 p hg
    simpa only [d9384, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9384, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d9384, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18259 (p : Pattern) (guard : d12493 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d12493, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d12493, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9384 p = 1 := by simpa only [d12493, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18258 p hg
    simpa only [d12493, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18260 (p : Pattern) (guard : d12494 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d12493 p = 1 := by simpa only [d12494, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18259 p hg
    simpa only [d12494, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d12494, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d12494, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18261 (p : Pattern) (guard : d12495 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d12494 p = 1 := by simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18260 p hg
    simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d28 p = 1 := by simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17948 p hg
    simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18262 (p : Pattern) (guard : d15966 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d323 p = 1 := by simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18255 p hg
    simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12495 p = 1 := by simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18261 p hg
    simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18263 (p : Pattern) (guard : d15967 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 157 with
  | false =>
    have hg : d15966 p = 1 := by simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18262 p hg
    simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d144 p = 1 := by simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18094 p hg
    simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18264 (p : Pattern) (guard : d15968 p = 1) : d48346 p ≤ (1 : Int) + d173722 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15968, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17939 p hg
    simpa only [d15968, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15967 p = 1 := by simpa only [d15968, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18263 p hg
    simpa only [d15968, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18265 (p : Pattern) (guard : d15969 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15969, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17938 p hg
    simpa only [d15969, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15968 p = 1 := by simpa only [d15969, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18264 p hg
    simpa only [d15969, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18266 (p : Pattern) (guard : d15970 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 136 with
  | false =>
    have hg : d15969 p = 1 := by simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18265 p hg
    simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d147 p = 1 := by simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18097 p hg
    simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18267 (p : Pattern) (guard : d15971 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 135 with
  | false =>
    have hg : d15970 p = 1 := by simpa only [d15971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18266 p hg
    simpa only [d15971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d148 p = 1 := by simpa only [d15971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18098 p hg
    simpa only [d15971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18268 (p : Pattern) (guard : d15972 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 119 with
  | false =>
    have hg : d15971 p = 1 := by simpa only [d15972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18267 p hg
    simpa only [d15972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17955 p hg
    simpa only [d15972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18269 (p : Pattern) (guard : d15973 p = 1) : d48356 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 116 with
  | false =>
    have hg : d15972 p = 1 := by simpa only [d15973, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18268 p hg
    simpa only [d15973, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15973, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17959 p hg
    simpa only [d15973, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18270 (p : Pattern) (guard : d15974 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15974, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17937 p hg
    simpa only [d15974, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15973 p = 1 := by simpa only [d15974, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18269 p hg
    simpa only [d15974, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18271 (p : Pattern) (guard : d15975 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 113 with
  | false =>
    have hg : d15974 p = 1 := by simpa only [d15975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18270 p hg
    simpa only [d15975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d152 p = 1 := by simpa only [d15975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18102 p hg
    simpa only [d15975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18272 (p : Pattern) (guard : d15976 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 96 with
  | false =>
    have hg : d15975 p = 1 := by simpa only [d15976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18271 p hg
    simpa only [d15976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d15976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18273 (p : Pattern) (guard : d15977 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 95 with
  | false =>
    have hg : d15976 p = 1 := by simpa only [d15977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18272 p hg
    simpa only [d15977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d15977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18274 (p : Pattern) (guard : d15985 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 93 with
  | false =>
    have hg : d15977 p = 1 := by simpa only [d15985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18273 p hg
    simpa only [d15985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d15985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18275 (p : Pattern) (guard : d15986 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 91 with
  | false =>
    have hg : d15985 p = 1 := by simpa only [d15986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18274 p hg
    simpa only [d15986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d203 p = 1 := by simpa only [d15986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18106 p hg
    simpa only [d15986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18276 (p : Pattern) (guard : d128196 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 90 with
  | false =>
    have hg : d15986 p = 1 := by simpa only [d128196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18275 p hg
    simpa only [d128196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d128196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18277 (p : Pattern) (guard : d4733 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 113 with
  | false =>
    have hg : d152 p = 1 := by simpa only [d4733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18102 p hg
    simpa only [d4733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d4733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18278 (p : Pattern) (guard : d4734 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 96 with
  | false =>
    have hg : d4733 p = 1 := by simpa only [d4734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18277 p hg
    simpa only [d4734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d4734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18279 (p : Pattern) (guard : d4735 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 95 with
  | false =>
    have hg : d4734 p = 1 := by simpa only [d4735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18278 p hg
    simpa only [d4735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d4735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18280 (p : Pattern) (guard : d5355 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 93 with
  | false =>
    have hg : d4735 p = 1 := by simpa only [d5355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18279 p hg
    simpa only [d5355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d5355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18281 (p : Pattern) (guard : d5356 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 91 with
  | false =>
    have hg : d5355 p = 1 := by simpa only [d5356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18280 p hg
    simpa only [d5356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d5356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18282 (p : Pattern) (guard : d5357 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 90 with
  | false =>
    have hg : d5356 p = 1 := by simpa only [d5357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18281 p hg
    simpa only [d5357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d5357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18283 (p : Pattern) (guard : d128197 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128196 p = 1 := by simpa only [d128197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18276 p hg
    simpa only [d128197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5357 p = 1 := by simpa only [d128197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18282 p hg
    simpa only [d128197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18284 (p : Pattern) (guard : d128205 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d128205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128197 p = 1 := by simpa only [d128205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18283 p hg
    simpa only [d128205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18285 (p : Pattern) (guard : d128206 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d128206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128205 p = 1 := by simpa only [d128206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18284 p hg
    simpa only [d128206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18286 (p : Pattern) (guard : d128207 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128207, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d128207, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128206 p = 1 := by simpa only [d128207, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18285 p hg
    simpa only [d128207, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18287 (p : Pattern) (guard : d128208 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17935 p hg
    simpa only [d128208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128207 p = 1 := by simpa only [d128208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18286 p hg
    simpa only [d128208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18288 (p : Pattern) (guard : d107 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d50 p = 1 := by simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17966 p hg
    simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18289 (p : Pattern) (guard : d108 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 89 with
  | false =>
    have hg : d107 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18288 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18290 (p : Pattern) (guard : d109 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d108 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18289 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18291 (p : Pattern) (guard : d110 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d109 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18290 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18292 (p : Pattern) (guard : d406 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d406, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d406, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d110 p = 1 := by simpa only [d406, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18291 p hg
    simpa only [d406, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18293 (p : Pattern) (guard : d407 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17935 p hg
    simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d406 p = 1 := by simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18292 p hg
    simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18294 (p : Pattern) (guard : d128209 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 69 with
  | false =>
    have hg : d128208 p = 1 := by simpa only [d128209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18287 p hg
    simpa only [d128209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d407 p = 1 := by simpa only [d128209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18293 p hg
    simpa only [d128209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18295 (p : Pattern) (guard : d128210 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 51 with
  | false =>
    have hg : d128209 p = 1 := by simpa only [d128210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18294 p hg
    simpa only [d128210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17935 p hg
    simpa only [d128210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18296 (p : Pattern) (guard : d128211 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 50 with
  | false =>
    have hg : d128210 p = 1 := by simpa only [d128211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18295 p hg
    simpa only [d128211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17935 p hg
    simpa only [d128211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18297 (p : Pattern) (guard : d128212 p = 1) : d48359 p ≤ (1 : Int) + d173727 p := by
  cases selected : p 49 with
  | false =>
    have hg : d128204 p = 1 := by simpa only [d128212, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18249 p hg
    simpa only [d128212, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128211 p = 1 := by simpa only [d128212, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18296 p hg
    simpa only [d128212, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18298 (p : Pattern) (guard : d175450 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 48 with
  | false =>
    have hg : d128212 p = 1 := by simpa only [d175450, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18297 p hg
    simpa only [d175450, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175450, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17977 p hg
    simpa only [d175450, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18299 (p : Pattern) (guard : d175451 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175450 p = 1 := by simpa only [d175451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18298 p hg
    simpa only [d175451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18300 (p : Pattern) (guard : d175452 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175451 p = 1 := by simpa only [d175452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18299 p hg
    simpa only [d175452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18301 (p : Pattern) (guard : d175453 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175452 p = 1 := by simpa only [d175453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18300 p hg
    simpa only [d175453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18302 (p : Pattern) (guard : d175454 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175453 p = 1 := by simpa only [d175454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18301 p hg
    simpa only [d175454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18303 (p : Pattern) (guard : d175455 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175454 p = 1 := by simpa only [d175455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18302 p hg
    simpa only [d175455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18304 (p : Pattern) (guard : d175456 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d54303 p = 1 := by simpa only [d175456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18123 p hg
    simpa only [d175456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175455 p = 1 := by simpa only [d175456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18303 p hg
    simpa only [d175456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18305 (p : Pattern) (guard : d475 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d147 p = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18023 p hg
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17889 p hg
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18306 (p : Pattern) (guard : d16035 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d15970 p = 1 := by simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18171 p hg
    simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d475 p = 1 := by simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18305 p hg
    simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18307 (p : Pattern) (guard : d16036 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16035 p = 1 := by simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18306 p hg
    simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17889 p hg
    simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18308 (p : Pattern) (guard : d16037 p = 1) : d48338 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16036 p = 1 := by simpa only [d16037, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18307 p hg
    simpa only [d16037, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16037, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d16037, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18309 (p : Pattern) (guard : d16038 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16038, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17871 p hg
    simpa only [d16038, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16037 p = 1 := by simpa only [d16038, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18308 p hg
    simpa only [d16038, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18310 (p : Pattern) (guard : d480 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d475 p = 1 := by simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18305 p hg
    simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17889 p hg
    simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18311 (p : Pattern) (guard : d481 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d480 p = 1 := by simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18310 p hg
    simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17889 p hg
    simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18312 (p : Pattern) (guard : d482 p = 1) : d48338 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d481 p = 1 := by simpa only [d482, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18311 p hg
    simpa only [d482, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d482, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d482, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18313 (p : Pattern) (guard : d483 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d483, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17871 p hg
    simpa only [d483, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d482 p = 1 := by simpa only [d483, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18312 p hg
    simpa only [d483, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18314 (p : Pattern) (guard : d16039 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16038 p = 1 := by simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18309 p hg
    simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d483 p = 1 := by simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18313 p hg
    simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18315 (p : Pattern) (guard : d16040 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16039 p = 1 := by simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18314 p hg
    simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18316 (p : Pattern) (guard : d16041 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16040 p = 1 := by simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18315 p hg
    simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18317 (p : Pattern) (guard : d16042 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16041 p = 1 := by simpa only [d16042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18316 p hg
    simpa only [d16042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18318 (p : Pattern) (guard : d488 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d483 p = 1 := by simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18313 p hg
    simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18319 (p : Pattern) (guard : d489 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d488 p = 1 := by simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18318 p hg
    simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18320 (p : Pattern) (guard : d490 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d489 p = 1 := by simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18319 p hg
    simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18321 (p : Pattern) (guard : d491 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d490 p = 1 := by simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18320 p hg
    simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18322 (p : Pattern) (guard : d16043 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16042 p = 1 := by simpa only [d16043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18317 p hg
    simpa only [d16043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d491 p = 1 := by simpa only [d16043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18321 p hg
    simpa only [d16043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18323 (p : Pattern) (guard : d16044 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16043 p = 1 := by simpa only [d16044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18322 p hg
    simpa only [d16044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18324 (p : Pattern) (guard : d16045 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16044 p = 1 := by simpa only [d16045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18323 p hg
    simpa only [d16045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18325 (p : Pattern) (guard : d16046 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16045 p = 1 := by simpa only [d16046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18324 p hg
    simpa only [d16046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18326 (p : Pattern) (guard : d16047 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16046 p = 1 := by simpa only [d16047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18325 p hg
    simpa only [d16047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18327 (p : Pattern) (guard : d16048 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16048, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16048, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16047 p = 1 := by simpa only [d16048, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18326 p hg
    simpa only [d16048, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18328 (p : Pattern) (guard : d16049 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17868 p hg
    simpa only [d16049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16048 p = 1 := by simpa only [d16049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18327 p hg
    simpa only [d16049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18329 (p : Pattern) (guard : d16050 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 69 with
  | false =>
    have hg : d16049 p = 1 := by simpa only [d16050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18328 p hg
    simpa only [d16050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17868 p hg
    simpa only [d16050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18330 (p : Pattern) (guard : d475 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d147 p = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18051 p hg
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17909 p hg
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18331 (p : Pattern) (guard : d16035 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d15970 p = 1 := by simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18205 p hg
    simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d475 p = 1 := by simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18330 p hg
    simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18332 (p : Pattern) (guard : d16036 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16035 p = 1 := by simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18331 p hg
    simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17909 p hg
    simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18333 (p : Pattern) (guard : d16037 p = 1) : d48329 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16036 p = 1 := by simpa only [d16037, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18332 p hg
    simpa only [d16037, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16037, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d16037, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18334 (p : Pattern) (guard : d16038 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16038, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17906 p hg
    simpa only [d16038, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16037 p = 1 := by simpa only [d16038, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18333 p hg
    simpa only [d16038, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18335 (p : Pattern) (guard : d480 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d475 p = 1 := by simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18330 p hg
    simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17909 p hg
    simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18336 (p : Pattern) (guard : d481 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d480 p = 1 := by simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18335 p hg
    simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17909 p hg
    simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18337 (p : Pattern) (guard : d482 p = 1) : d48329 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d481 p = 1 := by simpa only [d482, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18336 p hg
    simpa only [d482, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d482, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d482, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18338 (p : Pattern) (guard : d483 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d483, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17906 p hg
    simpa only [d483, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d482 p = 1 := by simpa only [d483, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18337 p hg
    simpa only [d483, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18339 (p : Pattern) (guard : d16039 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16038 p = 1 := by simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18334 p hg
    simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d483 p = 1 := by simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18338 p hg
    simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18340 (p : Pattern) (guard : d16040 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16039 p = 1 := by simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18339 p hg
    simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18341 (p : Pattern) (guard : d16041 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16040 p = 1 := by simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18340 p hg
    simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18342 (p : Pattern) (guard : d16042 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16041 p = 1 := by simpa only [d16042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18341 p hg
    simpa only [d16042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18343 (p : Pattern) (guard : d488 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d483 p = 1 := by simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18338 p hg
    simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18344 (p : Pattern) (guard : d489 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d488 p = 1 := by simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18343 p hg
    simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18345 (p : Pattern) (guard : d490 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d489 p = 1 := by simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18344 p hg
    simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18346 (p : Pattern) (guard : d491 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d490 p = 1 := by simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18345 p hg
    simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18347 (p : Pattern) (guard : d16043 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16042 p = 1 := by simpa only [d16043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18342 p hg
    simpa only [d16043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d491 p = 1 := by simpa only [d16043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18346 p hg
    simpa only [d16043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18348 (p : Pattern) (guard : d16044 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16043 p = 1 := by simpa only [d16044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18347 p hg
    simpa only [d16044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18349 (p : Pattern) (guard : d16045 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16044 p = 1 := by simpa only [d16045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18348 p hg
    simpa only [d16045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18350 (p : Pattern) (guard : d16046 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16045 p = 1 := by simpa only [d16046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18349 p hg
    simpa only [d16046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18351 (p : Pattern) (guard : d16047 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16046 p = 1 := by simpa only [d16047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18350 p hg
    simpa only [d16047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18352 (p : Pattern) (guard : d16051 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16041 p = 1 := by simpa only [d16051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18316 p hg
    simpa only [d16051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18353 (p : Pattern) (guard : d501 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d490 p = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18320 p hg
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18354 (p : Pattern) (guard : d16052 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16051 p = 1 := by simpa only [d16052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18352 p hg
    simpa only [d16052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d501 p = 1 := by simpa only [d16052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18353 p hg
    simpa only [d16052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18355 (p : Pattern) (guard : d16053 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16052 p = 1 := by simpa only [d16053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18354 p hg
    simpa only [d16053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18356 (p : Pattern) (guard : d16054 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16053 p = 1 := by simpa only [d16054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18355 p hg
    simpa only [d16054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18357 (p : Pattern) (guard : d16055 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16054 p = 1 := by simpa only [d16055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18356 p hg
    simpa only [d16055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18358 (p : Pattern) (guard : d16056 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16055 p = 1 := by simpa only [d16056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18357 p hg
    simpa only [d16056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18359 (p : Pattern) (guard : d16057 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d16047 p = 1 := by simpa only [d16057, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18351 p hg
    simpa only [d16057, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16056 p = 1 := by simpa only [d16057, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18358 p hg
    simpa only [d16057, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18360 (p : Pattern) (guard : d16058 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 70 with
  | false =>
    have hg : d16048 p = 1 := by simpa only [d16058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18327 p hg
    simpa only [d16058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16057 p = 1 := by simpa only [d16058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18359 p hg
    simpa only [d16058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18361 (p : Pattern) (guard : d16059 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 69 with
  | false =>
    have hg : d16058 p = 1 := by simpa only [d16059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18360 p hg
    simpa only [d16059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17868 p hg
    simpa only [d16059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18362 (p : Pattern) (guard : d16060 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 51 with
  | false =>
    have hg : d16050 p = 1 := by simpa only [d16060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18329 p hg
    simpa only [d16060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16059 p = 1 := by simpa only [d16060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18361 p hg
    simpa only [d16060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18363 (p : Pattern) (guard : d16061 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16040 p = 1 := by simpa only [d16061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18315 p hg
    simpa only [d16061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18364 (p : Pattern) (guard : d16062 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16061 p = 1 := by simpa only [d16062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18363 p hg
    simpa only [d16062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18365 (p : Pattern) (guard : d513 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d489 p = 1 := by simpa only [d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18319 p hg
    simpa only [d513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18366 (p : Pattern) (guard : d514 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d513 p = 1 := by simpa only [d514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18365 p hg
    simpa only [d514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18367 (p : Pattern) (guard : d16063 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16062 p = 1 := by simpa only [d16063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18364 p hg
    simpa only [d16063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d514 p = 1 := by simpa only [d16063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18366 p hg
    simpa only [d16063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18368 (p : Pattern) (guard : d16064 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16063 p = 1 := by simpa only [d16064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18367 p hg
    simpa only [d16064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18369 (p : Pattern) (guard : d16065 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16064 p = 1 := by simpa only [d16065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18368 p hg
    simpa only [d16065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18370 (p : Pattern) (guard : d16066 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16065 p = 1 := by simpa only [d16066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18369 p hg
    simpa only [d16066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18371 (p : Pattern) (guard : d16067 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16039 p = 1 := by simpa only [d16067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18314 p hg
    simpa only [d16067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18372 (p : Pattern) (guard : d16068 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16067 p = 1 := by simpa only [d16068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18371 p hg
    simpa only [d16068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18373 (p : Pattern) (guard : d16069 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16068 p = 1 := by simpa only [d16069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18372 p hg
    simpa only [d16069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18374 (p : Pattern) (guard : d522 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d488 p = 1 := by simpa only [d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18318 p hg
    simpa only [d522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18375 (p : Pattern) (guard : d523 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d522 p = 1 := by simpa only [d523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18374 p hg
    simpa only [d523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18376 (p : Pattern) (guard : d524 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d523 p = 1 := by simpa only [d524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18375 p hg
    simpa only [d524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18377 (p : Pattern) (guard : d16070 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16069 p = 1 := by simpa only [d16070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18373 p hg
    simpa only [d16070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d524 p = 1 := by simpa only [d16070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18376 p hg
    simpa only [d16070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18378 (p : Pattern) (guard : d16071 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16070 p = 1 := by simpa only [d16071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18377 p hg
    simpa only [d16071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18379 (p : Pattern) (guard : d16072 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16071 p = 1 := by simpa only [d16072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18378 p hg
    simpa only [d16072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18380 (p : Pattern) (guard : d542 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare18381 (p : Pattern) (guard : d543 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d542 p = 1 := by simpa only [d543, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18380 p hg
    simpa only [d543, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d543, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d543, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18382 (p : Pattern) (guard : d544 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d543 p = 1 := by simpa only [d544, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18381 p hg
    simpa only [d544, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d544, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d544, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18383 (p : Pattern) (guard : d545 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d545, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d545, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d544 p = 1 := by simpa only [d545, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18382 p hg
    simpa only [d545, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18384 (p : Pattern) (guard : d546 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d545 p = 1 := by simpa only [d546, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18383 p hg
    simpa only [d546, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d546, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d546, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18385 (p : Pattern) (guard : d9457 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare18386 (p : Pattern) (guard : d9458 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9457 p = 1 := by simpa only [d9458, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18385 p hg
    simpa only [d9458, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9458, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d9458, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18387 (p : Pattern) (guard : d9460 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9458 p = 1 := by simpa only [d9460, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18386 p hg
    simpa only [d9460, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9460, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d9460, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18388 (p : Pattern) (guard : d16073 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16073, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d16073, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9460 p = 1 := by simpa only [d16073, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18387 p hg
    simpa only [d16073, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18389 (p : Pattern) (guard : d16074 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16073 p = 1 := by simpa only [d16074, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18388 p hg
    simpa only [d16074, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16074, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d16074, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18390 (p : Pattern) (guard : d16075 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d546 p = 1 := by simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18384 p hg
    simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16074 p = 1 := by simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18389 p hg
    simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18391 (p : Pattern) (guard : d9467 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare18392 (p : Pattern) (guard : d9468 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9467 p = 1 := by simpa only [d9468, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18391 p hg
    simpa only [d9468, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9468, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d9468, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18393 (p : Pattern) (guard : d9470 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9468 p = 1 := by simpa only [d9470, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18392 p hg
    simpa only [d9470, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9470, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d9470, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18394 (p : Pattern) (guard : d12748 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d12748, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d12748, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9470 p = 1 := by simpa only [d12748, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18393 p hg
    simpa only [d12748, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18395 (p : Pattern) (guard : d12749 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d12748 p = 1 := by simpa only [d12749, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18394 p hg
    simpa only [d12749, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d12749, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d12749, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18396 (p : Pattern) (guard : d16076 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d12749 p = 1 := by simpa only [d16076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18395 p hg
    simpa only [d16076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12494 p = 1 := by simpa only [d16076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18165 p hg
    simpa only [d16076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18397 (p : Pattern) (guard : d16077 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16075 p = 1 := by simpa only [d16077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18390 p hg
    simpa only [d16077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16076 p = 1 := by simpa only [d16077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18396 p hg
    simpa only [d16077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18398 (p : Pattern) (guard : d16078 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16077 p = 1 := by simpa only [d16078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18397 p hg
    simpa only [d16078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15966 p = 1 := by simpa only [d16078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18167 p hg
    simpa only [d16078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18399 (p : Pattern) (guard : d16079 p = 1) : d48326 p ≤ (1 : Int) + d173709 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16079, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17873 p hg
    simpa only [d16079, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16078 p = 1 := by simpa only [d16079, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18398 p hg
    simpa only [d16079, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18400 (p : Pattern) (guard : d16080 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16080, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17872 p hg
    simpa only [d16080, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16079 p = 1 := by simpa only [d16080, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18399 p hg
    simpa only [d16080, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18401 (p : Pattern) (guard : d16081 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d12495 p = 1 := by simpa only [d16081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18166 p hg
    simpa only [d16081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d29 p = 1 := by simpa only [d16081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17884 p hg
    simpa only [d16081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18402 (p : Pattern) (guard : d16082 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 157 with
  | false =>
    have hg : d15966 p = 1 := by simpa only [d16082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18167 p hg
    simpa only [d16082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16081 p = 1 := by simpa only [d16082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18401 p hg
    simpa only [d16082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18403 (p : Pattern) (guard : d16083 p = 1) : d48326 p ≤ (1 : Int) + d173709 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16083, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17873 p hg
    simpa only [d16083, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16082 p = 1 := by simpa only [d16083, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18402 p hg
    simpa only [d16083, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18404 (p : Pattern) (guard : d16084 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16084, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17872 p hg
    simpa only [d16084, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16083 p = 1 := by simpa only [d16084, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18403 p hg
    simpa only [d16084, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18405 (p : Pattern) (guard : d16085 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16080 p = 1 := by simpa only [d16085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18400 p hg
    simpa only [d16085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16084 p = 1 := by simpa only [d16085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18404 p hg
    simpa only [d16085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18406 (p : Pattern) (guard : d16086 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16085 p = 1 := by simpa only [d16086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18405 p hg
    simpa only [d16086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15970 p = 1 := by simpa only [d16086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18171 p hg
    simpa only [d16086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18407 (p : Pattern) (guard : d16087 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16086 p = 1 := by simpa only [d16087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18406 p hg
    simpa only [d16087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17889 p hg
    simpa only [d16087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18408 (p : Pattern) (guard : d16088 p = 1) : d48338 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16087 p = 1 := by simpa only [d16088, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18407 p hg
    simpa only [d16088, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16088, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d16088, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18409 (p : Pattern) (guard : d16089 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16089, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17871 p hg
    simpa only [d16089, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16088 p = 1 := by simpa only [d16089, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18408 p hg
    simpa only [d16089, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18410 (p : Pattern) (guard : d16090 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16089 p = 1 := by simpa only [d16090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18409 p hg
    simpa only [d16090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16038 p = 1 := by simpa only [d16090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18309 p hg
    simpa only [d16090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18411 (p : Pattern) (guard : d16091 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16090 p = 1 := by simpa only [d16091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18410 p hg
    simpa only [d16091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18412 (p : Pattern) (guard : d16092 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16091 p = 1 := by simpa only [d16092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18411 p hg
    simpa only [d16092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18413 (p : Pattern) (guard : d16093 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16092 p = 1 := by simpa only [d16093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18412 p hg
    simpa only [d16093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18414 (p : Pattern) (guard : d16094 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16093 p = 1 := by simpa only [d16094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18413 p hg
    simpa only [d16094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16042 p = 1 := by simpa only [d16094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18317 p hg
    simpa only [d16094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18415 (p : Pattern) (guard : d128230 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16094 p = 1 := by simpa only [d128230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18414 p hg
    simpa only [d128230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d128230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18416 (p : Pattern) (guard : d16111 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16038 p = 1 := by simpa only [d16111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18309 p hg
    simpa only [d16111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18417 (p : Pattern) (guard : d16112 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16111 p = 1 := by simpa only [d16112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18416 p hg
    simpa only [d16112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18418 (p : Pattern) (guard : d16113 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16112 p = 1 := by simpa only [d16113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18417 p hg
    simpa only [d16113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18419 (p : Pattern) (guard : d16114 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16113 p = 1 := by simpa only [d16114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18418 p hg
    simpa only [d16114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18420 (p : Pattern) (guard : d16115 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16114 p = 1 := by simpa only [d16115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18419 p hg
    simpa only [d16115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18421 (p : Pattern) (guard : d16116 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16115 p = 1 := by simpa only [d16116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18420 p hg
    simpa only [d16116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18422 (p : Pattern) (guard : d128231 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128230 p = 1 := by simpa only [d128231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18415 p hg
    simpa only [d128231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16116 p = 1 := by simpa only [d128231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18421 p hg
    simpa only [d128231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18423 (p : Pattern) (guard : d128232 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d16072 p = 1 := by simpa only [d128232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18379 p hg
    simpa only [d128232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128231 p = 1 := by simpa only [d128232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18422 p hg
    simpa only [d128232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18424 (p : Pattern) (guard : d128233 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d16066 p = 1 := by simpa only [d128233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18370 p hg
    simpa only [d128233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128232 p = 1 := by simpa only [d128233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18423 p hg
    simpa only [d128233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18425 (p : Pattern) (guard : d128234 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128234, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d128234, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128233 p = 1 := by simpa only [d128234, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18424 p hg
    simpa only [d128234, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18426 (p : Pattern) (guard : d16061 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16040 p = 1 := by simpa only [d16061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18340 p hg
    simpa only [d16061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18427 (p : Pattern) (guard : d16062 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16061 p = 1 := by simpa only [d16062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18426 p hg
    simpa only [d16062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18428 (p : Pattern) (guard : d513 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d489 p = 1 := by simpa only [d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18344 p hg
    simpa only [d513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18429 (p : Pattern) (guard : d514 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d513 p = 1 := by simpa only [d514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18428 p hg
    simpa only [d514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18430 (p : Pattern) (guard : d16063 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16062 p = 1 := by simpa only [d16063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18427 p hg
    simpa only [d16063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d514 p = 1 := by simpa only [d16063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18429 p hg
    simpa only [d16063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18431 (p : Pattern) (guard : d16064 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16063 p = 1 := by simpa only [d16064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18430 p hg
    simpa only [d16064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18432 (p : Pattern) (guard : d16065 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16064 p = 1 := by simpa only [d16065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18431 p hg
    simpa only [d16065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18433 (p : Pattern) (guard : d16066 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16065 p = 1 := by simpa only [d16066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18432 p hg
    simpa only [d16066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18434 (p : Pattern) (guard : d16067 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16039 p = 1 := by simpa only [d16067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18339 p hg
    simpa only [d16067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18435 (p : Pattern) (guard : d16068 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16067 p = 1 := by simpa only [d16068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18434 p hg
    simpa only [d16068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18436 (p : Pattern) (guard : d16069 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16068 p = 1 := by simpa only [d16069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18435 p hg
    simpa only [d16069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18437 (p : Pattern) (guard : d522 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d488 p = 1 := by simpa only [d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18343 p hg
    simpa only [d522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18438 (p : Pattern) (guard : d523 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d522 p = 1 := by simpa only [d523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18437 p hg
    simpa only [d523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18439 (p : Pattern) (guard : d524 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d523 p = 1 := by simpa only [d524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18438 p hg
    simpa only [d524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18440 (p : Pattern) (guard : d16070 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16069 p = 1 := by simpa only [d16070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18436 p hg
    simpa only [d16070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d524 p = 1 := by simpa only [d16070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18439 p hg
    simpa only [d16070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18441 (p : Pattern) (guard : d16071 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16070 p = 1 := by simpa only [d16071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18440 p hg
    simpa only [d16071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18442 (p : Pattern) (guard : d16072 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16071 p = 1 := by simpa only [d16072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18441 p hg
    simpa only [d16072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18443 (p : Pattern) (guard : d16080 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16080, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17907 p hg
    simpa only [d16080, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16079 p = 1 := by simpa only [d16080, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18399 p hg
    simpa only [d16080, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18444 (p : Pattern) (guard : d16084 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16084, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17907 p hg
    simpa only [d16084, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16083 p = 1 := by simpa only [d16084, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18403 p hg
    simpa only [d16084, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18445 (p : Pattern) (guard : d16085 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16080 p = 1 := by simpa only [d16085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18443 p hg
    simpa only [d16085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16084 p = 1 := by simpa only [d16085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18444 p hg
    simpa only [d16085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18446 (p : Pattern) (guard : d16086 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16085 p = 1 := by simpa only [d16086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18445 p hg
    simpa only [d16086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15970 p = 1 := by simpa only [d16086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18205 p hg
    simpa only [d16086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18447 (p : Pattern) (guard : d16087 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16086 p = 1 := by simpa only [d16087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18446 p hg
    simpa only [d16087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17909 p hg
    simpa only [d16087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18448 (p : Pattern) (guard : d16088 p = 1) : d48329 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16087 p = 1 := by simpa only [d16088, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18447 p hg
    simpa only [d16088, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16088, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d16088, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18449 (p : Pattern) (guard : d16089 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16089, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17906 p hg
    simpa only [d16089, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16088 p = 1 := by simpa only [d16089, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18448 p hg
    simpa only [d16089, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18450 (p : Pattern) (guard : d16090 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16089 p = 1 := by simpa only [d16090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18449 p hg
    simpa only [d16090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16038 p = 1 := by simpa only [d16090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18334 p hg
    simpa only [d16090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18451 (p : Pattern) (guard : d16091 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16090 p = 1 := by simpa only [d16091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18450 p hg
    simpa only [d16091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18452 (p : Pattern) (guard : d16092 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16091 p = 1 := by simpa only [d16092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18451 p hg
    simpa only [d16092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18453 (p : Pattern) (guard : d16093 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16092 p = 1 := by simpa only [d16093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18452 p hg
    simpa only [d16093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18454 (p : Pattern) (guard : d16094 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16093 p = 1 := by simpa only [d16094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18453 p hg
    simpa only [d16094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16042 p = 1 := by simpa only [d16094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18342 p hg
    simpa only [d16094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18455 (p : Pattern) (guard : d128230 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16094 p = 1 := by simpa only [d128230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18454 p hg
    simpa only [d128230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d128230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18456 (p : Pattern) (guard : d16111 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16038 p = 1 := by simpa only [d16111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18334 p hg
    simpa only [d16111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18457 (p : Pattern) (guard : d16112 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16111 p = 1 := by simpa only [d16112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18456 p hg
    simpa only [d16112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18458 (p : Pattern) (guard : d16113 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16112 p = 1 := by simpa only [d16113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18457 p hg
    simpa only [d16113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18459 (p : Pattern) (guard : d16114 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16113 p = 1 := by simpa only [d16114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18458 p hg
    simpa only [d16114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18460 (p : Pattern) (guard : d16115 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16114 p = 1 := by simpa only [d16115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18459 p hg
    simpa only [d16115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18461 (p : Pattern) (guard : d16116 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16115 p = 1 := by simpa only [d16116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18460 p hg
    simpa only [d16116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18462 (p : Pattern) (guard : d128231 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128230 p = 1 := by simpa only [d128231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18455 p hg
    simpa only [d128231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16116 p = 1 := by simpa only [d128231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18461 p hg
    simpa only [d128231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18463 (p : Pattern) (guard : d128232 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d16072 p = 1 := by simpa only [d128232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18442 p hg
    simpa only [d128232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128231 p = 1 := by simpa only [d128232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18462 p hg
    simpa only [d128232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18464 (p : Pattern) (guard : d128233 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d16066 p = 1 := by simpa only [d128233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18433 p hg
    simpa only [d128233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128232 p = 1 := by simpa only [d128233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18463 p hg
    simpa only [d128233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18465 (p : Pattern) (guard : d16121 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16061 p = 1 := by simpa only [d16121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18363 p hg
    simpa only [d16121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18466 (p : Pattern) (guard : d610 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d513 p = 1 := by simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18365 p hg
    simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18467 (p : Pattern) (guard : d16122 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16121 p = 1 := by simpa only [d16122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18465 p hg
    simpa only [d16122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d610 p = 1 := by simpa only [d16122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18466 p hg
    simpa only [d16122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18468 (p : Pattern) (guard : d16123 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16122 p = 1 := by simpa only [d16123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18467 p hg
    simpa only [d16123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18469 (p : Pattern) (guard : d16124 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16123 p = 1 := by simpa only [d16124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18468 p hg
    simpa only [d16124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18470 (p : Pattern) (guard : d16125 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16124 p = 1 := by simpa only [d16125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18469 p hg
    simpa only [d16125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18471 (p : Pattern) (guard : d16126 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16068 p = 1 := by simpa only [d16126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18372 p hg
    simpa only [d16126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18472 (p : Pattern) (guard : d616 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d523 p = 1 := by simpa only [d616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18375 p hg
    simpa only [d616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18473 (p : Pattern) (guard : d16127 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16126 p = 1 := by simpa only [d16127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18471 p hg
    simpa only [d16127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d616 p = 1 := by simpa only [d16127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18472 p hg
    simpa only [d16127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18474 (p : Pattern) (guard : d16128 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16127 p = 1 := by simpa only [d16128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18473 p hg
    simpa only [d16128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18475 (p : Pattern) (guard : d16129 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16128 p = 1 := by simpa only [d16129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18474 p hg
    simpa only [d16129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18476 (p : Pattern) (guard : d16130 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16092 p = 1 := by simpa only [d16130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18412 p hg
    simpa only [d16130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18477 (p : Pattern) (guard : d16131 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16130 p = 1 := by simpa only [d16131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18476 p hg
    simpa only [d16131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16051 p = 1 := by simpa only [d16131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18352 p hg
    simpa only [d16131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18478 (p : Pattern) (guard : d128235 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16131 p = 1 := by simpa only [d128235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18477 p hg
    simpa only [d128235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d128235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18479 (p : Pattern) (guard : d16135 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16113 p = 1 := by simpa only [d16135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18418 p hg
    simpa only [d16135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18480 (p : Pattern) (guard : d16136 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16135 p = 1 := by simpa only [d16136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18479 p hg
    simpa only [d16136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18481 (p : Pattern) (guard : d16137 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16136 p = 1 := by simpa only [d16137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18480 p hg
    simpa only [d16137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18482 (p : Pattern) (guard : d128236 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128235 p = 1 := by simpa only [d128236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18478 p hg
    simpa only [d128236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16137 p = 1 := by simpa only [d128236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18481 p hg
    simpa only [d128236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18483 (p : Pattern) (guard : d128237 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d16129 p = 1 := by simpa only [d128237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18475 p hg
    simpa only [d128237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128236 p = 1 := by simpa only [d128237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18482 p hg
    simpa only [d128237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18484 (p : Pattern) (guard : d128238 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d16125 p = 1 := by simpa only [d128238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18470 p hg
    simpa only [d128238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128237 p = 1 := by simpa only [d128238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18483 p hg
    simpa only [d128238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18485 (p : Pattern) (guard : d128239 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d128233 p = 1 := by simpa only [d128239, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18464 p hg
    simpa only [d128239, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128238 p = 1 := by simpa only [d128239, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18484 p hg
    simpa only [d128239, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18486 (p : Pattern) (guard : d128240 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 70 with
  | false =>
    have hg : d128234 p = 1 := by simpa only [d128240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18425 p hg
    simpa only [d128240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128239 p = 1 := by simpa only [d128240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18485 p hg
    simpa only [d128240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18487 (p : Pattern) (guard : d633 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d491 p = 1 := by simpa only [d633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18321 p hg
    simpa only [d633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18488 (p : Pattern) (guard : d634 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d633 p = 1 := by simpa only [d634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18487 p hg
    simpa only [d634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18489 (p : Pattern) (guard : d635 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d634 p = 1 := by simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18488 p hg
    simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18490 (p : Pattern) (guard : d636 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d635 p = 1 := by simpa only [d636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18489 p hg
    simpa only [d636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18491 (p : Pattern) (guard : d637 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d636 p = 1 := by simpa only [d637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18490 p hg
    simpa only [d637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18492 (p : Pattern) (guard : d16143 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d16047 p = 1 := by simpa only [d16143, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18351 p hg
    simpa only [d16143, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d637 p = 1 := by simpa only [d16143, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18491 p hg
    simpa only [d16143, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18493 (p : Pattern) (guard : d633 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d491 p = 1 := by simpa only [d633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18346 p hg
    simpa only [d633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18494 (p : Pattern) (guard : d634 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d633 p = 1 := by simpa only [d634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18493 p hg
    simpa only [d634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18495 (p : Pattern) (guard : d635 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d634 p = 1 := by simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18494 p hg
    simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18496 (p : Pattern) (guard : d636 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d635 p = 1 := by simpa only [d636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18495 p hg
    simpa only [d636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18497 (p : Pattern) (guard : d637 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d636 p = 1 := by simpa only [d637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18496 p hg
    simpa only [d637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18498 (p : Pattern) (guard : d639 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d501 p = 1 := by simpa only [d639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18353 p hg
    simpa only [d639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare18499 (p : Pattern) (guard : d640 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d639 p = 1 := by simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18498 p hg
    simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
