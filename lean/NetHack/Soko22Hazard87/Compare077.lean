import NetHack.Soko22Hazard87.Compare076
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare19250 (p : Pattern) (guard : d14759 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14758 p = 1 := by simpa only [d14759, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19249 p hg
    simpa only [d14759, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14759, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d14759, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19251 (p : Pattern) (guard : d16510 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14837 p = 1 := by simpa only [d16510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19245 p hg
    simpa only [d16510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14759 p = 1 := by simpa only [d16510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19250 p hg
    simpa only [d16510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19252 (p : Pattern) (guard : d16511 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16509 p = 1 := by simpa only [d16511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19240 p hg
    simpa only [d16511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16510 p = 1 := by simpa only [d16511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19251 p hg
    simpa only [d16511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19253 (p : Pattern) (guard : d1099 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare19254 (p : Pattern) (guard : d1100 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1099 p = 1 := by simpa only [d1100, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19253 p hg
    simpa only [d1100, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1100, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d1100, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19255 (p : Pattern) (guard : d1101 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1100 p = 1 := by simpa only [d1101, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19254 p hg
    simpa only [d1101, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1101, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d1101, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19256 (p : Pattern) (guard : d1102 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1102, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d1102, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1101 p = 1 := by simpa only [d1102, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19255 p hg
    simpa only [d1102, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19257 (p : Pattern) (guard : d1103 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1102 p = 1 := by simpa only [d1103, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19256 p hg
    simpa only [d1103, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1103, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d1103, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19258 (p : Pattern) (guard : d9788 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare19259 (p : Pattern) (guard : d9789 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9788 p = 1 := by simpa only [d9789, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19258 p hg
    simpa only [d9789, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9789, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d9789, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19260 (p : Pattern) (guard : d9791 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9789 p = 1 := by simpa only [d9791, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19259 p hg
    simpa only [d9791, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9791, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d9791, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19261 (p : Pattern) (guard : d16438 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16438, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d16438, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9791 p = 1 := by simpa only [d16438, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19260 p hg
    simpa only [d16438, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19262 (p : Pattern) (guard : d16439 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16438 p = 1 := by simpa only [d16439, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19261 p hg
    simpa only [d16439, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16439, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d16439, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19263 (p : Pattern) (guard : d16440 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1103 p = 1 := by simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19257 p hg
    simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16439 p = 1 := by simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19262 p hg
    simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19264 (p : Pattern) (guard : d9799 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare19265 (p : Pattern) (guard : d9800 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9799 p = 1 := by simpa only [d9800, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19264 p hg
    simpa only [d9800, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9800, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d9800, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19266 (p : Pattern) (guard : d9802 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9800 p = 1 := by simpa only [d9802, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19265 p hg
    simpa only [d9802, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9802, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d9802, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19267 (p : Pattern) (guard : d14763 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d14763, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d14763, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9802 p = 1 := by simpa only [d14763, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19266 p hg
    simpa only [d14763, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19268 (p : Pattern) (guard : d14764 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14763 p = 1 := by simpa only [d14764, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19267 p hg
    simpa only [d14764, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14764, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d14764, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19269 (p : Pattern) (guard : d16441 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14759 p = 1 := by simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19250 p hg
    simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14764 p = 1 := by simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19268 p hg
    simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19270 (p : Pattern) (guard : d16442 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16440 p = 1 := by simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19263 p hg
    simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16441 p = 1 := by simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19269 p hg
    simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19271 (p : Pattern) (guard : d16512 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16511 p = 1 := by simpa only [d16512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19252 p hg
    simpa only [d16512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16442 p = 1 := by simpa only [d16512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19270 p hg
    simpa only [d16512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19272 (p : Pattern) (guard : d16513 p = 1) : d48346 p ≤ (1 : Int) + d173722 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16513, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17939 p hg
    simpa only [d16513, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16512 p = 1 := by simpa only [d16513, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19271 p hg
    simpa only [d16513, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19273 (p : Pattern) (guard : d16514 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16514, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17938 p hg
    simpa only [d16514, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16513 p = 1 := by simpa only [d16514, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19272 p hg
    simpa only [d16514, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19274 (p : Pattern) (guard : d9813 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare19275 (p : Pattern) (guard : d9814 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9813 p = 1 := by simpa only [d9814, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19274 p hg
    simpa only [d9814, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9814, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d9814, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19276 (p : Pattern) (guard : d9816 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9814 p = 1 := by simpa only [d9816, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19275 p hg
    simpa only [d9816, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9816, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d9816, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19277 (p : Pattern) (guard : d13022 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d13022, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d13022, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9816 p = 1 := by simpa only [d13022, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19276 p hg
    simpa only [d13022, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19278 (p : Pattern) (guard : d13023 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d13022 p = 1 := by simpa only [d13023, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19277 p hg
    simpa only [d13023, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13023, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d13023, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19279 (p : Pattern) (guard : d16515 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d13023 p = 1 := by simpa only [d16515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19278 p hg
    simpa only [d16515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14764 p = 1 := by simpa only [d16515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19268 p hg
    simpa only [d16515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19280 (p : Pattern) (guard : d14765 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14764 p = 1 := by simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19268 p hg
    simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17949 p hg
    simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19281 (p : Pattern) (guard : d16516 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16515 p = 1 := by simpa only [d16516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19279 p hg
    simpa only [d16516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14765 p = 1 := by simpa only [d16516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19280 p hg
    simpa only [d16516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19282 (p : Pattern) (guard : d16517 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16442 p = 1 := by simpa only [d16517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19270 p hg
    simpa only [d16517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16516 p = 1 := by simpa only [d16517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19281 p hg
    simpa only [d16517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19283 (p : Pattern) (guard : d16518 p = 1) : d48346 p ≤ (1 : Int) + d173722 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16518, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17939 p hg
    simpa only [d16518, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16517 p = 1 := by simpa only [d16518, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19282 p hg
    simpa only [d16518, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19284 (p : Pattern) (guard : d16519 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16519, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17938 p hg
    simpa only [d16519, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16518 p = 1 := by simpa only [d16519, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19283 p hg
    simpa only [d16519, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19285 (p : Pattern) (guard : d16520 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16514 p = 1 := by simpa only [d16520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19273 p hg
    simpa only [d16520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16519 p = 1 := by simpa only [d16520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19284 p hg
    simpa only [d16520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19286 (p : Pattern) (guard : d1109 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare19287 (p : Pattern) (guard : d1110 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1109 p = 1 := by simpa only [d1110, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19286 p hg
    simpa only [d1110, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1110, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d1110, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19288 (p : Pattern) (guard : d1111 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1110 p = 1 := by simpa only [d1111, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19287 p hg
    simpa only [d1111, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1111, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d1111, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19289 (p : Pattern) (guard : d1112 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1112, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d1112, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1111 p = 1 := by simpa only [d1112, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19288 p hg
    simpa only [d1112, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19290 (p : Pattern) (guard : d1113 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1112 p = 1 := by simpa only [d1113, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19289 p hg
    simpa only [d1113, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1113, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d1113, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19291 (p : Pattern) (guard : d1120 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare19292 (p : Pattern) (guard : d1121 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1120 p = 1 := by simpa only [d1121, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19291 p hg
    simpa only [d1121, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1121, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d1121, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19293 (p : Pattern) (guard : d1122 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1121 p = 1 := by simpa only [d1122, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19292 p hg
    simpa only [d1122, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1122, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d1122, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19294 (p : Pattern) (guard : d1123 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1123, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d1123, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1122 p = 1 := by simpa only [d1123, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19293 p hg
    simpa only [d1123, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19295 (p : Pattern) (guard : d1124 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1123 p = 1 := by simpa only [d1124, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19294 p hg
    simpa only [d1124, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1124, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d1124, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19296 (p : Pattern) (guard : d1125 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1113 p = 1 := by simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19290 p hg
    simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1124 p = 1 := by simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19295 p hg
    simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19297 (p : Pattern) (guard : d16443 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1125 p = 1 := by simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19296 p hg
    simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14765 p = 1 := by simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19280 p hg
    simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19298 (p : Pattern) (guard : d16444 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16442 p = 1 := by simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19270 p hg
    simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16443 p = 1 := by simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19297 p hg
    simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19299 (p : Pattern) (guard : d16445 p = 1) : d48346 p ≤ (1 : Int) + d173722 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16445, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17939 p hg
    simpa only [d16445, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16444 p = 1 := by simpa only [d16445, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19298 p hg
    simpa only [d16445, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19300 (p : Pattern) (guard : d16446 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16446, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17938 p hg
    simpa only [d16446, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16445 p = 1 := by simpa only [d16446, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19299 p hg
    simpa only [d16446, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19301 (p : Pattern) (guard : d5017 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare19302 (p : Pattern) (guard : d5018 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5017 p = 1 := by simpa only [d5018, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19301 p hg
    simpa only [d5018, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5018, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d5018, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19303 (p : Pattern) (guard : d5019 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5018 p = 1 := by simpa only [d5019, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19302 p hg
    simpa only [d5019, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5019, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d5019, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19304 (p : Pattern) (guard : d5020 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5020, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d5020, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5019 p = 1 := by simpa only [d5020, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19303 p hg
    simpa only [d5020, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19305 (p : Pattern) (guard : d5021 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5020 p = 1 := by simpa only [d5021, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19304 p hg
    simpa only [d5021, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5021, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d5021, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19306 (p : Pattern) (guard : d5022 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d5021 p = 1 := by simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19305 p hg
    simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17949 p hg
    simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19307 (p : Pattern) (guard : d9843 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare19308 (p : Pattern) (guard : d9844 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9843 p = 1 := by simpa only [d9844, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19307 p hg
    simpa only [d9844, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9844, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d9844, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19309 (p : Pattern) (guard : d9846 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9844 p = 1 := by simpa only [d9846, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19308 p hg
    simpa only [d9846, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9846, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d9846, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19310 (p : Pattern) (guard : d14770 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d14770, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d14770, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9846 p = 1 := by simpa only [d14770, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19309 p hg
    simpa only [d14770, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19311 (p : Pattern) (guard : d14771 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14770 p = 1 := by simpa only [d14771, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19310 p hg
    simpa only [d14771, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14771, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d14771, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19312 (p : Pattern) (guard : d14772 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14771 p = 1 := by simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19311 p hg
    simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17949 p hg
    simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19313 (p : Pattern) (guard : d14773 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d5022 p = 1 := by simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19306 p hg
    simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14772 p = 1 := by simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19312 p hg
    simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19314 (p : Pattern) (guard : d16447 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16443 p = 1 := by simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19297 p hg
    simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14773 p = 1 := by simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19313 p hg
    simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19315 (p : Pattern) (guard : d16448 p = 1) : d48346 p ≤ (1 : Int) + d173722 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16448, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17939 p hg
    simpa only [d16448, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16447 p = 1 := by simpa only [d16448, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19314 p hg
    simpa only [d16448, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19316 (p : Pattern) (guard : d16449 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16449, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17938 p hg
    simpa only [d16449, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16448 p = 1 := by simpa only [d16449, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19315 p hg
    simpa only [d16449, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19317 (p : Pattern) (guard : d16450 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16446 p = 1 := by simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19300 p hg
    simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16449 p = 1 := by simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19316 p hg
    simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19318 (p : Pattern) (guard : d16521 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16520 p = 1 := by simpa only [d16521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19285 p hg
    simpa only [d16521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16450 p = 1 := by simpa only [d16521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19317 p hg
    simpa only [d16521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19319 (p : Pattern) (guard : d16522 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16521 p = 1 := by simpa only [d16522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19318 p hg
    simpa only [d16522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17955 p hg
    simpa only [d16522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19320 (p : Pattern) (guard : d16523 p = 1) : d48356 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16522 p = 1 := by simpa only [d16523, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19319 p hg
    simpa only [d16523, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16523, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17959 p hg
    simpa only [d16523, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19321 (p : Pattern) (guard : d16524 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16524, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17937 p hg
    simpa only [d16524, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16523 p = 1 := by simpa only [d16524, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19320 p hg
    simpa only [d16524, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19322 (p : Pattern) (guard : d16525 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16449 p = 1 := by simpa only [d16525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19316 p hg
    simpa only [d16525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17955 p hg
    simpa only [d16525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19323 (p : Pattern) (guard : d16526 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16450 p = 1 := by simpa only [d16526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19317 p hg
    simpa only [d16526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16525 p = 1 := by simpa only [d16526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19322 p hg
    simpa only [d16526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19324 (p : Pattern) (guard : d16527 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16526 p = 1 := by simpa only [d16527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19323 p hg
    simpa only [d16527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17955 p hg
    simpa only [d16527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19325 (p : Pattern) (guard : d16528 p = 1) : d48356 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16527 p = 1 := by simpa only [d16528, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19324 p hg
    simpa only [d16528, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16528, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17959 p hg
    simpa only [d16528, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19326 (p : Pattern) (guard : d16529 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16529, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17937 p hg
    simpa only [d16529, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16528 p = 1 := by simpa only [d16529, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19325 p hg
    simpa only [d16529, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19327 (p : Pattern) (guard : d16530 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16524 p = 1 := by simpa only [d16530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19321 p hg
    simpa only [d16530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16529 p = 1 := by simpa only [d16530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19326 p hg
    simpa only [d16530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19328 (p : Pattern) (guard : d16531 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16530 p = 1 := by simpa only [d16531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19327 p hg
    simpa only [d16531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19329 (p : Pattern) (guard : d16532 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16531 p = 1 := by simpa only [d16532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19328 p hg
    simpa only [d16532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19330 (p : Pattern) (guard : d16603 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16532 p = 1 := by simpa only [d16603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19329 p hg
    simpa only [d16603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19331 (p : Pattern) (guard : d1127 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1124 p = 1 := by simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19295 p hg
    simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17949 p hg
    simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19332 (p : Pattern) (guard : d14778 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1127 p = 1 := by simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19331 p hg
    simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14772 p = 1 := by simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19312 p hg
    simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19333 (p : Pattern) (guard : d16451 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16443 p = 1 := by simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19297 p hg
    simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14778 p = 1 := by simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19332 p hg
    simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19334 (p : Pattern) (guard : d16452 p = 1) : d48346 p ≤ (1 : Int) + d173722 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16452, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17939 p hg
    simpa only [d16452, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16451 p = 1 := by simpa only [d16452, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19333 p hg
    simpa only [d16452, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19335 (p : Pattern) (guard : d16453 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16453, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17938 p hg
    simpa only [d16453, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16452 p = 1 := by simpa only [d16453, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19334 p hg
    simpa only [d16453, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19336 (p : Pattern) (guard : d16454 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16453 p = 1 := by simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19335 p hg
    simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17955 p hg
    simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19337 (p : Pattern) (guard : d16459 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16454 p = 1 := by simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19336 p hg
    simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17955 p hg
    simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19338 (p : Pattern) (guard : d16460 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16459 p = 1 := by simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19337 p hg
    simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17955 p hg
    simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19339 (p : Pattern) (guard : d16461 p = 1) : d48356 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16460 p = 1 := by simpa only [d16461, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19338 p hg
    simpa only [d16461, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16461, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17959 p hg
    simpa only [d16461, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19340 (p : Pattern) (guard : d16462 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16462, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17937 p hg
    simpa only [d16462, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16461 p = 1 := by simpa only [d16462, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19339 p hg
    simpa only [d16462, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19341 (p : Pattern) (guard : d16534 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16529 p = 1 := by simpa only [d16534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19326 p hg
    simpa only [d16534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16462 p = 1 := by simpa only [d16534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19340 p hg
    simpa only [d16534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19342 (p : Pattern) (guard : d16535 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16534 p = 1 := by simpa only [d16535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19341 p hg
    simpa only [d16535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19343 (p : Pattern) (guard : d16536 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16535 p = 1 := by simpa only [d16536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19342 p hg
    simpa only [d16536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19344 (p : Pattern) (guard : d16604 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16536 p = 1 := by simpa only [d16604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19343 p hg
    simpa only [d16604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19345 (p : Pattern) (guard : d16605 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16603 p = 1 := by simpa only [d16605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19330 p hg
    simpa only [d16605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16604 p = 1 := by simpa only [d16605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19344 p hg
    simpa only [d16605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19346 (p : Pattern) (guard : d128316 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16605 p = 1 := by simpa only [d128316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19345 p hg
    simpa only [d128316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d128316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19347 (p : Pattern) (guard : d12961 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1127 p = 1 := by simpa only [d12961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19331 p hg
    simpa only [d12961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d12961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17949 p hg
    simpa only [d12961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19348 (p : Pattern) (guard : d16574 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16443 p = 1 := by simpa only [d16574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19297 p hg
    simpa only [d16574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12961 p = 1 := by simpa only [d16574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19347 p hg
    simpa only [d16574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19349 (p : Pattern) (guard : d16575 p = 1) : d48346 p ≤ (1 : Int) + d173722 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16575, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17939 p hg
    simpa only [d16575, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16574 p = 1 := by simpa only [d16575, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19348 p hg
    simpa only [d16575, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19350 (p : Pattern) (guard : d16576 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16576, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17938 p hg
    simpa only [d16576, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16575 p = 1 := by simpa only [d16576, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19349 p hg
    simpa only [d16576, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19351 (p : Pattern) (guard : d16577 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16576 p = 1 := by simpa only [d16577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19350 p hg
    simpa only [d16577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17955 p hg
    simpa only [d16577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19352 (p : Pattern) (guard : d16578 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16450 p = 1 := by simpa only [d16578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19317 p hg
    simpa only [d16578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16577 p = 1 := by simpa only [d16578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19351 p hg
    simpa only [d16578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19353 (p : Pattern) (guard : d16579 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16578 p = 1 := by simpa only [d16579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19352 p hg
    simpa only [d16579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17955 p hg
    simpa only [d16579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19354 (p : Pattern) (guard : d16580 p = 1) : d48356 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16579 p = 1 := by simpa only [d16580, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19353 p hg
    simpa only [d16580, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16580, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17959 p hg
    simpa only [d16580, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19355 (p : Pattern) (guard : d16581 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16581, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17937 p hg
    simpa only [d16581, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16580 p = 1 := by simpa only [d16581, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19354 p hg
    simpa only [d16581, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19356 (p : Pattern) (guard : d16582 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16581 p = 1 := by simpa only [d16582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19355 p hg
    simpa only [d16582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19357 (p : Pattern) (guard : d16583 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16582 p = 1 := by simpa only [d16583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19356 p hg
    simpa only [d16583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19358 (p : Pattern) (guard : d16584 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16583 p = 1 := by simpa only [d16584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19357 p hg
    simpa only [d16584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19359 (p : Pattern) (guard : d16610 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16584 p = 1 := by simpa only [d16610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19358 p hg
    simpa only [d16610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19360 (p : Pattern) (guard : d16611 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16610 p = 1 := by simpa only [d16611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19359 p hg
    simpa only [d16611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19361 (p : Pattern) (guard : d16612 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16611 p = 1 := by simpa only [d16612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19360 p hg
    simpa only [d16612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19362 (p : Pattern) (guard : d128317 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128316 p = 1 := by simpa only [d128317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19346 p hg
    simpa only [d128317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16612 p = 1 := by simpa only [d128317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19361 p hg
    simpa only [d128317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19363 (p : Pattern) (guard : d128325 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d128325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128317 p = 1 := by simpa only [d128325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19362 p hg
    simpa only [d128325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19364 (p : Pattern) (guard : d128326 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d128326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128325 p = 1 := by simpa only [d128326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19363 p hg
    simpa only [d128326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19365 (p : Pattern) (guard : d128327 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128327, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d128327, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128326 p = 1 := by simpa only [d128327, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19364 p hg
    simpa only [d128327, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19366 (p : Pattern) (guard : d128328 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17935 p hg
    simpa only [d128328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128327 p = 1 := by simpa only [d128328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19365 p hg
    simpa only [d128328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19367 (p : Pattern) (guard : d16467 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16462 p = 1 := by simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19340 p hg
    simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19368 (p : Pattern) (guard : d16468 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16467 p = 1 := by simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19367 p hg
    simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19369 (p : Pattern) (guard : d16469 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16468 p = 1 := by simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19368 p hg
    simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19370 (p : Pattern) (guard : d16480 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16469 p = 1 := by simpa only [d16480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19369 p hg
    simpa only [d16480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19371 (p : Pattern) (guard : d16629 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16480 p = 1 := by simpa only [d16629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19370 p hg
    simpa only [d16629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19372 (p : Pattern) (guard : d16630 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16629 p = 1 := by simpa only [d16630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19371 p hg
    simpa only [d16630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19373 (p : Pattern) (guard : d16631 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16630 p = 1 := by simpa only [d16631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19372 p hg
    simpa only [d16631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19374 (p : Pattern) (guard : d16632 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16631 p = 1 := by simpa only [d16632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19373 p hg
    simpa only [d16632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19375 (p : Pattern) (guard : d16633 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d16633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16632 p = 1 := by simpa only [d16633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19374 p hg
    simpa only [d16633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19376 (p : Pattern) (guard : d16643 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16643, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16643, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16633 p = 1 := by simpa only [d16643, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19375 p hg
    simpa only [d16643, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19377 (p : Pattern) (guard : d16644 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17935 p hg
    simpa only [d16644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16643 p = 1 := by simpa only [d16644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19376 p hg
    simpa only [d16644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19378 (p : Pattern) (guard : d128329 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 69 with
  | false =>
    have hg : d128328 p = 1 := by simpa only [d128329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19366 p hg
    simpa only [d128329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16644 p = 1 := by simpa only [d128329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19377 p hg
    simpa only [d128329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19379 (p : Pattern) (guard : d128330 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 51 with
  | false =>
    have hg : d128329 p = 1 := by simpa only [d128330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19378 p hg
    simpa only [d128330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17935 p hg
    simpa only [d128330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19380 (p : Pattern) (guard : d128331 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 50 with
  | false =>
    have hg : d128330 p = 1 := by simpa only [d128331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19379 p hg
    simpa only [d128331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17935 p hg
    simpa only [d128331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19381 (p : Pattern) (guard : d128332 p = 1) : d48359 p ≤ (1 : Int) + d173727 p := by
  cases selected : p 49 with
  | false =>
    have hg : d128324 p = 1 := by simpa only [d128332, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19229 p hg
    simpa only [d128332, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128331 p = 1 := by simpa only [d128332, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19380 p hg
    simpa only [d128332, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19382 (p : Pattern) (guard : d175474 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 48 with
  | false =>
    have hg : d128332 p = 1 := by simpa only [d175474, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19381 p hg
    simpa only [d175474, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175474, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17977 p hg
    simpa only [d175474, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19383 (p : Pattern) (guard : d175475 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175474 p = 1 := by simpa only [d175475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19382 p hg
    simpa only [d175475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19384 (p : Pattern) (guard : d175476 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175475 p = 1 := by simpa only [d175476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19383 p hg
    simpa only [d175476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19385 (p : Pattern) (guard : d175477 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175476 p = 1 := by simpa only [d175477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19384 p hg
    simpa only [d175477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19386 (p : Pattern) (guard : d175478 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175477 p = 1 := by simpa only [d175478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19385 p hg
    simpa only [d175478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19387 (p : Pattern) (guard : d175479 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175478 p = 1 := by simpa only [d175479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19386 p hg
    simpa only [d175479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19388 (p : Pattern) (guard : d175480 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175479 p = 1 := by simpa only [d175480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19387 p hg
    simpa only [d175480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19389 (p : Pattern) (guard : d175481 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175480 p = 1 := by simpa only [d175481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19388 p hg
    simpa only [d175481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19390 (p : Pattern) (guard : d175482 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d175482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175481 p = 1 := by simpa only [d175482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19389 p hg
    simpa only [d175482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19391 (p : Pattern) (guard : d175483 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d175473 p = 1 := by simpa only [d175483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18916 p hg
    simpa only [d175483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175482 p = 1 := by simpa only [d175483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19390 p hg
    simpa only [d175483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19392 (p : Pattern) (guard : d1554 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare19393 (p : Pattern) (guard : d1555 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1554 p = 1 := by simpa only [d1555, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19392 p hg
    simpa only [d1555, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1555, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d1555, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19394 (p : Pattern) (guard : d1556 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1555 p = 1 := by simpa only [d1556, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19393 p hg
    simpa only [d1556, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1556, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d1556, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19395 (p : Pattern) (guard : d1557 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1557, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d1557, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1556 p = 1 := by simpa only [d1557, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19394 p hg
    simpa only [d1557, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19396 (p : Pattern) (guard : d1558 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1557 p = 1 := by simpa only [d1558, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19395 p hg
    simpa only [d1558, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1558, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d1558, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19397 (p : Pattern) (guard : d10073 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare19398 (p : Pattern) (guard : d10074 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10073 p = 1 := by simpa only [d10074, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19397 p hg
    simpa only [d10074, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10074, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d10074, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19399 (p : Pattern) (guard : d10076 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10074 p = 1 := by simpa only [d10076, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19398 p hg
    simpa only [d10076, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10076, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d10076, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19400 (p : Pattern) (guard : d16787 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16787, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d16787, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10076 p = 1 := by simpa only [d16787, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19399 p hg
    simpa only [d16787, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19401 (p : Pattern) (guard : d16788 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16787 p = 1 := by simpa only [d16788, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19400 p hg
    simpa only [d16788, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16788, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d16788, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19402 (p : Pattern) (guard : d16789 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1558 p = 1 := by simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19396 p hg
    simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16788 p = 1 := by simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19401 p hg
    simpa only [d16789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19403 (p : Pattern) (guard : d10062 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare19404 (p : Pattern) (guard : d10063 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10062 p = 1 := by simpa only [d10063, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19403 p hg
    simpa only [d10063, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10063, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d10063, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19405 (p : Pattern) (guard : d10065 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10063 p = 1 := by simpa only [d10065, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19404 p hg
    simpa only [d10065, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10065, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d10065, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19406 (p : Pattern) (guard : d15151 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15151, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d15151, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10065 p = 1 := by simpa only [d15151, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19405 p hg
    simpa only [d15151, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19407 (p : Pattern) (guard : d15152 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15151 p = 1 := by simpa only [d15152, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19406 p hg
    simpa only [d15152, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15152, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d15152, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19408 (p : Pattern) (guard : d10084 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare19409 (p : Pattern) (guard : d10085 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10084 p = 1 := by simpa only [d10085, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19408 p hg
    simpa only [d10085, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10085, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d10085, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19410 (p : Pattern) (guard : d10087 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10085 p = 1 := by simpa only [d10087, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19409 p hg
    simpa only [d10087, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10087, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d10087, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19411 (p : Pattern) (guard : d15156 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15156, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d15156, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10087 p = 1 := by simpa only [d15156, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19410 p hg
    simpa only [d15156, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19412 (p : Pattern) (guard : d15157 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15156 p = 1 := by simpa only [d15157, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19411 p hg
    simpa only [d15157, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15157, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d15157, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19413 (p : Pattern) (guard : d16790 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15152 p = 1 := by simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19407 p hg
    simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15157 p = 1 := by simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19412 p hg
    simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19414 (p : Pattern) (guard : d16791 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16789 p = 1 := by simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19402 p hg
    simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16790 p = 1 := by simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19413 p hg
    simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19415 (p : Pattern) (guard : d1569 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare19416 (p : Pattern) (guard : d1570 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1569 p = 1 := by simpa only [d1570, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19415 p hg
    simpa only [d1570, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1570, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d1570, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19417 (p : Pattern) (guard : d1571 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1570 p = 1 := by simpa only [d1571, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19416 p hg
    simpa only [d1571, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1571, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d1571, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19418 (p : Pattern) (guard : d1572 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1572, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d1572, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1571 p = 1 := by simpa only [d1572, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19417 p hg
    simpa only [d1572, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19419 (p : Pattern) (guard : d1573 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1572 p = 1 := by simpa only [d1573, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19418 p hg
    simpa only [d1573, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1573, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d1573, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19420 (p : Pattern) (guard : d10114 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare19421 (p : Pattern) (guard : d10115 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10114 p = 1 := by simpa only [d10115, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19420 p hg
    simpa only [d10115, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10115, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d10115, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19422 (p : Pattern) (guard : d10117 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10115 p = 1 := by simpa only [d10117, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19421 p hg
    simpa only [d10117, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10117, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d10117, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19423 (p : Pattern) (guard : d16792 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16792, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d16792, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10117 p = 1 := by simpa only [d16792, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19422 p hg
    simpa only [d16792, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19424 (p : Pattern) (guard : d16793 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16792 p = 1 := by simpa only [d16793, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19423 p hg
    simpa only [d16793, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16793, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d16793, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19425 (p : Pattern) (guard : d16794 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1573 p = 1 := by simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19419 p hg
    simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16793 p = 1 := by simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19424 p hg
    simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19426 (p : Pattern) (guard : d15158 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15157 p = 1 := by simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19412 p hg
    simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17883 p hg
    simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19427 (p : Pattern) (guard : d16795 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16794 p = 1 := by simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19425 p hg
    simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15158 p = 1 := by simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19426 p hg
    simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19428 (p : Pattern) (guard : d16796 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16791 p = 1 := by simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19414 p hg
    simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16795 p = 1 := by simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19427 p hg
    simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19429 (p : Pattern) (guard : d16797 p = 1) : d48326 p ≤ (1 : Int) + d173709 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16797, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17873 p hg
    simpa only [d16797, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16796 p = 1 := by simpa only [d16797, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19428 p hg
    simpa only [d16797, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19430 (p : Pattern) (guard : d16798 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16798, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17872 p hg
    simpa only [d16798, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16797 p = 1 := by simpa only [d16798, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19429 p hg
    simpa only [d16798, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19431 (p : Pattern) (guard : d5133 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare19432 (p : Pattern) (guard : d5134 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5133 p = 1 := by simpa only [d5134, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19431 p hg
    simpa only [d5134, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5134, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d5134, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19433 (p : Pattern) (guard : d5135 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5134 p = 1 := by simpa only [d5135, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19432 p hg
    simpa only [d5135, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5135, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d5135, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19434 (p : Pattern) (guard : d5136 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5136, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d5136, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5135 p = 1 := by simpa only [d5136, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19433 p hg
    simpa only [d5136, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19435 (p : Pattern) (guard : d5137 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5136 p = 1 := by simpa only [d5137, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19434 p hg
    simpa only [d5137, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5137, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d5137, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19436 (p : Pattern) (guard : d5138 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d5137 p = 1 := by simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19435 p hg
    simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17883 p hg
    simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19437 (p : Pattern) (guard : d10134 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare19438 (p : Pattern) (guard : d10135 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10134 p = 1 := by simpa only [d10135, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19437 p hg
    simpa only [d10135, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10135, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d10135, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19439 (p : Pattern) (guard : d10137 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10135 p = 1 := by simpa only [d10137, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19438 p hg
    simpa only [d10137, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10137, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d10137, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19440 (p : Pattern) (guard : d15163 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15163, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d15163, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10137 p = 1 := by simpa only [d15163, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19439 p hg
    simpa only [d15163, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19441 (p : Pattern) (guard : d15164 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15163 p = 1 := by simpa only [d15164, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19440 p hg
    simpa only [d15164, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15164, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d15164, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19442 (p : Pattern) (guard : d15165 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15164 p = 1 := by simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19441 p hg
    simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17883 p hg
    simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19443 (p : Pattern) (guard : d15166 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d5138 p = 1 := by simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19436 p hg
    simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15165 p = 1 := by simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19442 p hg
    simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19444 (p : Pattern) (guard : d16799 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16795 p = 1 := by simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19427 p hg
    simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15166 p = 1 := by simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19443 p hg
    simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19445 (p : Pattern) (guard : d16800 p = 1) : d48326 p ≤ (1 : Int) + d173709 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16800, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17873 p hg
    simpa only [d16800, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16799 p = 1 := by simpa only [d16800, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19444 p hg
    simpa only [d16800, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19446 (p : Pattern) (guard : d16801 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16801, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17872 p hg
    simpa only [d16801, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16800 p = 1 := by simpa only [d16801, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19445 p hg
    simpa only [d16801, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19447 (p : Pattern) (guard : d16802 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16798 p = 1 := by simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19430 p hg
    simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16801 p = 1 := by simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19446 p hg
    simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19448 (p : Pattern) (guard : d1581 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare19449 (p : Pattern) (guard : d1582 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1581 p = 1 := by simpa only [d1582, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19448 p hg
    simpa only [d1582, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1582, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d1582, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19450 (p : Pattern) (guard : d1583 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1582 p = 1 := by simpa only [d1583, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19449 p hg
    simpa only [d1583, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1583, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d1583, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19451 (p : Pattern) (guard : d1584 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1584, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d1584, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1583 p = 1 := by simpa only [d1584, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19450 p hg
    simpa only [d1584, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19452 (p : Pattern) (guard : d1585 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1584 p = 1 := by simpa only [d1585, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19451 p hg
    simpa only [d1585, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1585, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d1585, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19453 (p : Pattern) (guard : d1588 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1585 p = 1 := by simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19452 p hg
    simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17883 p hg
    simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19454 (p : Pattern) (guard : d15171 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1588 p = 1 := by simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19453 p hg
    simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15165 p = 1 := by simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19442 p hg
    simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19455 (p : Pattern) (guard : d16803 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16795 p = 1 := by simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19427 p hg
    simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15171 p = 1 := by simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19454 p hg
    simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19456 (p : Pattern) (guard : d16804 p = 1) : d48326 p ≤ (1 : Int) + d173709 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16804, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17873 p hg
    simpa only [d16804, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16803 p = 1 := by simpa only [d16804, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19455 p hg
    simpa only [d16804, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19457 (p : Pattern) (guard : d16805 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16805, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17872 p hg
    simpa only [d16805, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16804 p = 1 := by simpa only [d16805, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19456 p hg
    simpa only [d16805, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19458 (p : Pattern) (guard : d16806 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16805 p = 1 := by simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19457 p hg
    simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17889 p hg
    simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19459 (p : Pattern) (guard : d16807 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16802 p = 1 := by simpa only [d16807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19447 p hg
    simpa only [d16807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16806 p = 1 := by simpa only [d16807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19458 p hg
    simpa only [d16807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19460 (p : Pattern) (guard : d16808 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16807 p = 1 := by simpa only [d16808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19459 p hg
    simpa only [d16808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17889 p hg
    simpa only [d16808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19461 (p : Pattern) (guard : d16809 p = 1) : d48338 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16808 p = 1 := by simpa only [d16809, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19460 p hg
    simpa only [d16809, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16809, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d16809, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19462 (p : Pattern) (guard : d16810 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16810, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17871 p hg
    simpa only [d16810, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16809 p = 1 := by simpa only [d16810, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19461 p hg
    simpa only [d16810, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19463 (p : Pattern) (guard : d16811 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16806 p = 1 := by simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19458 p hg
    simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17889 p hg
    simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19464 (p : Pattern) (guard : d16812 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16811 p = 1 := by simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19463 p hg
    simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17889 p hg
    simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19465 (p : Pattern) (guard : d16813 p = 1) : d48338 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16812 p = 1 := by simpa only [d16813, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19464 p hg
    simpa only [d16813, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16813, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d16813, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19466 (p : Pattern) (guard : d16814 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16814, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17871 p hg
    simpa only [d16814, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16813 p = 1 := by simpa only [d16814, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19465 p hg
    simpa only [d16814, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19467 (p : Pattern) (guard : d16815 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16810 p = 1 := by simpa only [d16815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19462 p hg
    simpa only [d16815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16814 p = 1 := by simpa only [d16815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19466 p hg
    simpa only [d16815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19468 (p : Pattern) (guard : d16816 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16815 p = 1 := by simpa only [d16816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19467 p hg
    simpa only [d16816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19469 (p : Pattern) (guard : d16817 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16816 p = 1 := by simpa only [d16817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19468 p hg
    simpa only [d16817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19470 (p : Pattern) (guard : d16818 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16817 p = 1 := by simpa only [d16818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19469 p hg
    simpa only [d16818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19471 (p : Pattern) (guard : d16819 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16814 p = 1 := by simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19466 p hg
    simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19472 (p : Pattern) (guard : d16820 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16819 p = 1 := by simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19471 p hg
    simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19473 (p : Pattern) (guard : d16821 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16820 p = 1 := by simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19472 p hg
    simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19474 (p : Pattern) (guard : d16822 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16821 p = 1 := by simpa only [d16822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19473 p hg
    simpa only [d16822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19475 (p : Pattern) (guard : d16823 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16818 p = 1 := by simpa only [d16823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19470 p hg
    simpa only [d16823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16822 p = 1 := by simpa only [d16823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19474 p hg
    simpa only [d16823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19476 (p : Pattern) (guard : d16824 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16823 p = 1 := by simpa only [d16824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19475 p hg
    simpa only [d16824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19477 (p : Pattern) (guard : d16825 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16824 p = 1 := by simpa only [d16825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19476 p hg
    simpa only [d16825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19478 (p : Pattern) (guard : d16826 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16825 p = 1 := by simpa only [d16826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19477 p hg
    simpa only [d16826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19479 (p : Pattern) (guard : d16827 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d16827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16826 p = 1 := by simpa only [d16827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19478 p hg
    simpa only [d16827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19480 (p : Pattern) (guard : d16828 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16828, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16828, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16827 p = 1 := by simpa only [d16828, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19479 p hg
    simpa only [d16828, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19481 (p : Pattern) (guard : d16829 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17868 p hg
    simpa only [d16829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16828 p = 1 := by simpa only [d16829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19480 p hg
    simpa only [d16829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19482 (p : Pattern) (guard : d16830 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 69 with
  | false =>
    have hg : d16829 p = 1 := by simpa only [d16830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19481 p hg
    simpa only [d16830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17868 p hg
    simpa only [d16830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19483 (p : Pattern) (guard : d16798 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16798, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17907 p hg
    simpa only [d16798, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16797 p = 1 := by simpa only [d16798, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19429 p hg
    simpa only [d16798, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19484 (p : Pattern) (guard : d16801 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16801, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17907 p hg
    simpa only [d16801, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16800 p = 1 := by simpa only [d16801, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19445 p hg
    simpa only [d16801, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19485 (p : Pattern) (guard : d16802 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16798 p = 1 := by simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19483 p hg
    simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16801 p = 1 := by simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19484 p hg
    simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19486 (p : Pattern) (guard : d16805 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16805, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17907 p hg
    simpa only [d16805, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16804 p = 1 := by simpa only [d16805, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19456 p hg
    simpa only [d16805, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19487 (p : Pattern) (guard : d16806 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16805 p = 1 := by simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19486 p hg
    simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17909 p hg
    simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19488 (p : Pattern) (guard : d16807 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16802 p = 1 := by simpa only [d16807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19485 p hg
    simpa only [d16807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16806 p = 1 := by simpa only [d16807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19487 p hg
    simpa only [d16807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19489 (p : Pattern) (guard : d16808 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16807 p = 1 := by simpa only [d16808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19488 p hg
    simpa only [d16808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17909 p hg
    simpa only [d16808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19490 (p : Pattern) (guard : d16809 p = 1) : d48329 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16808 p = 1 := by simpa only [d16809, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19489 p hg
    simpa only [d16809, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16809, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d16809, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19491 (p : Pattern) (guard : d16810 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16810, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17906 p hg
    simpa only [d16810, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16809 p = 1 := by simpa only [d16810, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19490 p hg
    simpa only [d16810, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19492 (p : Pattern) (guard : d16811 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16806 p = 1 := by simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19487 p hg
    simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17909 p hg
    simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19493 (p : Pattern) (guard : d16812 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16811 p = 1 := by simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19492 p hg
    simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17909 p hg
    simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19494 (p : Pattern) (guard : d16813 p = 1) : d48329 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16812 p = 1 := by simpa only [d16813, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19493 p hg
    simpa only [d16813, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16813, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d16813, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19495 (p : Pattern) (guard : d16814 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16814, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17906 p hg
    simpa only [d16814, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16813 p = 1 := by simpa only [d16814, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19494 p hg
    simpa only [d16814, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19496 (p : Pattern) (guard : d16815 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16810 p = 1 := by simpa only [d16815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19491 p hg
    simpa only [d16815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16814 p = 1 := by simpa only [d16815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19495 p hg
    simpa only [d16815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19497 (p : Pattern) (guard : d16816 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16815 p = 1 := by simpa only [d16816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19496 p hg
    simpa only [d16816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19498 (p : Pattern) (guard : d16817 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16816 p = 1 := by simpa only [d16817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19497 p hg
    simpa only [d16817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare19499 (p : Pattern) (guard : d16818 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d16818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16817 p = 1 := by simpa only [d16818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19498 p hg
    simpa only [d16818, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
