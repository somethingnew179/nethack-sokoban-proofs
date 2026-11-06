import NetHack.Soko22Hazard87.Compare100
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare25250 (p : Pattern) (guard : d181353 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181353, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24929 p hg
    simpa only [d181353, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181352 p = 1 := by simpa only [d181353, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25249 p hg
    simpa only [d181353, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25251 (p : Pattern) (guard : d6496 p = 1) : d47652 p ≤ (2 : Int) + d47652 p := by
  omega
theorem compare25252 (p : Pattern) (guard : d19274 p = 1) : d48567 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6496 p = 1 := by simpa only [d19274, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25251 p hg
    simpa only [d19274, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19274, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24932 p hg
    simpa only [d19274, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25253 (p : Pattern) (guard : d181354 p = 1) : d48698 p ≤ (2 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19274 p = 1 := by simpa only [d181354, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25252 p hg
    simpa only [d181354, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181354, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24934 p hg
    simpa only [d181354, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25254 (p : Pattern) (guard : d181355 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181354 p = 1 := by simpa only [d181355, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25253 p hg
    simpa only [d181355, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181355, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24936 p hg
    simpa only [d181355, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25255 (p : Pattern) (guard : d181356 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181355 p = 1 := by simpa only [d181356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25254 p hg
    simpa only [d181356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24938 p hg
    simpa only [d181356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25256 (p : Pattern) (guard : d15412 p = 1) : d47652 p ≤ (2 : Int) + d47652 p := by
  omega
theorem compare25257 (p : Pattern) (guard : d19278 p = 1) : d48567 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d15412 p = 1 := by simpa only [d19278, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25256 p hg
    simpa only [d19278, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19278, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24932 p hg
    simpa only [d19278, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25258 (p : Pattern) (guard : d181357 p = 1) : d48698 p ≤ (2 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19278 p = 1 := by simpa only [d181357, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25257 p hg
    simpa only [d181357, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181357, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24934 p hg
    simpa only [d181357, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25259 (p : Pattern) (guard : d181358 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181357 p = 1 := by simpa only [d181358, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25258 p hg
    simpa only [d181358, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181358, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24936 p hg
    simpa only [d181358, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25260 (p : Pattern) (guard : d181359 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181358 p = 1 := by simpa only [d181359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25259 p hg
    simpa only [d181359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24938 p hg
    simpa only [d181359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25261 (p : Pattern) (guard : d181360 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d181356 p = 1 := by simpa only [d181360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25255 p hg
    simpa only [d181360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181359 p = 1 := by simpa only [d181360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25260 p hg
    simpa only [d181360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25262 (p : Pattern) (guard : d181361 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 157 with
  | false =>
    have hg : d181350 p = 1 := by simpa only [d181361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25247 p hg
    simpa only [d181361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181360 p = 1 := by simpa only [d181361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25261 p hg
    simpa only [d181361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25263 (p : Pattern) (guard : d181362 p = 1) : d48702 p ≤ (2 : Int) + d130449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181362, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24930 p hg
    simpa only [d181362, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181361 p = 1 := by simpa only [d181362, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25262 p hg
    simpa only [d181362, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25264 (p : Pattern) (guard : d181363 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181363, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24929 p hg
    simpa only [d181363, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181362 p = 1 := by simpa only [d181363, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25263 p hg
    simpa only [d181363, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25265 (p : Pattern) (guard : d181364 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 136 with
  | false =>
    have hg : d181353 p = 1 := by simpa only [d181364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25250 p hg
    simpa only [d181364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181363 p = 1 := by simpa only [d181364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25264 p hg
    simpa only [d181364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25266 (p : Pattern) (guard : d1868 p = 1) : d47652 p ≤ (2 : Int) + d47652 p := by
  omega
theorem compare25267 (p : Pattern) (guard : d19313 p = 1) : d48567 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1868 p = 1 := by simpa only [d19313, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25266 p hg
    simpa only [d19313, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19313, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24932 p hg
    simpa only [d19313, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25268 (p : Pattern) (guard : d181378 p = 1) : d48698 p ≤ (2 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19313 p = 1 := by simpa only [d181378, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25267 p hg
    simpa only [d181378, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181378, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24934 p hg
    simpa only [d181378, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25269 (p : Pattern) (guard : d181379 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181378 p = 1 := by simpa only [d181379, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25268 p hg
    simpa only [d181379, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181379, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24936 p hg
    simpa only [d181379, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25270 (p : Pattern) (guard : d181380 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181379 p = 1 := by simpa only [d181380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25269 p hg
    simpa only [d181380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24938 p hg
    simpa only [d181380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25271 (p : Pattern) (guard : d181381 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d181380 p = 1 := by simpa only [d181381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25270 p hg
    simpa only [d181381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181359 p = 1 := by simpa only [d181381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25260 p hg
    simpa only [d181381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25272 (p : Pattern) (guard : d181382 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 157 with
  | false =>
    have hg : d181350 p = 1 := by simpa only [d181382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25247 p hg
    simpa only [d181382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181381 p = 1 := by simpa only [d181382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25271 p hg
    simpa only [d181382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25273 (p : Pattern) (guard : d181383 p = 1) : d48702 p ≤ (2 : Int) + d130449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181383, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24930 p hg
    simpa only [d181383, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181382 p = 1 := by simpa only [d181383, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25272 p hg
    simpa only [d181383, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25274 (p : Pattern) (guard : d181384 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181384, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24929 p hg
    simpa only [d181384, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181383 p = 1 := by simpa only [d181384, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25273 p hg
    simpa only [d181384, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25275 (p : Pattern) (guard : d181385 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 136 with
  | false =>
    have hg : d181384 p = 1 := by simpa only [d181385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25274 p hg
    simpa only [d181385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24944 p hg
    simpa only [d181385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25276 (p : Pattern) (guard : d181705 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 135 with
  | false =>
    have hg : d181364 p = 1 := by simpa only [d181705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25265 p hg
    simpa only [d181705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181385 p = 1 := by simpa only [d181705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25275 p hg
    simpa only [d181705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25277 (p : Pattern) (guard : d181706 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 119 with
  | false =>
    have hg : d181705 p = 1 := by simpa only [d181706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25276 p hg
    simpa only [d181706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24944 p hg
    simpa only [d181706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25278 (p : Pattern) (guard : d181707 p = 1) : d48705 p ≤ (2 : Int) + d130452 p := by
  cases selected : p 116 with
  | false =>
    have hg : d181706 p = 1 := by simpa only [d181707, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25277 p hg
    simpa only [d181707, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181707, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24948 p hg
    simpa only [d181707, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25279 (p : Pattern) (guard : d181708 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181708, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24928 p hg
    simpa only [d181708, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181707 p = 1 := by simpa only [d181708, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25278 p hg
    simpa only [d181708, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25280 (p : Pattern) (guard : d181386 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 135 with
  | false =>
    have hg : d181385 p = 1 := by simpa only [d181386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25275 p hg
    simpa only [d181386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24944 p hg
    simpa only [d181386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25281 (p : Pattern) (guard : d181387 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 119 with
  | false =>
    have hg : d181386 p = 1 := by simpa only [d181387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25280 p hg
    simpa only [d181387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24944 p hg
    simpa only [d181387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25282 (p : Pattern) (guard : d181388 p = 1) : d48705 p ≤ (2 : Int) + d130452 p := by
  cases selected : p 116 with
  | false =>
    have hg : d181387 p = 1 := by simpa only [d181388, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25281 p hg
    simpa only [d181388, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181388, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24948 p hg
    simpa only [d181388, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25283 (p : Pattern) (guard : d181389 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181389, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24928 p hg
    simpa only [d181389, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181388 p = 1 := by simpa only [d181389, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25282 p hg
    simpa only [d181389, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25284 (p : Pattern) (guard : d181709 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 113 with
  | false =>
    have hg : d181708 p = 1 := by simpa only [d181709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25279 p hg
    simpa only [d181709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181389 p = 1 := by simpa only [d181709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25283 p hg
    simpa only [d181709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25285 (p : Pattern) (guard : d181710 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 96 with
  | false =>
    have hg : d181709 p = 1 := by simpa only [d181710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25284 p hg
    simpa only [d181710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25286 (p : Pattern) (guard : d181711 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 95 with
  | false =>
    have hg : d181710 p = 1 := by simpa only [d181711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25285 p hg
    simpa only [d181711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25287 (p : Pattern) (guard : d181712 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 93 with
  | false =>
    have hg : d181711 p = 1 := by simpa only [d181712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25286 p hg
    simpa only [d181712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25288 (p : Pattern) (guard : d181416 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 113 with
  | false =>
    have hg : d181389 p = 1 := by simpa only [d181416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25283 p hg
    simpa only [d181416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25289 (p : Pattern) (guard : d181417 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 96 with
  | false =>
    have hg : d181416 p = 1 := by simpa only [d181417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25288 p hg
    simpa only [d181417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25290 (p : Pattern) (guard : d181418 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 95 with
  | false =>
    have hg : d181417 p = 1 := by simpa only [d181418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25289 p hg
    simpa only [d181418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25291 (p : Pattern) (guard : d181419 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 93 with
  | false =>
    have hg : d181418 p = 1 := by simpa only [d181419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25290 p hg
    simpa only [d181419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25292 (p : Pattern) (guard : d181713 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 91 with
  | false =>
    have hg : d181712 p = 1 := by simpa only [d181713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25287 p hg
    simpa only [d181713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181419 p = 1 := by simpa only [d181713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25291 p hg
    simpa only [d181713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25293 (p : Pattern) (guard : d181714 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181713 p = 1 := by simpa only [d181714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25292 p hg
    simpa only [d181714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25294 (p : Pattern) (guard : d181715 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 89 with
  | false =>
    have hg : d181714 p = 1 := by simpa only [d181715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25293 p hg
    simpa only [d181715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25295 (p : Pattern) (guard : d181716 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181715 p = 1 := by simpa only [d181716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25294 p hg
    simpa only [d181716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25296 (p : Pattern) (guard : d181717 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181716 p = 1 := by simpa only [d181717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25295 p hg
    simpa only [d181717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25297 (p : Pattern) (guard : d181718 p = 1) : d48707 p ≤ (2 : Int) + d130454 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181718, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24926 p hg
    simpa only [d181718, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181717 p = 1 := by simpa only [d181718, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25296 p hg
    simpa only [d181718, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25298 (p : Pattern) (guard : d181719 p = 1) : d48707 p ≤ (2 : Int) + d130454 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24925 p hg
    simpa only [d181719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181718 p = 1 := by simpa only [d181719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25297 p hg
    simpa only [d181719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25299 (p : Pattern) (guard : d181720 p = 1) : d48707 p ≤ (2 : Int) + d130454 p := by
  cases selected : p 69 with
  | false =>
    have hg : d181719 p = 1 := by simpa only [d181720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25298 p hg
    simpa only [d181720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24925 p hg
    simpa only [d181720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25300 (p : Pattern) (guard : d181721 p = 1) : d48707 p ≤ (2 : Int) + d130454 p := by
  cases selected : p 51 with
  | false =>
    have hg : d181720 p = 1 := by simpa only [d181721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25299 p hg
    simpa only [d181721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24925 p hg
    simpa only [d181721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25301 (p : Pattern) (guard : d181722 p = 1) : d48707 p ≤ (2 : Int) + d130454 p := by
  cases selected : p 50 with
  | false =>
    have hg : d181721 p = 1 := by simpa only [d181722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25300 p hg
    simpa only [d181722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24925 p hg
    simpa only [d181722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25302 (p : Pattern) (guard : d181723 p = 1) : d48748 p ≤ (2 : Int) + d130478 p := by
  cases selected : p 49 with
  | false =>
    have hg : d181722 p = 1 := by simpa only [d181723, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25301 p hg
    simpa only [d181723, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181723, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24965 p hg
    simpa only [d181723, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25303 (p : Pattern) (guard : d181724 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181724, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24924 p hg
    simpa only [d181724, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181723 p = 1 := by simpa only [d181724, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25302 p hg
    simpa only [d181724, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25304 (p : Pattern) (guard : d181725 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181724 p = 1 := by simpa only [d181725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25303 p hg
    simpa only [d181725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25305 (p : Pattern) (guard : d181726 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181725 p = 1 := by simpa only [d181726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25304 p hg
    simpa only [d181726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25306 (p : Pattern) (guard : d181727 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181726 p = 1 := by simpa only [d181727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25305 p hg
    simpa only [d181727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25307 (p : Pattern) (guard : d181728 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181727 p = 1 := by simpa only [d181728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25306 p hg
    simpa only [d181728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25308 (p : Pattern) (guard : d181729 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181728 p = 1 := by simpa only [d181729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25307 p hg
    simpa only [d181729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25309 (p : Pattern) (guard : d181730 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181729 p = 1 := by simpa only [d181730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25308 p hg
    simpa only [d181730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25310 (p : Pattern) (guard : d181731 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181730 p = 1 := by simpa only [d181731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25309 p hg
    simpa only [d181731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25311 (p : Pattern) (guard : d181732 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181731 p = 1 := by simpa only [d181732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25310 p hg
    simpa only [d181732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25312 (p : Pattern) (guard : d181733 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181732 p = 1 := by simpa only [d181733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25311 p hg
    simpa only [d181733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25313 (p : Pattern) (guard : d181734 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d181704 p = 1 := by simpa only [d181734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25217 p hg
    simpa only [d181734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181733 p = 1 := by simpa only [d181734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25312 p hg
    simpa only [d181734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25314 (p : Pattern) (guard : d2335 p = 1) : d47652 p ≤ (2 : Int) + d47652 p := by
  omega
theorem compare25315 (p : Pattern) (guard : d19474 p = 1) : d48567 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2335 p = 1 := by simpa only [d19474, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25314 p hg
    simpa only [d19474, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19474, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24932 p hg
    simpa only [d19474, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25316 (p : Pattern) (guard : d181451 p = 1) : d48698 p ≤ (2 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19474 p = 1 := by simpa only [d181451, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25315 p hg
    simpa only [d181451, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181451, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24934 p hg
    simpa only [d181451, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25317 (p : Pattern) (guard : d181452 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181451 p = 1 := by simpa only [d181452, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25316 p hg
    simpa only [d181452, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181452, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24936 p hg
    simpa only [d181452, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25318 (p : Pattern) (guard : d17376 p = 1) : d47652 p ≤ (2 : Int) + d47652 p := by
  omega
theorem compare25319 (p : Pattern) (guard : d19477 p = 1) : d48567 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d17376 p = 1 := by simpa only [d19477, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25318 p hg
    simpa only [d19477, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19477, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24932 p hg
    simpa only [d19477, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25320 (p : Pattern) (guard : d181453 p = 1) : d48698 p ≤ (2 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19477 p = 1 := by simpa only [d181453, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25319 p hg
    simpa only [d181453, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181453, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24934 p hg
    simpa only [d181453, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25321 (p : Pattern) (guard : d181454 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181453 p = 1 := by simpa only [d181454, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25320 p hg
    simpa only [d181454, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181454, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24936 p hg
    simpa only [d181454, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25322 (p : Pattern) (guard : d181455 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181452 p = 1 := by simpa only [d181455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25317 p hg
    simpa only [d181455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181454 p = 1 := by simpa only [d181455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25321 p hg
    simpa only [d181455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25323 (p : Pattern) (guard : d13813 p = 1) : d47652 p ≤ (2 : Int) + d47652 p := by
  omega
theorem compare25324 (p : Pattern) (guard : d19469 p = 1) : d48567 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d13813 p = 1 := by simpa only [d19469, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25323 p hg
    simpa only [d19469, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19469, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24932 p hg
    simpa only [d19469, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25325 (p : Pattern) (guard : d181447 p = 1) : d48698 p ≤ (2 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19469 p = 1 := by simpa only [d181447, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25324 p hg
    simpa only [d181447, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181447, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24934 p hg
    simpa only [d181447, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25326 (p : Pattern) (guard : d181448 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181447 p = 1 := by simpa only [d181448, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25325 p hg
    simpa only [d181448, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181448, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24936 p hg
    simpa only [d181448, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25327 (p : Pattern) (guard : d15775 p = 1) : d47652 p ≤ (2 : Int) + d47652 p := by
  omega
theorem compare25328 (p : Pattern) (guard : d19481 p = 1) : d48567 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d15775 p = 1 := by simpa only [d19481, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25327 p hg
    simpa only [d19481, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19481, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24932 p hg
    simpa only [d19481, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25329 (p : Pattern) (guard : d181456 p = 1) : d48698 p ≤ (2 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19481 p = 1 := by simpa only [d181456, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25328 p hg
    simpa only [d181456, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181456, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24934 p hg
    simpa only [d181456, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25330 (p : Pattern) (guard : d181457 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181456 p = 1 := by simpa only [d181457, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25329 p hg
    simpa only [d181457, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181457, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24936 p hg
    simpa only [d181457, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25331 (p : Pattern) (guard : d181458 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181448 p = 1 := by simpa only [d181458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25326 p hg
    simpa only [d181458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181457 p = 1 := by simpa only [d181458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25330 p hg
    simpa only [d181458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25332 (p : Pattern) (guard : d181459 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d181455 p = 1 := by simpa only [d181459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25322 p hg
    simpa only [d181459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181458 p = 1 := by simpa only [d181459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25331 p hg
    simpa only [d181459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25333 (p : Pattern) (guard : d2340 p = 1) : d47652 p ≤ (2 : Int) + d47652 p := by
  omega
theorem compare25334 (p : Pattern) (guard : d19495 p = 1) : d48567 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2340 p = 1 := by simpa only [d19495, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25333 p hg
    simpa only [d19495, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19495, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24932 p hg
    simpa only [d19495, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25335 (p : Pattern) (guard : d181469 p = 1) : d48698 p ≤ (2 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19495 p = 1 := by simpa only [d181469, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25334 p hg
    simpa only [d181469, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181469, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24934 p hg
    simpa only [d181469, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25336 (p : Pattern) (guard : d181470 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181469 p = 1 := by simpa only [d181470, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25335 p hg
    simpa only [d181470, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181470, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24936 p hg
    simpa only [d181470, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25337 (p : Pattern) (guard : d17391 p = 1) : d47652 p ≤ (2 : Int) + d47652 p := by
  omega
theorem compare25338 (p : Pattern) (guard : d19498 p = 1) : d48567 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d17391 p = 1 := by simpa only [d19498, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25337 p hg
    simpa only [d19498, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19498, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24932 p hg
    simpa only [d19498, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25339 (p : Pattern) (guard : d181471 p = 1) : d48698 p ≤ (2 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19498 p = 1 := by simpa only [d181471, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25338 p hg
    simpa only [d181471, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181471, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24934 p hg
    simpa only [d181471, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25340 (p : Pattern) (guard : d181472 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181471 p = 1 := by simpa only [d181472, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25339 p hg
    simpa only [d181472, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181472, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24936 p hg
    simpa only [d181472, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25341 (p : Pattern) (guard : d181473 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181470 p = 1 := by simpa only [d181473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25336 p hg
    simpa only [d181473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181472 p = 1 := by simpa only [d181473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25340 p hg
    simpa only [d181473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25342 (p : Pattern) (guard : d181463 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181457 p = 1 := by simpa only [d181463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25330 p hg
    simpa only [d181463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24938 p hg
    simpa only [d181463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25343 (p : Pattern) (guard : d181474 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d181473 p = 1 := by simpa only [d181474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25341 p hg
    simpa only [d181474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181463 p = 1 := by simpa only [d181474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25342 p hg
    simpa only [d181474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25344 (p : Pattern) (guard : d181475 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 157 with
  | false =>
    have hg : d181459 p = 1 := by simpa only [d181475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25332 p hg
    simpa only [d181475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181474 p = 1 := by simpa only [d181475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25343 p hg
    simpa only [d181475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25345 (p : Pattern) (guard : d181476 p = 1) : d48702 p ≤ (2 : Int) + d130449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181476, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24930 p hg
    simpa only [d181476, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181475 p = 1 := by simpa only [d181476, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25344 p hg
    simpa only [d181476, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25346 (p : Pattern) (guard : d181477 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181477, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24929 p hg
    simpa only [d181477, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181476 p = 1 := by simpa only [d181477, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25345 p hg
    simpa only [d181477, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25347 (p : Pattern) (guard : d6643 p = 1) : d47652 p ≤ (2 : Int) + d47652 p := by
  omega
theorem compare25348 (p : Pattern) (guard : d19506 p = 1) : d48567 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6643 p = 1 := by simpa only [d19506, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25347 p hg
    simpa only [d19506, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19506, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24932 p hg
    simpa only [d19506, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25349 (p : Pattern) (guard : d181478 p = 1) : d48698 p ≤ (2 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19506 p = 1 := by simpa only [d181478, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25348 p hg
    simpa only [d181478, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181478, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24934 p hg
    simpa only [d181478, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25350 (p : Pattern) (guard : d181479 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181478 p = 1 := by simpa only [d181479, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25349 p hg
    simpa only [d181479, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181479, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24936 p hg
    simpa only [d181479, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25351 (p : Pattern) (guard : d181480 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181479 p = 1 := by simpa only [d181480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25350 p hg
    simpa only [d181480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24938 p hg
    simpa only [d181480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25352 (p : Pattern) (guard : d15790 p = 1) : d47652 p ≤ (2 : Int) + d47652 p := by
  omega
theorem compare25353 (p : Pattern) (guard : d19510 p = 1) : d48567 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d15790 p = 1 := by simpa only [d19510, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25352 p hg
    simpa only [d19510, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19510, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24932 p hg
    simpa only [d19510, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25354 (p : Pattern) (guard : d181481 p = 1) : d48698 p ≤ (2 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19510 p = 1 := by simpa only [d181481, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25353 p hg
    simpa only [d181481, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181481, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24934 p hg
    simpa only [d181481, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25355 (p : Pattern) (guard : d181482 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181481 p = 1 := by simpa only [d181482, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25354 p hg
    simpa only [d181482, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181482, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24936 p hg
    simpa only [d181482, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25356 (p : Pattern) (guard : d181483 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181482 p = 1 := by simpa only [d181483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25355 p hg
    simpa only [d181483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24938 p hg
    simpa only [d181483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25357 (p : Pattern) (guard : d181484 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d181480 p = 1 := by simpa only [d181484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25351 p hg
    simpa only [d181484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181483 p = 1 := by simpa only [d181484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25356 p hg
    simpa only [d181484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25358 (p : Pattern) (guard : d181485 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 157 with
  | false =>
    have hg : d181474 p = 1 := by simpa only [d181485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25343 p hg
    simpa only [d181485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181484 p = 1 := by simpa only [d181485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25357 p hg
    simpa only [d181485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25359 (p : Pattern) (guard : d181486 p = 1) : d48702 p ≤ (2 : Int) + d130449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181486, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24930 p hg
    simpa only [d181486, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181485 p = 1 := by simpa only [d181486, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25358 p hg
    simpa only [d181486, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25360 (p : Pattern) (guard : d181487 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181487, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24929 p hg
    simpa only [d181487, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181486 p = 1 := by simpa only [d181487, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25359 p hg
    simpa only [d181487, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25361 (p : Pattern) (guard : d181488 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 136 with
  | false =>
    have hg : d181477 p = 1 := by simpa only [d181488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25346 p hg
    simpa only [d181488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181487 p = 1 := by simpa only [d181488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25360 p hg
    simpa only [d181488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25362 (p : Pattern) (guard : d2346 p = 1) : d47652 p ≤ (2 : Int) + d47652 p := by
  omega
theorem compare25363 (p : Pattern) (guard : d19545 p = 1) : d48567 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2346 p = 1 := by simpa only [d19545, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25362 p hg
    simpa only [d19545, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19545, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24932 p hg
    simpa only [d19545, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25364 (p : Pattern) (guard : d181502 p = 1) : d48698 p ≤ (2 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19545 p = 1 := by simpa only [d181502, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25363 p hg
    simpa only [d181502, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181502, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24934 p hg
    simpa only [d181502, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25365 (p : Pattern) (guard : d181503 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181502 p = 1 := by simpa only [d181503, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25364 p hg
    simpa only [d181503, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181503, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24936 p hg
    simpa only [d181503, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25366 (p : Pattern) (guard : d181504 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181503 p = 1 := by simpa only [d181504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25365 p hg
    simpa only [d181504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24938 p hg
    simpa only [d181504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25367 (p : Pattern) (guard : d181505 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d181504 p = 1 := by simpa only [d181505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25366 p hg
    simpa only [d181505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181483 p = 1 := by simpa only [d181505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25356 p hg
    simpa only [d181505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25368 (p : Pattern) (guard : d181506 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 157 with
  | false =>
    have hg : d181474 p = 1 := by simpa only [d181506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25343 p hg
    simpa only [d181506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181505 p = 1 := by simpa only [d181506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25367 p hg
    simpa only [d181506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25369 (p : Pattern) (guard : d181507 p = 1) : d48702 p ≤ (2 : Int) + d130449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181507, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24930 p hg
    simpa only [d181507, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181506 p = 1 := by simpa only [d181507, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25368 p hg
    simpa only [d181507, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25370 (p : Pattern) (guard : d181508 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181508, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24929 p hg
    simpa only [d181508, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181507 p = 1 := by simpa only [d181508, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25369 p hg
    simpa only [d181508, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25371 (p : Pattern) (guard : d181509 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 136 with
  | false =>
    have hg : d181508 p = 1 := by simpa only [d181509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25370 p hg
    simpa only [d181509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24944 p hg
    simpa only [d181509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25372 (p : Pattern) (guard : d181735 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 135 with
  | false =>
    have hg : d181488 p = 1 := by simpa only [d181735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25361 p hg
    simpa only [d181735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181509 p = 1 := by simpa only [d181735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25371 p hg
    simpa only [d181735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25373 (p : Pattern) (guard : d181736 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 119 with
  | false =>
    have hg : d181735 p = 1 := by simpa only [d181736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25372 p hg
    simpa only [d181736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24944 p hg
    simpa only [d181736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25374 (p : Pattern) (guard : d181737 p = 1) : d48705 p ≤ (2 : Int) + d130452 p := by
  cases selected : p 116 with
  | false =>
    have hg : d181736 p = 1 := by simpa only [d181737, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25373 p hg
    simpa only [d181737, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181737, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24948 p hg
    simpa only [d181737, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25375 (p : Pattern) (guard : d181738 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181738, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24928 p hg
    simpa only [d181738, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181737 p = 1 := by simpa only [d181738, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25374 p hg
    simpa only [d181738, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25376 (p : Pattern) (guard : d181510 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 135 with
  | false =>
    have hg : d181509 p = 1 := by simpa only [d181510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25371 p hg
    simpa only [d181510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24944 p hg
    simpa only [d181510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25377 (p : Pattern) (guard : d181511 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 119 with
  | false =>
    have hg : d181510 p = 1 := by simpa only [d181511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25376 p hg
    simpa only [d181511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24944 p hg
    simpa only [d181511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25378 (p : Pattern) (guard : d181512 p = 1) : d48705 p ≤ (2 : Int) + d130452 p := by
  cases selected : p 116 with
  | false =>
    have hg : d181511 p = 1 := by simpa only [d181512, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25377 p hg
    simpa only [d181512, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181512, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24948 p hg
    simpa only [d181512, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25379 (p : Pattern) (guard : d181513 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181513, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24928 p hg
    simpa only [d181513, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181512 p = 1 := by simpa only [d181513, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25378 p hg
    simpa only [d181513, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25380 (p : Pattern) (guard : d181739 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 113 with
  | false =>
    have hg : d181738 p = 1 := by simpa only [d181739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25375 p hg
    simpa only [d181739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181513 p = 1 := by simpa only [d181739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25379 p hg
    simpa only [d181739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25381 (p : Pattern) (guard : d181740 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 96 with
  | false =>
    have hg : d181739 p = 1 := by simpa only [d181740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25380 p hg
    simpa only [d181740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25382 (p : Pattern) (guard : d181741 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 95 with
  | false =>
    have hg : d181740 p = 1 := by simpa only [d181741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25381 p hg
    simpa only [d181741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25383 (p : Pattern) (guard : d181742 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 93 with
  | false =>
    have hg : d181741 p = 1 := by simpa only [d181742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25382 p hg
    simpa only [d181742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25384 (p : Pattern) (guard : d181540 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 113 with
  | false =>
    have hg : d181513 p = 1 := by simpa only [d181540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25379 p hg
    simpa only [d181540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25385 (p : Pattern) (guard : d181541 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 96 with
  | false =>
    have hg : d181540 p = 1 := by simpa only [d181541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25384 p hg
    simpa only [d181541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25386 (p : Pattern) (guard : d181542 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 95 with
  | false =>
    have hg : d181541 p = 1 := by simpa only [d181542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25385 p hg
    simpa only [d181542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25387 (p : Pattern) (guard : d181543 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 93 with
  | false =>
    have hg : d181542 p = 1 := by simpa only [d181543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25386 p hg
    simpa only [d181543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25388 (p : Pattern) (guard : d181743 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 91 with
  | false =>
    have hg : d181742 p = 1 := by simpa only [d181743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25383 p hg
    simpa only [d181743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181543 p = 1 := by simpa only [d181743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25387 p hg
    simpa only [d181743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25389 (p : Pattern) (guard : d181744 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181743 p = 1 := by simpa only [d181744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25388 p hg
    simpa only [d181744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25390 (p : Pattern) (guard : d181745 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 89 with
  | false =>
    have hg : d181744 p = 1 := by simpa only [d181745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25389 p hg
    simpa only [d181745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25391 (p : Pattern) (guard : d181746 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181745 p = 1 := by simpa only [d181746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25390 p hg
    simpa only [d181746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25392 (p : Pattern) (guard : d181747 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181746 p = 1 := by simpa only [d181747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25391 p hg
    simpa only [d181747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25393 (p : Pattern) (guard : d181748 p = 1) : d48707 p ≤ (2 : Int) + d130454 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181748, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24926 p hg
    simpa only [d181748, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181747 p = 1 := by simpa only [d181748, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25392 p hg
    simpa only [d181748, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25394 (p : Pattern) (guard : d181749 p = 1) : d48707 p ≤ (2 : Int) + d130454 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24925 p hg
    simpa only [d181749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181748 p = 1 := by simpa only [d181749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25393 p hg
    simpa only [d181749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25395 (p : Pattern) (guard : d181750 p = 1) : d48707 p ≤ (2 : Int) + d130454 p := by
  cases selected : p 69 with
  | false =>
    have hg : d181749 p = 1 := by simpa only [d181750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25394 p hg
    simpa only [d181750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24925 p hg
    simpa only [d181750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25396 (p : Pattern) (guard : d181751 p = 1) : d48707 p ≤ (2 : Int) + d130454 p := by
  cases selected : p 51 with
  | false =>
    have hg : d181750 p = 1 := by simpa only [d181751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25395 p hg
    simpa only [d181751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24925 p hg
    simpa only [d181751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25397 (p : Pattern) (guard : d181752 p = 1) : d48707 p ≤ (2 : Int) + d130454 p := by
  cases selected : p 50 with
  | false =>
    have hg : d181751 p = 1 := by simpa only [d181752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25396 p hg
    simpa only [d181752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24925 p hg
    simpa only [d181752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25398 (p : Pattern) (guard : d181753 p = 1) : d48748 p ≤ (2 : Int) + d130478 p := by
  cases selected : p 49 with
  | false =>
    have hg : d181752 p = 1 := by simpa only [d181753, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25397 p hg
    simpa only [d181753, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181753, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24965 p hg
    simpa only [d181753, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25399 (p : Pattern) (guard : d181754 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181754, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24924 p hg
    simpa only [d181754, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181753 p = 1 := by simpa only [d181754, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25398 p hg
    simpa only [d181754, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25400 (p : Pattern) (guard : d181755 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181754 p = 1 := by simpa only [d181755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25399 p hg
    simpa only [d181755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25401 (p : Pattern) (guard : d181756 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181755 p = 1 := by simpa only [d181756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25400 p hg
    simpa only [d181756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25402 (p : Pattern) (guard : d181757 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181756 p = 1 := by simpa only [d181757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25401 p hg
    simpa only [d181757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25403 (p : Pattern) (guard : d181758 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181757 p = 1 := by simpa only [d181758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25402 p hg
    simpa only [d181758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25404 (p : Pattern) (guard : d181759 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181758 p = 1 := by simpa only [d181759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25403 p hg
    simpa only [d181759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25405 (p : Pattern) (guard : d181760 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181759 p = 1 := by simpa only [d181760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25404 p hg
    simpa only [d181760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25406 (p : Pattern) (guard : d181761 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181760 p = 1 := by simpa only [d181761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25405 p hg
    simpa only [d181761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25407 (p : Pattern) (guard : d181762 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181761 p = 1 := by simpa only [d181762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25406 p hg
    simpa only [d181762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25408 (p : Pattern) (guard : d181763 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181762 p = 1 := by simpa only [d181763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25407 p hg
    simpa only [d181763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25409 (p : Pattern) (guard : d181764 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181763 p = 1 := by simpa only [d181764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25408 p hg
    simpa only [d181764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25410 (p : Pattern) (guard : d181765 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10250 with
  | false =>
    have hg : d181734 p = 1 := by simpa only [d181765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25313 p hg
    simpa only [d181765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181764 p = 1 := by simpa only [d181765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25409 p hg
    simpa only [d181765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25411 (p : Pattern) (guard : d181766 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 260 with
  | false =>
    have hg : d181765 p = 1 := by simpa only [d181766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25410 p hg
    simpa only [d181766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25412 (p : Pattern) (guard : d181767 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 259 with
  | false =>
    have hg : d181766 p = 1 := by simpa only [d181767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25411 p hg
    simpa only [d181767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25413 (p : Pattern) (guard : d181768 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 258 with
  | false =>
    have hg : d181767 p = 1 := by simpa only [d181768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25412 p hg
    simpa only [d181768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25414 (p : Pattern) (guard : d181769 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 257 with
  | false =>
    have hg : d181768 p = 1 := by simpa only [d181769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25413 p hg
    simpa only [d181769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25415 (p : Pattern) (guard : d181770 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 256 with
  | false =>
    have hg : d181769 p = 1 := by simpa only [d181770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25414 p hg
    simpa only [d181770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25416 (p : Pattern) (guard : d181771 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 255 with
  | false =>
    have hg : d181770 p = 1 := by simpa only [d181771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25415 p hg
    simpa only [d181771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25417 (p : Pattern) (guard : d181772 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 254 with
  | false =>
    have hg : d181771 p = 1 := by simpa only [d181772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25416 p hg
    simpa only [d181772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25418 (p : Pattern) (guard : d181773 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 253 with
  | false =>
    have hg : d181772 p = 1 := by simpa only [d181773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25417 p hg
    simpa only [d181773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25419 (p : Pattern) (guard : d181774 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 252 with
  | false =>
    have hg : d181773 p = 1 := by simpa only [d181774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25418 p hg
    simpa only [d181774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25420 (p : Pattern) (guard : d181775 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 251 with
  | false =>
    have hg : d181774 p = 1 := by simpa only [d181775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25419 p hg
    simpa only [d181775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25421 (p : Pattern) (guard : d181776 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 250 with
  | false =>
    have hg : d181775 p = 1 := by simpa only [d181776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25420 p hg
    simpa only [d181776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25422 (p : Pattern) (guard : d181777 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 249 with
  | false =>
    have hg : d181776 p = 1 := by simpa only [d181777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25421 p hg
    simpa only [d181777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25423 (p : Pattern) (guard : d181778 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 245 with
  | false =>
    have hg : d181777 p = 1 := by simpa only [d181778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25422 p hg
    simpa only [d181778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25424 (p : Pattern) (guard : d181779 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 200 with
  | false =>
    have hg : d181778 p = 1 := by simpa only [d181779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25423 p hg
    simpa only [d181779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25425 (p : Pattern) (guard : d181780 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 199 with
  | false =>
    have hg : d181779 p = 1 := by simpa only [d181780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25424 p hg
    simpa only [d181780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25426 (p : Pattern) (guard : d181781 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 186 with
  | false =>
    have hg : d181780 p = 1 := by simpa only [d181781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25425 p hg
    simpa only [d181781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25427 (p : Pattern) (guard : d181782 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 185 with
  | false =>
    have hg : d181781 p = 1 := by simpa only [d181782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25426 p hg
    simpa only [d181782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25428 (p : Pattern) (guard : d181783 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 184 with
  | false =>
    have hg : d181782 p = 1 := by simpa only [d181783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25427 p hg
    simpa only [d181783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25429 (p : Pattern) (guard : d181784 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 181 with
  | false =>
    have hg : d181783 p = 1 := by simpa only [d181784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25428 p hg
    simpa only [d181784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25430 (p : Pattern) (guard : d181785 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 177 with
  | false =>
    have hg : d181784 p = 1 := by simpa only [d181785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25429 p hg
    simpa only [d181785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25431 (p : Pattern) (guard : d181786 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 164 with
  | false =>
    have hg : d181785 p = 1 := by simpa only [d181786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25430 p hg
    simpa only [d181786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25432 (p : Pattern) (guard : d181787 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 156 with
  | false =>
    have hg : d181786 p = 1 := by simpa only [d181787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25431 p hg
    simpa only [d181787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25433 (p : Pattern) (guard : d181788 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 155 with
  | false =>
    have hg : d181787 p = 1 := by simpa only [d181788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25432 p hg
    simpa only [d181788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25434 (p : Pattern) (guard : d181789 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 134 with
  | false =>
    have hg : d181788 p = 1 := by simpa only [d181789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25433 p hg
    simpa only [d181789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25435 (p : Pattern) (guard : d181790 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 133 with
  | false =>
    have hg : d181789 p = 1 := by simpa only [d181790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25434 p hg
    simpa only [d181790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25436 (p : Pattern) (guard : d181791 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 120 with
  | false =>
    have hg : d181790 p = 1 := by simpa only [d181791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25435 p hg
    simpa only [d181791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25437 (p : Pattern) (guard : d181792 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 118 with
  | false =>
    have hg : d181791 p = 1 := by simpa only [d181792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25436 p hg
    simpa only [d181792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25438 (p : Pattern) (guard : d181793 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 114 with
  | false =>
    have hg : d181792 p = 1 := by simpa only [d181793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25437 p hg
    simpa only [d181793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25439 (p : Pattern) (guard : d181794 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 111 with
  | false =>
    have hg : d181793 p = 1 := by simpa only [d181794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25438 p hg
    simpa only [d181794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25440 (p : Pattern) (guard : d181795 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 98 with
  | false =>
    have hg : d181794 p = 1 := by simpa only [d181795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25439 p hg
    simpa only [d181795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25441 (p : Pattern) (guard : d181796 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 97 with
  | false =>
    have hg : d181795 p = 1 := by simpa only [d181796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25440 p hg
    simpa only [d181796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25442 (p : Pattern) (guard : d181797 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 94 with
  | false =>
    have hg : d181796 p = 1 := by simpa only [d181797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25441 p hg
    simpa only [d181797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25443 (p : Pattern) (guard : d181798 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 76 with
  | false =>
    have hg : d181797 p = 1 := by simpa only [d181798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25442 p hg
    simpa only [d181798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25444 (p : Pattern) (guard : d181799 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 67 with
  | false =>
    have hg : d181798 p = 1 := by simpa only [d181799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25443 p hg
    simpa only [d181799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25445 (p : Pattern) (guard : d181800 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 52 with
  | false =>
    have hg : d181799 p = 1 := by simpa only [d181800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25444 p hg
    simpa only [d181800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25446 (p : Pattern) (guard : d181801 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 47 with
  | false =>
    have hg : d181800 p = 1 := by simpa only [d181801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25445 p hg
    simpa only [d181801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25447 (p : Pattern) (guard : d181802 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 46 with
  | false =>
    have hg : d181801 p = 1 := by simpa only [d181802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25446 p hg
    simpa only [d181802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25448 (p : Pattern) (guard : d181803 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 45 with
  | false =>
    have hg : d181802 p = 1 := by simpa only [d181803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25447 p hg
    simpa only [d181803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25449 (p : Pattern) (guard : d181804 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 30 with
  | false =>
    have hg : d181803 p = 1 := by simpa only [d181804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25448 p hg
    simpa only [d181804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25450 (p : Pattern) (guard : d181805 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 29 with
  | false =>
    have hg : d181804 p = 1 := by simpa only [d181805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25449 p hg
    simpa only [d181805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25451 (p : Pattern) (guard : d181806 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 28 with
  | false =>
    have hg : d181805 p = 1 := by simpa only [d181806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25450 p hg
    simpa only [d181806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25452 (p : Pattern) (guard : d181807 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 27 with
  | false =>
    have hg : d181806 p = 1 := by simpa only [d181807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25451 p hg
    simpa only [d181807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25453 (p : Pattern) (guard : d181808 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 25 with
  | false =>
    have hg : d181807 p = 1 := by simpa only [d181808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25452 p hg
    simpa only [d181808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25454 (p : Pattern) (guard : d0 p = 1) : d48749 p ≤ (-1 : Int) + d48547 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25455 (p : Pattern) (guard : d0 p = 1) : d48749 p ≤ (-2 : Int) + d48547 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25456 (p : Pattern) (guard : d0 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25457 (p : Pattern) (guard : d0 p = 1) : d48697 p ≤ (-1 : Int) + d188502 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25458 (p : Pattern) (guard : d0 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25459 (p : Pattern) (guard : d0 p = 1) : d48613 p ≤ (-1 : Int) + d188495 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25460 (p : Pattern) (guard : d0 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25461 (p : Pattern) (guard : d0 p = 1) : d48630 p ≤ (-1 : Int) + d188492 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25462 (p : Pattern) (guard : d0 p = 1) : d48635 p ≤ (-1 : Int) + d188488 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25463 (p : Pattern) (guard : d0 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25464 (p : Pattern) (guard : d0 p = 1) : d48567 p ≤ (-1 : Int) + d48502 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25465 (p : Pattern) (guard : d14 p = 1) : d2 p ≤ (-1 : Int) + d4 p := by
  have ha := bounds2 p
  have hb := bounds4 p
  omega
theorem compare25466 (p : Pattern) (guard : d0 p = 1) : d47629 p ≤ (-1 : Int) + d47616 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25467 (p : Pattern) (guard : d15 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 246 with
  | false =>
    have hg : d14 p = 1 := by simpa only [d15, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25465 p hg
    simpa only [d15, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25466 p hg
    simpa only [d15, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25468 (p : Pattern) (guard : d0 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25469 (p : Pattern) (guard : d16 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 226 with
  | false =>
    have hg : d15 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25467 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25470 (p : Pattern) (guard : d17 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d16 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25469 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25471 (p : Pattern) (guard : d18 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d17 p = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25470 p hg
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25472 (p : Pattern) (guard : d19 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d18 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25471 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25473 (p : Pattern) (guard : d20 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d19 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25472 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25474 (p : Pattern) (guard : d21 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d20 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25473 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25475 (p : Pattern) (guard : d22 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d21 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25474 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25476 (p : Pattern) (guard : d0 p = 1) : d47631 p ≤ (-1 : Int) + d47618 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25477 (p : Pattern) (guard : d23 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d22 p = 1 := by simpa only [d23, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25475 p hg
    simpa only [d23, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d23, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d23, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25478 (p : Pattern) (guard : d0 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25479 (p : Pattern) (guard : d24 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d23 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25477 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25478 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25480 (p : Pattern) (guard : d0 p = 1) : d47619 p ≤ (-1 : Int) + d47619 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25481 (p : Pattern) (guard : d25 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d24 p = 1 := by simpa only [d25, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25479 p hg
    simpa only [d25, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d25, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25482 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (-1 : Int) + d47682 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25483 (p : Pattern) (guard : d26 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d25 p = 1 := by simpa only [d26, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25481 p hg
    simpa only [d26, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d26, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d26, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25484 (p : Pattern) (guard : d27 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d27, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d27, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d26 p = 1 := by simpa only [d27, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25483 p hg
    simpa only [d27, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25485 (p : Pattern) (guard : d0 p = 1) : d48700 p ≤ (-1 : Int) + d48502 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25486 (p : Pattern) (guard : d28 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d27 p = 1 := by simpa only [d28, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25484 p hg
    simpa only [d28, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d28, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d28, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25487 (p : Pattern) (guard : d0 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25488 (p : Pattern) (guard : d29 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d28 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25486 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25489 (p : Pattern) (guard : d30 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d29 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25488 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25490 (p : Pattern) (guard : d31 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 157 with
  | false =>
    have hg : d30 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25489 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25491 (p : Pattern) (guard : d32 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d32, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d32, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d31 p = 1 := by simpa only [d32, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25490 p hg
    simpa only [d32, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25492 (p : Pattern) (guard : d33 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d33, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d33, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32 p = 1 := by simpa only [d33, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25491 p hg
    simpa only [d33, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25493 (p : Pattern) (guard : d0 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25494 (p : Pattern) (guard : d34 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d33 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25492 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25493 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25495 (p : Pattern) (guard : d35 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d34 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25494 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25493 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25496 (p : Pattern) (guard : d0 p = 1) : d48600 p ≤ (-1 : Int) + d48498 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25497 (p : Pattern) (guard : d14 p = 1) : d0 p ≤ (-1 : Int) + d2 p := by
  have ha := bounds0 p
  have hb := bounds2 p
  omega
theorem compare25498 (p : Pattern) (guard : d0 p = 1) : d47612 p ≤ (-1 : Int) + d47629 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare25499 (p : Pattern) (guard : d15 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 246 with
  | false =>
    have hg : d14 p = 1 := by simpa only [d15, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25497 p hg
    simpa only [d15, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25498 p hg
    simpa only [d15, d47613, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
