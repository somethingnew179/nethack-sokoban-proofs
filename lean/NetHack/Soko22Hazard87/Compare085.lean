import NetHack.Soko22Hazard87.Compare084
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare21250 (p : Pattern) (guard : d10087 p = 1) : d47736 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10085 p = 1 := by simpa only [d10087, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21249 p hg
    simpa only [d10087, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10087, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20462 p hg
    simpa only [d10087, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21251 (p : Pattern) (guard : d15156 p = 1) : d47737 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15156, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20459 p hg
    simpa only [d15156, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10087 p = 1 := by simpa only [d15156, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21250 p hg
    simpa only [d15156, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21252 (p : Pattern) (guard : d15157 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15156 p = 1 := by simpa only [d15157, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21251 p hg
    simpa only [d15157, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15157, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20465 p hg
    simpa only [d15157, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21253 (p : Pattern) (guard : d16790 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15152 p = 1 := by simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21247 p hg
    simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15157 p = 1 := by simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21252 p hg
    simpa only [d16790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21254 (p : Pattern) (guard : d16791 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16789 p = 1 := by simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21242 p hg
    simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16790 p = 1 := by simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21253 p hg
    simpa only [d16791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21255 (p : Pattern) (guard : d1569 p = 1) : d47708 p ≤ (0 : Int) + d47708 p := by
  omega
theorem compare21256 (p : Pattern) (guard : d1570 p = 1) : d47735 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1569 p = 1 := by simpa only [d1570, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21255 p hg
    simpa only [d1570, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1570, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d1570, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21257 (p : Pattern) (guard : d1571 p = 1) : d47736 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1570 p = 1 := by simpa only [d1571, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21256 p hg
    simpa only [d1571, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1571, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20462 p hg
    simpa only [d1571, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21258 (p : Pattern) (guard : d1572 p = 1) : d47737 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1572, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20459 p hg
    simpa only [d1572, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1571 p = 1 := by simpa only [d1572, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21257 p hg
    simpa only [d1572, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21259 (p : Pattern) (guard : d1573 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1572 p = 1 := by simpa only [d1573, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21258 p hg
    simpa only [d1573, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1573, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20465 p hg
    simpa only [d1573, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21260 (p : Pattern) (guard : d10114 p = 1) : d47708 p ≤ (0 : Int) + d47708 p := by
  omega
theorem compare21261 (p : Pattern) (guard : d10115 p = 1) : d47735 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10114 p = 1 := by simpa only [d10115, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21260 p hg
    simpa only [d10115, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10115, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d10115, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21262 (p : Pattern) (guard : d10117 p = 1) : d47736 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10115 p = 1 := by simpa only [d10117, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21261 p hg
    simpa only [d10117, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10117, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20462 p hg
    simpa only [d10117, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21263 (p : Pattern) (guard : d16792 p = 1) : d47737 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16792, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20459 p hg
    simpa only [d16792, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10117 p = 1 := by simpa only [d16792, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21262 p hg
    simpa only [d16792, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21264 (p : Pattern) (guard : d16793 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16792 p = 1 := by simpa only [d16793, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21263 p hg
    simpa only [d16793, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16793, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20465 p hg
    simpa only [d16793, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21265 (p : Pattern) (guard : d16794 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1573 p = 1 := by simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21259 p hg
    simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16793 p = 1 := by simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21264 p hg
    simpa only [d16794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21266 (p : Pattern) (guard : d15158 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15157 p = 1 := by simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21252 p hg
    simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20467 p hg
    simpa only [d15158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21267 (p : Pattern) (guard : d16795 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16794 p = 1 := by simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21265 p hg
    simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15158 p = 1 := by simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21266 p hg
    simpa only [d16795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21268 (p : Pattern) (guard : d16796 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16791 p = 1 := by simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21254 p hg
    simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16795 p = 1 := by simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21267 p hg
    simpa only [d16796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21269 (p : Pattern) (guard : d16797 p = 1) : d48346 p ≤ (0 : Int) + d173722 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16797, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20458 p hg
    simpa only [d16797, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16796 p = 1 := by simpa only [d16797, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21268 p hg
    simpa only [d16797, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21270 (p : Pattern) (guard : d16798 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16798, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20457 p hg
    simpa only [d16798, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16797 p = 1 := by simpa only [d16798, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21269 p hg
    simpa only [d16798, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21271 (p : Pattern) (guard : d5133 p = 1) : d47708 p ≤ (0 : Int) + d47708 p := by
  omega
theorem compare21272 (p : Pattern) (guard : d5134 p = 1) : d47735 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5133 p = 1 := by simpa only [d5134, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21271 p hg
    simpa only [d5134, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5134, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d5134, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21273 (p : Pattern) (guard : d5135 p = 1) : d47736 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5134 p = 1 := by simpa only [d5135, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21272 p hg
    simpa only [d5135, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5135, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20462 p hg
    simpa only [d5135, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21274 (p : Pattern) (guard : d5136 p = 1) : d47737 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5136, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20459 p hg
    simpa only [d5136, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5135 p = 1 := by simpa only [d5136, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21273 p hg
    simpa only [d5136, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21275 (p : Pattern) (guard : d5137 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5136 p = 1 := by simpa only [d5137, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21274 p hg
    simpa only [d5137, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5137, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20465 p hg
    simpa only [d5137, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21276 (p : Pattern) (guard : d5138 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d5137 p = 1 := by simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21275 p hg
    simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20467 p hg
    simpa only [d5138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21277 (p : Pattern) (guard : d10134 p = 1) : d47708 p ≤ (0 : Int) + d47708 p := by
  omega
theorem compare21278 (p : Pattern) (guard : d10135 p = 1) : d47735 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10134 p = 1 := by simpa only [d10135, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21277 p hg
    simpa only [d10135, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10135, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d10135, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21279 (p : Pattern) (guard : d10137 p = 1) : d47736 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10135 p = 1 := by simpa only [d10137, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21278 p hg
    simpa only [d10137, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10137, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20462 p hg
    simpa only [d10137, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21280 (p : Pattern) (guard : d15163 p = 1) : d47737 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15163, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20459 p hg
    simpa only [d15163, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10137 p = 1 := by simpa only [d15163, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21279 p hg
    simpa only [d15163, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21281 (p : Pattern) (guard : d15164 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15163 p = 1 := by simpa only [d15164, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21280 p hg
    simpa only [d15164, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15164, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20465 p hg
    simpa only [d15164, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21282 (p : Pattern) (guard : d15165 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15164 p = 1 := by simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21281 p hg
    simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20467 p hg
    simpa only [d15165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21283 (p : Pattern) (guard : d15166 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d5138 p = 1 := by simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21276 p hg
    simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15165 p = 1 := by simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21282 p hg
    simpa only [d15166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21284 (p : Pattern) (guard : d16799 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16795 p = 1 := by simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21267 p hg
    simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15166 p = 1 := by simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21283 p hg
    simpa only [d16799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21285 (p : Pattern) (guard : d16800 p = 1) : d48346 p ≤ (0 : Int) + d173722 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16800, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20458 p hg
    simpa only [d16800, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16799 p = 1 := by simpa only [d16800, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21284 p hg
    simpa only [d16800, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21286 (p : Pattern) (guard : d16801 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16801, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20457 p hg
    simpa only [d16801, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16800 p = 1 := by simpa only [d16801, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21285 p hg
    simpa only [d16801, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21287 (p : Pattern) (guard : d16802 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16798 p = 1 := by simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21270 p hg
    simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16801 p = 1 := by simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21286 p hg
    simpa only [d16802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21288 (p : Pattern) (guard : d1581 p = 1) : d47708 p ≤ (0 : Int) + d47708 p := by
  omega
theorem compare21289 (p : Pattern) (guard : d1582 p = 1) : d47735 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1581 p = 1 := by simpa only [d1582, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21288 p hg
    simpa only [d1582, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1582, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d1582, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21290 (p : Pattern) (guard : d1583 p = 1) : d47736 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1582 p = 1 := by simpa only [d1583, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21289 p hg
    simpa only [d1583, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1583, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20462 p hg
    simpa only [d1583, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21291 (p : Pattern) (guard : d1584 p = 1) : d47737 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1584, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20459 p hg
    simpa only [d1584, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1583 p = 1 := by simpa only [d1584, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21290 p hg
    simpa only [d1584, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21292 (p : Pattern) (guard : d1585 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1584 p = 1 := by simpa only [d1585, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21291 p hg
    simpa only [d1585, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1585, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20465 p hg
    simpa only [d1585, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21293 (p : Pattern) (guard : d1588 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1585 p = 1 := by simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21292 p hg
    simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20467 p hg
    simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21294 (p : Pattern) (guard : d15171 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1588 p = 1 := by simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21293 p hg
    simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15165 p = 1 := by simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21282 p hg
    simpa only [d15171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21295 (p : Pattern) (guard : d16803 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16795 p = 1 := by simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21267 p hg
    simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15171 p = 1 := by simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21294 p hg
    simpa only [d16803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21296 (p : Pattern) (guard : d16804 p = 1) : d48346 p ≤ (0 : Int) + d173722 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16804, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20458 p hg
    simpa only [d16804, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16803 p = 1 := by simpa only [d16804, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21295 p hg
    simpa only [d16804, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21297 (p : Pattern) (guard : d16805 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16805, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20457 p hg
    simpa only [d16805, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16804 p = 1 := by simpa only [d16805, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21296 p hg
    simpa only [d16805, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21298 (p : Pattern) (guard : d16806 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16805 p = 1 := by simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21297 p hg
    simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20473 p hg
    simpa only [d16806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21299 (p : Pattern) (guard : d16807 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16802 p = 1 := by simpa only [d16807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21287 p hg
    simpa only [d16807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16806 p = 1 := by simpa only [d16807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21298 p hg
    simpa only [d16807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21300 (p : Pattern) (guard : d16808 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16807 p = 1 := by simpa only [d16808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21299 p hg
    simpa only [d16808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20473 p hg
    simpa only [d16808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21301 (p : Pattern) (guard : d16809 p = 1) : d48356 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16808 p = 1 := by simpa only [d16809, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21300 p hg
    simpa only [d16809, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16809, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20477 p hg
    simpa only [d16809, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21302 (p : Pattern) (guard : d16810 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16810, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20456 p hg
    simpa only [d16810, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16809 p = 1 := by simpa only [d16810, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21301 p hg
    simpa only [d16810, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21303 (p : Pattern) (guard : d16811 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16806 p = 1 := by simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21298 p hg
    simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20473 p hg
    simpa only [d16811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21304 (p : Pattern) (guard : d16812 p = 1) : d48354 p ≤ (0 : Int) + d173723 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16811 p = 1 := by simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21303 p hg
    simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20473 p hg
    simpa only [d16812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21305 (p : Pattern) (guard : d16813 p = 1) : d48356 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16812 p = 1 := by simpa only [d16813, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21304 p hg
    simpa only [d16813, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16813, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20477 p hg
    simpa only [d16813, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21306 (p : Pattern) (guard : d16814 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16814, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20456 p hg
    simpa only [d16814, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16813 p = 1 := by simpa only [d16814, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21305 p hg
    simpa only [d16814, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21307 (p : Pattern) (guard : d16815 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16810 p = 1 := by simpa only [d16815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21302 p hg
    simpa only [d16815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16814 p = 1 := by simpa only [d16815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21306 p hg
    simpa only [d16815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21308 (p : Pattern) (guard : d16816 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16815 p = 1 := by simpa only [d16816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21307 p hg
    simpa only [d16816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d16816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21309 (p : Pattern) (guard : d16817 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16816 p = 1 := by simpa only [d16817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21308 p hg
    simpa only [d16817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d16817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21310 (p : Pattern) (guard : d16831 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16817 p = 1 := by simpa only [d16831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21309 p hg
    simpa only [d16831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d16831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21311 (p : Pattern) (guard : d16819 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16814 p = 1 := by simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21306 p hg
    simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d16819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21312 (p : Pattern) (guard : d16820 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16819 p = 1 := by simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21311 p hg
    simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d16820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21313 (p : Pattern) (guard : d16821 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16820 p = 1 := by simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21312 p hg
    simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d16821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21314 (p : Pattern) (guard : d16832 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16821 p = 1 := by simpa only [d16832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21313 p hg
    simpa only [d16832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d16832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21315 (p : Pattern) (guard : d16833 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16831 p = 1 := by simpa only [d16833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21310 p hg
    simpa only [d16833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16832 p = 1 := by simpa only [d16833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21314 p hg
    simpa only [d16833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21316 (p : Pattern) (guard : d16834 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d16834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16833 p = 1 := by simpa only [d16834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21315 p hg
    simpa only [d16834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21317 (p : Pattern) (guard : d16835 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16834 p = 1 := by simpa only [d16835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21316 p hg
    simpa only [d16835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d16835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21318 (p : Pattern) (guard : d16836 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d16836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16835 p = 1 := by simpa only [d16836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21317 p hg
    simpa only [d16836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21319 (p : Pattern) (guard : d16837 p = 1) : d48357 p ≤ (0 : Int) + d173725 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20455 p hg
    simpa only [d16837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16836 p = 1 := by simpa only [d16837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21318 p hg
    simpa only [d16837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21320 (p : Pattern) (guard : d171170 p = 1) : d48358 p ≤ (0 : Int) + d173726 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171170, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d171170, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16837 p = 1 := by simpa only [d171170, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21319 p hg
    simpa only [d171170, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21321 (p : Pattern) (guard : d171171 p = 1) : d48358 p ≤ (0 : Int) + d173726 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20454 p hg
    simpa only [d171171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171170 p = 1 := by simpa only [d171171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21320 p hg
    simpa only [d171171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21322 (p : Pattern) (guard : d171172 p = 1) : d48358 p ≤ (0 : Int) + d173726 p := by
  cases selected : p 69 with
  | false =>
    have hg : d171171 p = 1 := by simpa only [d171172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21321 p hg
    simpa only [d171172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20454 p hg
    simpa only [d171172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21323 (p : Pattern) (guard : d171173 p = 1) : d48358 p ≤ (0 : Int) + d173726 p := by
  cases selected : p 51 with
  | false =>
    have hg : d171172 p = 1 := by simpa only [d171173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21322 p hg
    simpa only [d171173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20454 p hg
    simpa only [d171173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21324 (p : Pattern) (guard : d171174 p = 1) : d48358 p ≤ (0 : Int) + d173726 p := by
  cases selected : p 50 with
  | false =>
    have hg : d171173 p = 1 := by simpa only [d171174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21323 p hg
    simpa only [d171174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20454 p hg
    simpa only [d171174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21325 (p : Pattern) (guard : d171175 p = 1) : d48359 p ≤ (0 : Int) + d173727 p := by
  cases selected : p 49 with
  | false =>
    have hg : d171169 p = 1 := by simpa only [d171175, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21231 p hg
    simpa only [d171175, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171174 p = 1 := by simpa only [d171175, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21324 p hg
    simpa only [d171175, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21326 (p : Pattern) (guard : d175690 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 48 with
  | false =>
    have hg : d171175 p = 1 := by simpa only [d175690, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21325 p hg
    simpa only [d175690, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d175690, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20495 p hg
    simpa only [d175690, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21327 (p : Pattern) (guard : d175691 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175690 p = 1 := by simpa only [d175691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21326 p hg
    simpa only [d175691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21328 (p : Pattern) (guard : d175692 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175691 p = 1 := by simpa only [d175692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21327 p hg
    simpa only [d175692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21329 (p : Pattern) (guard : d175693 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175692 p = 1 := by simpa only [d175693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21328 p hg
    simpa only [d175693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21330 (p : Pattern) (guard : d175694 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175693 p = 1 := by simpa only [d175694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21329 p hg
    simpa only [d175694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21331 (p : Pattern) (guard : d175695 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175694 p = 1 := by simpa only [d175695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21330 p hg
    simpa only [d175695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21332 (p : Pattern) (guard : d175696 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175695 p = 1 := by simpa only [d175696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21331 p hg
    simpa only [d175696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21333 (p : Pattern) (guard : d175697 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175696 p = 1 := by simpa only [d175697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21332 p hg
    simpa only [d175697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21334 (p : Pattern) (guard : d175698 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175697 p = 1 := by simpa only [d175698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21333 p hg
    simpa only [d175698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21335 (p : Pattern) (guard : d175699 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d175699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20386 p hg
    simpa only [d175699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175698 p = 1 := by simpa only [d175699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21334 p hg
    simpa only [d175699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21336 (p : Pattern) (guard : d175700 p = 1) : d48388 p ≤ (0 : Int) + d173755 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d175689 p = 1 := by simpa only [d175700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21104 p hg
    simpa only [d175700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d175699 p = 1 := by simpa only [d175700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21335 p hg
    simpa only [d175700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21337 (p : Pattern) (guard : d2034 p = 1) : d47619 p ≤ (0 : Int) + d47619 p := by
  omega
theorem compare21338 (p : Pattern) (guard : d2035 p = 1) : d47660 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2034 p = 1 := by simpa only [d2035, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21337 p hg
    simpa only [d2035, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2035, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20395 p hg
    simpa only [d2035, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21339 (p : Pattern) (guard : d2036 p = 1) : d47663 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2035 p = 1 := by simpa only [d2036, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21338 p hg
    simpa only [d2036, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2036, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20397 p hg
    simpa only [d2036, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21340 (p : Pattern) (guard : d2037 p = 1) : d47664 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2037, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20393 p hg
    simpa only [d2037, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2036 p = 1 := by simpa only [d2037, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21339 p hg
    simpa only [d2037, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21341 (p : Pattern) (guard : d2038 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2037 p = 1 := by simpa only [d2038, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21340 p hg
    simpa only [d2038, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2038, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20400 p hg
    simpa only [d2038, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21342 (p : Pattern) (guard : d10363 p = 1) : d47619 p ≤ (0 : Int) + d47619 p := by
  omega
theorem compare21343 (p : Pattern) (guard : d10364 p = 1) : d47660 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10363 p = 1 := by simpa only [d10364, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21342 p hg
    simpa only [d10364, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10364, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20395 p hg
    simpa only [d10364, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21344 (p : Pattern) (guard : d10366 p = 1) : d47663 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10364 p = 1 := by simpa only [d10366, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21343 p hg
    simpa only [d10366, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10366, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20397 p hg
    simpa only [d10366, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21345 (p : Pattern) (guard : d17153 p = 1) : d47664 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17153, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20393 p hg
    simpa only [d17153, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10366 p = 1 := by simpa only [d17153, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21344 p hg
    simpa only [d17153, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21346 (p : Pattern) (guard : d17154 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17153 p = 1 := by simpa only [d17154, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21345 p hg
    simpa only [d17154, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17154, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20400 p hg
    simpa only [d17154, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21347 (p : Pattern) (guard : d17155 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2038 p = 1 := by simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21341 p hg
    simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17154 p = 1 := by simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21346 p hg
    simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21348 (p : Pattern) (guard : d10352 p = 1) : d47619 p ≤ (0 : Int) + d47619 p := by
  omega
theorem compare21349 (p : Pattern) (guard : d10353 p = 1) : d47660 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10352 p = 1 := by simpa only [d10353, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21348 p hg
    simpa only [d10353, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10353, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20395 p hg
    simpa only [d10353, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21350 (p : Pattern) (guard : d10355 p = 1) : d47663 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10353 p = 1 := by simpa only [d10355, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21349 p hg
    simpa only [d10355, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10355, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20397 p hg
    simpa only [d10355, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21351 (p : Pattern) (guard : d13675 p = 1) : d47664 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d13675, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20393 p hg
    simpa only [d13675, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10355 p = 1 := by simpa only [d13675, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21350 p hg
    simpa only [d13675, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21352 (p : Pattern) (guard : d13676 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d13675 p = 1 := by simpa only [d13676, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21351 p hg
    simpa only [d13676, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13676, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20400 p hg
    simpa only [d13676, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21353 (p : Pattern) (guard : d10370 p = 1) : d47619 p ≤ (0 : Int) + d47619 p := by
  omega
theorem compare21354 (p : Pattern) (guard : d10371 p = 1) : d47660 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10370 p = 1 := by simpa only [d10371, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21353 p hg
    simpa only [d10371, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10371, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20395 p hg
    simpa only [d10371, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21355 (p : Pattern) (guard : d10373 p = 1) : d47663 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10371 p = 1 := by simpa only [d10373, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21354 p hg
    simpa only [d10373, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10373, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20397 p hg
    simpa only [d10373, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21356 (p : Pattern) (guard : d15548 p = 1) : d47664 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15548, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20393 p hg
    simpa only [d15548, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10373 p = 1 := by simpa only [d15548, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21355 p hg
    simpa only [d15548, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21357 (p : Pattern) (guard : d15549 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15548 p = 1 := by simpa only [d15549, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21356 p hg
    simpa only [d15549, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15549, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20400 p hg
    simpa only [d15549, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21358 (p : Pattern) (guard : d17156 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d13676 p = 1 := by simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21352 p hg
    simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15549 p = 1 := by simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21357 p hg
    simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21359 (p : Pattern) (guard : d17157 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17155 p = 1 := by simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21347 p hg
    simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17156 p = 1 := by simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21358 p hg
    simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21360 (p : Pattern) (guard : d2052 p = 1) : d47619 p ≤ (0 : Int) + d47619 p := by
  omega
theorem compare21361 (p : Pattern) (guard : d2053 p = 1) : d47660 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2052 p = 1 := by simpa only [d2053, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21360 p hg
    simpa only [d2053, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2053, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20395 p hg
    simpa only [d2053, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21362 (p : Pattern) (guard : d2054 p = 1) : d47663 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2053 p = 1 := by simpa only [d2054, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21361 p hg
    simpa only [d2054, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2054, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20397 p hg
    simpa only [d2054, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21363 (p : Pattern) (guard : d2055 p = 1) : d47664 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2055, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20393 p hg
    simpa only [d2055, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2054 p = 1 := by simpa only [d2055, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21362 p hg
    simpa only [d2055, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21364 (p : Pattern) (guard : d2056 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2055 p = 1 := by simpa only [d2056, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21363 p hg
    simpa only [d2056, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2056, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20400 p hg
    simpa only [d2056, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21365 (p : Pattern) (guard : d10390 p = 1) : d47619 p ≤ (0 : Int) + d47619 p := by
  omega
theorem compare21366 (p : Pattern) (guard : d10391 p = 1) : d47660 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10390 p = 1 := by simpa only [d10391, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21365 p hg
    simpa only [d10391, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10391, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20395 p hg
    simpa only [d10391, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21367 (p : Pattern) (guard : d10393 p = 1) : d47663 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10391 p = 1 := by simpa only [d10393, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21366 p hg
    simpa only [d10393, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10393, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20397 p hg
    simpa only [d10393, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21368 (p : Pattern) (guard : d17158 p = 1) : d47664 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17158, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20393 p hg
    simpa only [d17158, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10393 p = 1 := by simpa only [d17158, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21367 p hg
    simpa only [d17158, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21369 (p : Pattern) (guard : d17159 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17158 p = 1 := by simpa only [d17159, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21368 p hg
    simpa only [d17159, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17159, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20400 p hg
    simpa only [d17159, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21370 (p : Pattern) (guard : d17160 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2056 p = 1 := by simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21364 p hg
    simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17159 p = 1 := by simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21369 p hg
    simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21371 (p : Pattern) (guard : d15550 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15549 p = 1 := by simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21357 p hg
    simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20402 p hg
    simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21372 (p : Pattern) (guard : d17161 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17160 p = 1 := by simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21370 p hg
    simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15550 p = 1 := by simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21371 p hg
    simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21373 (p : Pattern) (guard : d17162 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17157 p = 1 := by simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21359 p hg
    simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17161 p = 1 := by simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21372 p hg
    simpa only [d17162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21374 (p : Pattern) (guard : d17163 p = 1) : d48326 p ≤ (0 : Int) + d173709 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17163, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20392 p hg
    simpa only [d17163, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17162 p = 1 := by simpa only [d17163, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21373 p hg
    simpa only [d17163, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21375 (p : Pattern) (guard : d17164 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17164, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20391 p hg
    simpa only [d17164, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17163 p = 1 := by simpa only [d17164, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21374 p hg
    simpa only [d17164, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21376 (p : Pattern) (guard : d5246 p = 1) : d47619 p ≤ (0 : Int) + d47619 p := by
  omega
theorem compare21377 (p : Pattern) (guard : d5247 p = 1) : d47660 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5246 p = 1 := by simpa only [d5247, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21376 p hg
    simpa only [d5247, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5247, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20395 p hg
    simpa only [d5247, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21378 (p : Pattern) (guard : d5248 p = 1) : d47663 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5247 p = 1 := by simpa only [d5248, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21377 p hg
    simpa only [d5248, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5248, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20397 p hg
    simpa only [d5248, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21379 (p : Pattern) (guard : d5249 p = 1) : d47664 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5249, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20393 p hg
    simpa only [d5249, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5248 p = 1 := by simpa only [d5249, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21378 p hg
    simpa only [d5249, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21380 (p : Pattern) (guard : d5250 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5249 p = 1 := by simpa only [d5250, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21379 p hg
    simpa only [d5250, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5250, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20400 p hg
    simpa only [d5250, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21381 (p : Pattern) (guard : d5251 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d5250 p = 1 := by simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21380 p hg
    simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20402 p hg
    simpa only [d5251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21382 (p : Pattern) (guard : d10411 p = 1) : d47619 p ≤ (0 : Int) + d47619 p := by
  omega
theorem compare21383 (p : Pattern) (guard : d10412 p = 1) : d47660 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10411 p = 1 := by simpa only [d10412, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21382 p hg
    simpa only [d10412, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10412, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20395 p hg
    simpa only [d10412, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21384 (p : Pattern) (guard : d10414 p = 1) : d47663 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10412 p = 1 := by simpa only [d10414, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21383 p hg
    simpa only [d10414, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10414, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20397 p hg
    simpa only [d10414, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21385 (p : Pattern) (guard : d15555 p = 1) : d47664 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15555, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20393 p hg
    simpa only [d15555, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10414 p = 1 := by simpa only [d15555, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21384 p hg
    simpa only [d15555, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21386 (p : Pattern) (guard : d15556 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15555 p = 1 := by simpa only [d15556, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21385 p hg
    simpa only [d15556, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15556, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20400 p hg
    simpa only [d15556, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21387 (p : Pattern) (guard : d15557 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15556 p = 1 := by simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21386 p hg
    simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20402 p hg
    simpa only [d15557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21388 (p : Pattern) (guard : d15558 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d5251 p = 1 := by simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21381 p hg
    simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15557 p = 1 := by simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21387 p hg
    simpa only [d15558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21389 (p : Pattern) (guard : d17165 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17161 p = 1 := by simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21372 p hg
    simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15558 p = 1 := by simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21388 p hg
    simpa only [d17165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21390 (p : Pattern) (guard : d17166 p = 1) : d48326 p ≤ (0 : Int) + d173709 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17166, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20392 p hg
    simpa only [d17166, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17165 p = 1 := by simpa only [d17166, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21389 p hg
    simpa only [d17166, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21391 (p : Pattern) (guard : d17167 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17167, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20391 p hg
    simpa only [d17167, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17166 p = 1 := by simpa only [d17167, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21390 p hg
    simpa only [d17167, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21392 (p : Pattern) (guard : d17168 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17164 p = 1 := by simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21375 p hg
    simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17167 p = 1 := by simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21391 p hg
    simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21393 (p : Pattern) (guard : d2064 p = 1) : d47619 p ≤ (0 : Int) + d47619 p := by
  omega
theorem compare21394 (p : Pattern) (guard : d2065 p = 1) : d47660 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2064 p = 1 := by simpa only [d2065, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21393 p hg
    simpa only [d2065, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2065, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20395 p hg
    simpa only [d2065, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21395 (p : Pattern) (guard : d2066 p = 1) : d47663 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2065 p = 1 := by simpa only [d2066, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21394 p hg
    simpa only [d2066, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2066, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20397 p hg
    simpa only [d2066, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21396 (p : Pattern) (guard : d2067 p = 1) : d47664 p ≤ (0 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2067, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20393 p hg
    simpa only [d2067, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2066 p = 1 := by simpa only [d2067, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21395 p hg
    simpa only [d2067, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21397 (p : Pattern) (guard : d2068 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2067 p = 1 := by simpa only [d2068, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21396 p hg
    simpa only [d2068, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2068, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20400 p hg
    simpa only [d2068, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21398 (p : Pattern) (guard : d2071 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2068 p = 1 := by simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21397 p hg
    simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20402 p hg
    simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21399 (p : Pattern) (guard : d15563 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2071 p = 1 := by simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21398 p hg
    simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15557 p = 1 := by simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21387 p hg
    simpa only [d15563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21400 (p : Pattern) (guard : d17169 p = 1) : d48313 p ≤ (0 : Int) + d173708 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17161 p = 1 := by simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21372 p hg
    simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15563 p = 1 := by simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21399 p hg
    simpa only [d17169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21401 (p : Pattern) (guard : d17170 p = 1) : d48326 p ≤ (0 : Int) + d173709 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17170, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20392 p hg
    simpa only [d17170, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17169 p = 1 := by simpa only [d17170, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21400 p hg
    simpa only [d17170, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21402 (p : Pattern) (guard : d17171 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17171, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20391 p hg
    simpa only [d17171, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17170 p = 1 := by simpa only [d17171, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21401 p hg
    simpa only [d17171, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21403 (p : Pattern) (guard : d17172 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17171 p = 1 := by simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21402 p hg
    simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20408 p hg
    simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21404 (p : Pattern) (guard : d17173 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17168 p = 1 := by simpa only [d17173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21392 p hg
    simpa only [d17173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17172 p = 1 := by simpa only [d17173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21403 p hg
    simpa only [d17173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21405 (p : Pattern) (guard : d17174 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17173 p = 1 := by simpa only [d17174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21404 p hg
    simpa only [d17174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20408 p hg
    simpa only [d17174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21406 (p : Pattern) (guard : d17175 p = 1) : d48338 p ≤ (0 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17174 p = 1 := by simpa only [d17175, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21405 p hg
    simpa only [d17175, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17175, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20412 p hg
    simpa only [d17175, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21407 (p : Pattern) (guard : d17176 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17176, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20390 p hg
    simpa only [d17176, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17175 p = 1 := by simpa only [d17176, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21406 p hg
    simpa only [d17176, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21408 (p : Pattern) (guard : d17177 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17172 p = 1 := by simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21403 p hg
    simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20408 p hg
    simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21409 (p : Pattern) (guard : d17178 p = 1) : d48337 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17177 p = 1 := by simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21408 p hg
    simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20408 p hg
    simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21410 (p : Pattern) (guard : d17179 p = 1) : d48338 p ≤ (0 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17178 p = 1 := by simpa only [d17179, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21409 p hg
    simpa only [d17179, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17179, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20412 p hg
    simpa only [d17179, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21411 (p : Pattern) (guard : d17180 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17180, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20390 p hg
    simpa only [d17180, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17179 p = 1 := by simpa only [d17180, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21410 p hg
    simpa only [d17180, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21412 (p : Pattern) (guard : d17181 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17176 p = 1 := by simpa only [d17181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21407 p hg
    simpa only [d17181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17180 p = 1 := by simpa only [d17181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21411 p hg
    simpa only [d17181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21413 (p : Pattern) (guard : d17182 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17181 p = 1 := by simpa only [d17182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21412 p hg
    simpa only [d17182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d17182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21414 (p : Pattern) (guard : d17183 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17182 p = 1 := by simpa only [d17183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21413 p hg
    simpa only [d17183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d17183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21415 (p : Pattern) (guard : d17184 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d17184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17183 p = 1 := by simpa only [d17184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21414 p hg
    simpa only [d17184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21416 (p : Pattern) (guard : d17185 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17180 p = 1 := by simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21411 p hg
    simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21417 (p : Pattern) (guard : d17186 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17185 p = 1 := by simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21416 p hg
    simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21418 (p : Pattern) (guard : d17187 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17186 p = 1 := by simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21417 p hg
    simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21419 (p : Pattern) (guard : d17188 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d17188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17187 p = 1 := by simpa only [d17188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21418 p hg
    simpa only [d17188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21420 (p : Pattern) (guard : d17189 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17184 p = 1 := by simpa only [d17189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21415 p hg
    simpa only [d17189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17188 p = 1 := by simpa only [d17189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21419 p hg
    simpa only [d17189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21421 (p : Pattern) (guard : d17190 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d17190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17189 p = 1 := by simpa only [d17190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21420 p hg
    simpa only [d17190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21422 (p : Pattern) (guard : d17191 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d17190 p = 1 := by simpa only [d17191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21421 p hg
    simpa only [d17191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d17191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21423 (p : Pattern) (guard : d17192 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d17192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17191 p = 1 := by simpa only [d17192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21422 p hg
    simpa only [d17192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21424 (p : Pattern) (guard : d17193 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d17193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17192 p = 1 := by simpa only [d17193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21423 p hg
    simpa only [d17193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21425 (p : Pattern) (guard : d17194 p = 1) : d48340 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17194, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d17194, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17193 p = 1 := by simpa only [d17194, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21424 p hg
    simpa only [d17194, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21426 (p : Pattern) (guard : d17164 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17164, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20426 p hg
    simpa only [d17164, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17163 p = 1 := by simpa only [d17164, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21374 p hg
    simpa only [d17164, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21427 (p : Pattern) (guard : d17167 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17167, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20426 p hg
    simpa only [d17167, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17166 p = 1 := by simpa only [d17167, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21390 p hg
    simpa only [d17167, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21428 (p : Pattern) (guard : d17168 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17164 p = 1 := by simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21426 p hg
    simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17167 p = 1 := by simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21427 p hg
    simpa only [d17168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21429 (p : Pattern) (guard : d17171 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17171, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20426 p hg
    simpa only [d17171, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17170 p = 1 := by simpa only [d17171, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21401 p hg
    simpa only [d17171, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21430 (p : Pattern) (guard : d17172 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17171 p = 1 := by simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21429 p hg
    simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20428 p hg
    simpa only [d17172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21431 (p : Pattern) (guard : d17173 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17168 p = 1 := by simpa only [d17173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21428 p hg
    simpa only [d17173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17172 p = 1 := by simpa only [d17173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21430 p hg
    simpa only [d17173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21432 (p : Pattern) (guard : d17174 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17173 p = 1 := by simpa only [d17174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21431 p hg
    simpa only [d17174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20428 p hg
    simpa only [d17174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21433 (p : Pattern) (guard : d17175 p = 1) : d48329 p ≤ (0 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17174 p = 1 := by simpa only [d17175, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21432 p hg
    simpa only [d17175, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17175, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20412 p hg
    simpa only [d17175, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21434 (p : Pattern) (guard : d17176 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17176, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20425 p hg
    simpa only [d17176, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17175 p = 1 := by simpa only [d17176, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21433 p hg
    simpa only [d17176, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21435 (p : Pattern) (guard : d17177 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17172 p = 1 := by simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21430 p hg
    simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20428 p hg
    simpa only [d17177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21436 (p : Pattern) (guard : d17178 p = 1) : d48327 p ≤ (0 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17177 p = 1 := by simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21435 p hg
    simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20428 p hg
    simpa only [d17178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21437 (p : Pattern) (guard : d17179 p = 1) : d48329 p ≤ (0 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17178 p = 1 := by simpa only [d17179, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21436 p hg
    simpa only [d17179, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17179, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20412 p hg
    simpa only [d17179, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21438 (p : Pattern) (guard : d17180 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17180, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20425 p hg
    simpa only [d17180, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17179 p = 1 := by simpa only [d17180, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21437 p hg
    simpa only [d17180, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21439 (p : Pattern) (guard : d17181 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17176 p = 1 := by simpa only [d17181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21434 p hg
    simpa only [d17181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17180 p = 1 := by simpa only [d17181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21438 p hg
    simpa only [d17181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21440 (p : Pattern) (guard : d17182 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17181 p = 1 := by simpa only [d17182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21439 p hg
    simpa only [d17182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d17182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21441 (p : Pattern) (guard : d17183 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17182 p = 1 := by simpa only [d17183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21440 p hg
    simpa only [d17183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d17183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21442 (p : Pattern) (guard : d17184 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d17184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17183 p = 1 := by simpa only [d17184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21441 p hg
    simpa only [d17184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21443 (p : Pattern) (guard : d17185 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17180 p = 1 := by simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21438 p hg
    simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d17185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21444 (p : Pattern) (guard : d17186 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17185 p = 1 := by simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21443 p hg
    simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d17186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21445 (p : Pattern) (guard : d17187 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17186 p = 1 := by simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21444 p hg
    simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d17187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21446 (p : Pattern) (guard : d17188 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d17188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17187 p = 1 := by simpa only [d17188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21445 p hg
    simpa only [d17188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21447 (p : Pattern) (guard : d17189 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17184 p = 1 := by simpa only [d17189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21442 p hg
    simpa only [d17189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17188 p = 1 := by simpa only [d17189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21446 p hg
    simpa only [d17189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21448 (p : Pattern) (guard : d17190 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d17190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17189 p = 1 := by simpa only [d17190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21447 p hg
    simpa only [d17190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21449 (p : Pattern) (guard : d17191 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d17190 p = 1 := by simpa only [d17191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21448 p hg
    simpa only [d17191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d17191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21450 (p : Pattern) (guard : d17192 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d17192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17191 p = 1 := by simpa only [d17192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21449 p hg
    simpa only [d17192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21451 (p : Pattern) (guard : d17193 p = 1) : d48330 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20388 p hg
    simpa only [d17193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17192 p = 1 := by simpa only [d17193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21450 p hg
    simpa only [d17193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21452 (p : Pattern) (guard : d17197 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17183 p = 1 := by simpa only [d17197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21414 p hg
    simpa only [d17197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d17197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21453 (p : Pattern) (guard : d17198 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17187 p = 1 := by simpa only [d17198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21418 p hg
    simpa only [d17198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d17198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21454 (p : Pattern) (guard : d17199 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d17197 p = 1 := by simpa only [d17199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21452 p hg
    simpa only [d17199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17198 p = 1 := by simpa only [d17199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21453 p hg
    simpa only [d17199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21455 (p : Pattern) (guard : d17200 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d17200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17199 p = 1 := by simpa only [d17200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21454 p hg
    simpa only [d17200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21456 (p : Pattern) (guard : d17201 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d17200 p = 1 := by simpa only [d17201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21455 p hg
    simpa only [d17201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d17201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21457 (p : Pattern) (guard : d17202 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d17202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17201 p = 1 := by simpa only [d17202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21456 p hg
    simpa only [d17202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21458 (p : Pattern) (guard : d17203 p = 1) : d48339 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20389 p hg
    simpa only [d17203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17202 p = 1 := by simpa only [d17203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21457 p hg
    simpa only [d17203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21459 (p : Pattern) (guard : d17204 p = 1) : d48340 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d17193 p = 1 := by simpa only [d17204, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21451 p hg
    simpa only [d17204, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17203 p = 1 := by simpa only [d17204, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21458 p hg
    simpa only [d17204, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21460 (p : Pattern) (guard : d17205 p = 1) : d48340 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 70 with
  | false =>
    have hg : d17194 p = 1 := by simpa only [d17205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21425 p hg
    simpa only [d17205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17204 p = 1 := by simpa only [d17205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21459 p hg
    simpa only [d17205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21461 (p : Pattern) (guard : d17206 p = 1) : d48340 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 69 with
  | false =>
    have hg : d17205 p = 1 := by simpa only [d17206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21460 p hg
    simpa only [d17206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20387 p hg
    simpa only [d17206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21462 (p : Pattern) (guard : d171206 p = 1) : d48340 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 51 with
  | false =>
    have hg : d17206 p = 1 := by simpa only [d171206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21461 p hg
    simpa only [d171206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20387 p hg
    simpa only [d171206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21463 (p : Pattern) (guard : d171207 p = 1) : d48340 p ≤ (0 : Int) + d173717 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20387 p hg
    simpa only [d171207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171206 p = 1 := by simpa only [d171207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21462 p hg
    simpa only [d171207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21464 (p : Pattern) (guard : d2034 p = 1) : d47708 p ≤ (0 : Int) + d47708 p := by
  omega
theorem compare21465 (p : Pattern) (guard : d2035 p = 1) : d47735 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2034 p = 1 := by simpa only [d2035, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21464 p hg
    simpa only [d2035, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2035, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d2035, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21466 (p : Pattern) (guard : d2036 p = 1) : d47736 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2035 p = 1 := by simpa only [d2036, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21465 p hg
    simpa only [d2036, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2036, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20462 p hg
    simpa only [d2036, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21467 (p : Pattern) (guard : d2037 p = 1) : d47737 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2037, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20459 p hg
    simpa only [d2037, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2036 p = 1 := by simpa only [d2037, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21466 p hg
    simpa only [d2037, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21468 (p : Pattern) (guard : d2038 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2037 p = 1 := by simpa only [d2038, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21467 p hg
    simpa only [d2038, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2038, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20465 p hg
    simpa only [d2038, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21469 (p : Pattern) (guard : d10363 p = 1) : d47708 p ≤ (0 : Int) + d47708 p := by
  omega
theorem compare21470 (p : Pattern) (guard : d10364 p = 1) : d47735 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10363 p = 1 := by simpa only [d10364, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21469 p hg
    simpa only [d10364, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10364, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d10364, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21471 (p : Pattern) (guard : d10366 p = 1) : d47736 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10364 p = 1 := by simpa only [d10366, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21470 p hg
    simpa only [d10366, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10366, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20462 p hg
    simpa only [d10366, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21472 (p : Pattern) (guard : d17153 p = 1) : d47737 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17153, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20459 p hg
    simpa only [d17153, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10366 p = 1 := by simpa only [d17153, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21471 p hg
    simpa only [d17153, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21473 (p : Pattern) (guard : d17154 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17153 p = 1 := by simpa only [d17154, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21472 p hg
    simpa only [d17154, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17154, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20465 p hg
    simpa only [d17154, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21474 (p : Pattern) (guard : d17155 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2038 p = 1 := by simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21468 p hg
    simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17154 p = 1 := by simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21473 p hg
    simpa only [d17155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21475 (p : Pattern) (guard : d10352 p = 1) : d47708 p ≤ (0 : Int) + d47708 p := by
  omega
theorem compare21476 (p : Pattern) (guard : d10353 p = 1) : d47735 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10352 p = 1 := by simpa only [d10353, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21475 p hg
    simpa only [d10353, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10353, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d10353, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21477 (p : Pattern) (guard : d10355 p = 1) : d47736 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10353 p = 1 := by simpa only [d10355, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21476 p hg
    simpa only [d10355, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10355, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20462 p hg
    simpa only [d10355, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21478 (p : Pattern) (guard : d13675 p = 1) : d47737 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d13675, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20459 p hg
    simpa only [d13675, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10355 p = 1 := by simpa only [d13675, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21477 p hg
    simpa only [d13675, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21479 (p : Pattern) (guard : d13676 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d13675 p = 1 := by simpa only [d13676, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21478 p hg
    simpa only [d13676, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13676, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20465 p hg
    simpa only [d13676, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21480 (p : Pattern) (guard : d10370 p = 1) : d47708 p ≤ (0 : Int) + d47708 p := by
  omega
theorem compare21481 (p : Pattern) (guard : d10371 p = 1) : d47735 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10370 p = 1 := by simpa only [d10371, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21480 p hg
    simpa only [d10371, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10371, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d10371, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21482 (p : Pattern) (guard : d10373 p = 1) : d47736 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10371 p = 1 := by simpa only [d10373, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21481 p hg
    simpa only [d10373, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10373, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20462 p hg
    simpa only [d10373, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21483 (p : Pattern) (guard : d15548 p = 1) : d47737 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15548, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20459 p hg
    simpa only [d15548, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10373 p = 1 := by simpa only [d15548, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21482 p hg
    simpa only [d15548, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21484 (p : Pattern) (guard : d15549 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15548 p = 1 := by simpa only [d15549, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21483 p hg
    simpa only [d15549, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15549, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20465 p hg
    simpa only [d15549, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21485 (p : Pattern) (guard : d17156 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d13676 p = 1 := by simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21479 p hg
    simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15549 p = 1 := by simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21484 p hg
    simpa only [d17156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21486 (p : Pattern) (guard : d17157 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17155 p = 1 := by simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21474 p hg
    simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17156 p = 1 := by simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21485 p hg
    simpa only [d17157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21487 (p : Pattern) (guard : d2052 p = 1) : d47708 p ≤ (0 : Int) + d47708 p := by
  omega
theorem compare21488 (p : Pattern) (guard : d2053 p = 1) : d47735 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2052 p = 1 := by simpa only [d2053, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21487 p hg
    simpa only [d2053, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2053, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d2053, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21489 (p : Pattern) (guard : d2054 p = 1) : d47736 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2053 p = 1 := by simpa only [d2054, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21488 p hg
    simpa only [d2054, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2054, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20462 p hg
    simpa only [d2054, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21490 (p : Pattern) (guard : d2055 p = 1) : d47737 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2055, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20459 p hg
    simpa only [d2055, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2054 p = 1 := by simpa only [d2055, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21489 p hg
    simpa only [d2055, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21491 (p : Pattern) (guard : d2056 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2055 p = 1 := by simpa only [d2056, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21490 p hg
    simpa only [d2056, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2056, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20465 p hg
    simpa only [d2056, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21492 (p : Pattern) (guard : d10390 p = 1) : d47708 p ≤ (0 : Int) + d47708 p := by
  omega
theorem compare21493 (p : Pattern) (guard : d10391 p = 1) : d47735 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d10390 p = 1 := by simpa only [d10391, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21492 p hg
    simpa only [d10391, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10391, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d10391, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21494 (p : Pattern) (guard : d10393 p = 1) : d47736 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d10391 p = 1 := by simpa only [d10393, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21493 p hg
    simpa only [d10393, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10393, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20462 p hg
    simpa only [d10393, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21495 (p : Pattern) (guard : d17158 p = 1) : d47737 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17158, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20459 p hg
    simpa only [d17158, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10393 p = 1 := by simpa only [d17158, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21494 p hg
    simpa only [d17158, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21496 (p : Pattern) (guard : d17159 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17158 p = 1 := by simpa only [d17159, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21495 p hg
    simpa only [d17159, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17159, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20465 p hg
    simpa only [d17159, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21497 (p : Pattern) (guard : d17160 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2056 p = 1 := by simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21491 p hg
    simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17159 p = 1 := by simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21496 p hg
    simpa only [d17160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21498 (p : Pattern) (guard : d15550 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15549 p = 1 := by simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21484 p hg
    simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20467 p hg
    simpa only [d15550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare21499 (p : Pattern) (guard : d17161 p = 1) : d48345 p ≤ (0 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17160 p = 1 := by simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21497 p hg
    simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15550 p = 1 := by simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21498 p hg
    simpa only [d17161, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
