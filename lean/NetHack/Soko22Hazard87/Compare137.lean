import NetHack.Soko22Hazard87.Compare136
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare34250 (p : Pattern) (guard : d294830 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294825 p = 1 := by simpa only [d294830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34245 p hg
    simpa only [d294830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d294830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34251 (p : Pattern) (guard : d294831 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294830 p = 1 := by simpa only [d294831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34250 p hg
    simpa only [d294831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d294831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34252 (p : Pattern) (guard : d294832 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294831 p = 1 := by simpa only [d294832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34251 p hg
    simpa only [d294832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d294832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34253 (p : Pattern) (guard : d294843 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d294832 p = 1 := by simpa only [d294843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34252 p hg
    simpa only [d294843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d294843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34254 (p : Pattern) (guard : d294844 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294842 p = 1 := by simpa only [d294844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34249 p hg
    simpa only [d294844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294843 p = 1 := by simpa only [d294844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34253 p hg
    simpa only [d294844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34255 (p : Pattern) (guard : d294845 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d294845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294844 p = 1 := by simpa only [d294845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34254 p hg
    simpa only [d294845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34256 (p : Pattern) (guard : d294846 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294845 p = 1 := by simpa only [d294846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34255 p hg
    simpa only [d294846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d294846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34257 (p : Pattern) (guard : d294847 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d294847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294846 p = 1 := by simpa only [d294847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34256 p hg
    simpa only [d294847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34258 (p : Pattern) (guard : d294848 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d294848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294847 p = 1 := by simpa only [d294848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34257 p hg
    simpa only [d294848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34259 (p : Pattern) (guard : d295706 p = 1) : d50001 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295706, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d295706, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294848 p = 1 := by simpa only [d295706, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34258 p hg
    simpa only [d295706, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34260 (p : Pattern) (guard : d295707 p = 1) : d50001 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33935 p hg
    simpa only [d295707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295706 p = 1 := by simpa only [d295707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34259 p hg
    simpa only [d295707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34261 (p : Pattern) (guard : d295708 p = 1) : d50001 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d295707 p = 1 := by simpa only [d295708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34260 p hg
    simpa only [d295708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33935 p hg
    simpa only [d295708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34262 (p : Pattern) (guard : d295709 p = 1) : d50001 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d295708 p = 1 := by simpa only [d295709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34261 p hg
    simpa only [d295709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33935 p hg
    simpa only [d295709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34263 (p : Pattern) (guard : d295710 p = 1) : d50001 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d295709 p = 1 := by simpa only [d295710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34262 p hg
    simpa only [d295710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33935 p hg
    simpa only [d295710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34264 (p : Pattern) (guard : d295711 p = 1) : d50002 p ≤ (0 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d295705 p = 1 := by simpa only [d295711, d50002, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34204 p hg
    simpa only [d295711, d50002, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295710 p = 1 := by simpa only [d295711, d50002, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34263 p hg
    simpa only [d295711, d50002, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34265 (p : Pattern) (guard : d131 p = 1) : d47630 p ≤ (0 : Int) + d47630 p := by
  omega
theorem compare34266 (p : Pattern) (guard : d25432 p = 1) : d49808 p ≤ (0 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d131 p = 1 := by simpa only [d25432, d49808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34265 p hg
    simpa only [d25432, d49808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25432, d49808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34018 p hg
    simpa only [d25432, d49808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34267 (p : Pattern) (guard : d25433 p = 1) : d49808 p ≤ (0 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d25432 p = 1 := by simpa only [d25433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34266 p hg
    simpa only [d25433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34016 p hg
    simpa only [d25433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34268 (p : Pattern) (guard : d25434 p = 1) : d49808 p ≤ (0 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d25433 p = 1 := by simpa only [d25434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34267 p hg
    simpa only [d25434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34016 p hg
    simpa only [d25434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34269 (p : Pattern) (guard : d205998 p = 1) : d49808 p ≤ (0 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d205998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34016 p hg
    simpa only [d205998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d25434 p = 1 := by simpa only [d205998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34268 p hg
    simpa only [d205998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34270 (p : Pattern) (guard : d294647 p = 1) : d49808 p ≤ (0 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34016 p hg
    simpa only [d294647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d205998 p = 1 := by simpa only [d294647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34269 p hg
    simpa only [d294647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34271 (p : Pattern) (guard : d294648 p = 1) : d49831 p ≤ (0 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d294647 p = 1 := by simpa only [d294648, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34270 p hg
    simpa only [d294648, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294648, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34024 p hg
    simpa only [d294648, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34272 (p : Pattern) (guard : d294649 p = 1) : d49831 p ≤ (0 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d294648 p = 1 := by simpa only [d294649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34271 p hg
    simpa only [d294649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34015 p hg
    simpa only [d294649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34273 (p : Pattern) (guard : d294728 p = 1) : d49831 p ≤ (0 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34015 p hg
    simpa only [d294728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294649 p = 1 := by simpa only [d294728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34272 p hg
    simpa only [d294728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34274 (p : Pattern) (guard : d294650 p = 1) : d50030 p ≤ (0 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d294649 p = 1 := by simpa only [d294650, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34120 p hg
    simpa only [d294650, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294650, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33954 p hg
    simpa only [d294650, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34275 (p : Pattern) (guard : d294729 p = 1) : d50031 p ≤ (0 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d294728 p = 1 := by simpa only [d294729, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34273 p hg
    simpa only [d294729, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294650 p = 1 := by simpa only [d294729, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34274 p hg
    simpa only [d294729, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34276 (p : Pattern) (guard : d131 p = 1) : d47634 p ≤ (0 : Int) + d47634 p := by
  omega
theorem compare34277 (p : Pattern) (guard : d25432 p = 1) : d49811 p ≤ (0 : Int) + d47634 p := by
  cases selected : p 224 with
  | false =>
    have hg : d131 p = 1 := by simpa only [d25432, d49811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34276 p hg
    simpa only [d25432, d49811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25432, d49811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34032 p hg
    simpa only [d25432, d49811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34278 (p : Pattern) (guard : d25433 p = 1) : d49811 p ≤ (0 : Int) + d47634 p := by
  cases selected : p 223 with
  | false =>
    have hg : d25432 p = 1 := by simpa only [d25433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34277 p hg
    simpa only [d25433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34030 p hg
    simpa only [d25433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34279 (p : Pattern) (guard : d25434 p = 1) : d49811 p ≤ (0 : Int) + d47634 p := by
  cases selected : p 204 with
  | false =>
    have hg : d25433 p = 1 := by simpa only [d25434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34278 p hg
    simpa only [d25434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34030 p hg
    simpa only [d25434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34280 (p : Pattern) (guard : d205998 p = 1) : d49811 p ≤ (0 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d205998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34030 p hg
    simpa only [d205998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d25434 p = 1 := by simpa only [d205998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34279 p hg
    simpa only [d205998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34281 (p : Pattern) (guard : d294647 p = 1) : d49811 p ≤ (0 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34030 p hg
    simpa only [d294647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d205998 p = 1 := by simpa only [d294647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34280 p hg
    simpa only [d294647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34282 (p : Pattern) (guard : d294648 p = 1) : d49857 p ≤ (0 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d294647 p = 1 := by simpa only [d294648, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34281 p hg
    simpa only [d294648, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294648, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34038 p hg
    simpa only [d294648, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34283 (p : Pattern) (guard : d294649 p = 1) : d49857 p ≤ (0 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d294648 p = 1 := by simpa only [d294649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34282 p hg
    simpa only [d294649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34040 p hg
    simpa only [d294649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34284 (p : Pattern) (guard : d294650 p = 1) : d49865 p ≤ (0 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d294649 p = 1 := by simpa only [d294650, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34283 p hg
    simpa only [d294650, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294650, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d294650, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34285 (p : Pattern) (guard : d294651 p = 1) : d49866 p ≤ (0 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d294650 p = 1 := by simpa only [d294651, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34284 p hg
    simpa only [d294651, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294651, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d294651, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34286 (p : Pattern) (guard : d294730 p = 1) : d50032 p ≤ (0 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d294729 p = 1 := by simpa only [d294730, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34275 p hg
    simpa only [d294730, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294651 p = 1 := by simpa only [d294730, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34285 p hg
    simpa only [d294730, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34287 (p : Pattern) (guard : d294731 p = 1) : d50036 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d294730 p = 1 := by simpa only [d294731, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34286 p hg
    simpa only [d294731, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294731, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34045 p hg
    simpa only [d294731, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34288 (p : Pattern) (guard : d294732 p = 1) : d50036 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34014 p hg
    simpa only [d294732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294731 p = 1 := by simpa only [d294732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34287 p hg
    simpa only [d294732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34289 (p : Pattern) (guard : d293369 p = 1) : d49808 p ≤ (0 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d205998 p = 1 := by simpa only [d293369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34269 p hg
    simpa only [d293369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34016 p hg
    simpa only [d293369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34290 (p : Pattern) (guard : d293370 p = 1) : d49831 p ≤ (0 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d293369 p = 1 := by simpa only [d293370, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34289 p hg
    simpa only [d293370, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293370, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34024 p hg
    simpa only [d293370, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34291 (p : Pattern) (guard : d293371 p = 1) : d49831 p ≤ (0 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d293370 p = 1 := by simpa only [d293371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34290 p hg
    simpa only [d293371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34015 p hg
    simpa only [d293371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34292 (p : Pattern) (guard : d293415 p = 1) : d49831 p ≤ (0 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d293415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34015 p hg
    simpa only [d293415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d293371 p = 1 := by simpa only [d293415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34291 p hg
    simpa only [d293415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34293 (p : Pattern) (guard : d293372 p = 1) : d50030 p ≤ (0 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d293371 p = 1 := by simpa only [d293372, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34128 p hg
    simpa only [d293372, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293372, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33954 p hg
    simpa only [d293372, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34294 (p : Pattern) (guard : d293416 p = 1) : d50031 p ≤ (0 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d293415 p = 1 := by simpa only [d293416, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34292 p hg
    simpa only [d293416, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d293372 p = 1 := by simpa only [d293416, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34293 p hg
    simpa only [d293416, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34295 (p : Pattern) (guard : d293369 p = 1) : d49811 p ≤ (0 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d205998 p = 1 := by simpa only [d293369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34280 p hg
    simpa only [d293369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34030 p hg
    simpa only [d293369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34296 (p : Pattern) (guard : d293370 p = 1) : d49857 p ≤ (0 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d293369 p = 1 := by simpa only [d293370, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34295 p hg
    simpa only [d293370, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293370, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34038 p hg
    simpa only [d293370, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34297 (p : Pattern) (guard : d293371 p = 1) : d49857 p ≤ (0 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d293370 p = 1 := by simpa only [d293371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34296 p hg
    simpa only [d293371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34040 p hg
    simpa only [d293371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34298 (p : Pattern) (guard : d293372 p = 1) : d49865 p ≤ (0 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d293371 p = 1 := by simpa only [d293372, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34297 p hg
    simpa only [d293372, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293372, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d293372, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34299 (p : Pattern) (guard : d293373 p = 1) : d49866 p ≤ (0 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d293372 p = 1 := by simpa only [d293373, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34298 p hg
    simpa only [d293373, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293373, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d293373, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34300 (p : Pattern) (guard : d293417 p = 1) : d50032 p ≤ (0 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d293416 p = 1 := by simpa only [d293417, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34294 p hg
    simpa only [d293417, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d293373 p = 1 := by simpa only [d293417, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34299 p hg
    simpa only [d293417, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34301 (p : Pattern) (guard : d293418 p = 1) : d50036 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d293417 p = 1 := by simpa only [d293418, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34300 p hg
    simpa only [d293418, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293418, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34045 p hg
    simpa only [d293418, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34302 (p : Pattern) (guard : d294957 p = 1) : d50036 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34014 p hg
    simpa only [d294957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d293418 p = 1 := by simpa only [d294957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34301 p hg
    simpa only [d294957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34303 (p : Pattern) (guard : d294958 p = 1) : d50036 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294732 p = 1 := by simpa only [d294958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34288 p hg
    simpa only [d294958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294957 p = 1 := by simpa only [d294958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34302 p hg
    simpa only [d294958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34304 (p : Pattern) (guard : d293813 p = 1) : d50036 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d293418 p = 1 := by simpa only [d293813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34301 p hg
    simpa only [d293813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34014 p hg
    simpa only [d293813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34305 (p : Pattern) (guard : d294962 p = 1) : d50036 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294957 p = 1 := by simpa only [d294962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34302 p hg
    simpa only [d294962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d293813 p = 1 := by simpa only [d294962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34304 p hg
    simpa only [d294962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34306 (p : Pattern) (guard : d294963 p = 1) : d50036 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d294958 p = 1 := by simpa only [d294963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34303 p hg
    simpa only [d294963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294962 p = 1 := by simpa only [d294963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34305 p hg
    simpa only [d294963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34307 (p : Pattern) (guard : d294964 p = 1) : d50037 p ≤ (0 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294964, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34013 p hg
    simpa only [d294964, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294963 p = 1 := by simpa only [d294964, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34306 p hg
    simpa only [d294964, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34308 (p : Pattern) (guard : d294965 p = 1) : d50038 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294965, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34012 p hg
    simpa only [d294965, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294964 p = 1 := by simpa only [d294965, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34307 p hg
    simpa only [d294965, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34309 (p : Pattern) (guard : d294967 p = 1) : d50036 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d293813 p = 1 := by simpa only [d294967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34304 p hg
    simpa only [d294967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34014 p hg
    simpa only [d294967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34310 (p : Pattern) (guard : d294968 p = 1) : d50036 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d294962 p = 1 := by simpa only [d294968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34305 p hg
    simpa only [d294968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294967 p = 1 := by simpa only [d294968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34309 p hg
    simpa only [d294968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34311 (p : Pattern) (guard : d294969 p = 1) : d50037 p ≤ (0 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294969, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34013 p hg
    simpa only [d294969, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294968 p = 1 := by simpa only [d294969, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34310 p hg
    simpa only [d294969, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34312 (p : Pattern) (guard : d294970 p = 1) : d50038 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294970, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34012 p hg
    simpa only [d294970, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294969 p = 1 := by simpa only [d294970, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34311 p hg
    simpa only [d294970, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34313 (p : Pattern) (guard : d294971 p = 1) : d50038 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d294965 p = 1 := by simpa only [d294971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34308 p hg
    simpa only [d294971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294970 p = 1 := by simpa only [d294971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34312 p hg
    simpa only [d294971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34314 (p : Pattern) (guard : d294976 p = 1) : d50038 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d294970 p = 1 := by simpa only [d294976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34312 p hg
    simpa only [d294976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34073 p hg
    simpa only [d294976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34315 (p : Pattern) (guard : d294977 p = 1) : d50038 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d294971 p = 1 := by simpa only [d294977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34313 p hg
    simpa only [d294977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294976 p = 1 := by simpa only [d294977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34314 p hg
    simpa only [d294977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34316 (p : Pattern) (guard : d294978 p = 1) : d50038 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d294977 p = 1 := by simpa only [d294978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34315 p hg
    simpa only [d294978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34073 p hg
    simpa only [d294978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34317 (p : Pattern) (guard : d294979 p = 1) : d50040 p ≤ (0 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d294978 p = 1 := by simpa only [d294979, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34316 p hg
    simpa only [d294979, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294979, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34077 p hg
    simpa only [d294979, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34318 (p : Pattern) (guard : d294980 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294980, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33826 p hg
    simpa only [d294980, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294979 p = 1 := by simpa only [d294980, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34317 p hg
    simpa only [d294980, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34319 (p : Pattern) (guard : d294985 p = 1) : d50038 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d294976 p = 1 := by simpa only [d294985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34314 p hg
    simpa only [d294985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34073 p hg
    simpa only [d294985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34320 (p : Pattern) (guard : d294986 p = 1) : d50038 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d294985 p = 1 := by simpa only [d294986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34319 p hg
    simpa only [d294986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34073 p hg
    simpa only [d294986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34321 (p : Pattern) (guard : d294987 p = 1) : d50040 p ≤ (0 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d294986 p = 1 := by simpa only [d294987, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34320 p hg
    simpa only [d294987, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294987, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34077 p hg
    simpa only [d294987, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34322 (p : Pattern) (guard : d294988 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294988, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33826 p hg
    simpa only [d294988, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294987 p = 1 := by simpa only [d294988, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34321 p hg
    simpa only [d294988, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34323 (p : Pattern) (guard : d294989 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294980 p = 1 := by simpa only [d294989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34318 p hg
    simpa only [d294989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294988 p = 1 := by simpa only [d294989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34322 p hg
    simpa only [d294989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34324 (p : Pattern) (guard : d294990 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294989 p = 1 := by simpa only [d294990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34323 p hg
    simpa only [d294990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d294990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34325 (p : Pattern) (guard : d294991 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294990 p = 1 := by simpa only [d294991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34324 p hg
    simpa only [d294991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d294991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34326 (p : Pattern) (guard : d294992 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d294991 p = 1 := by simpa only [d294992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34325 p hg
    simpa only [d294992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d294992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34327 (p : Pattern) (guard : d295006 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294988 p = 1 := by simpa only [d295006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34322 p hg
    simpa only [d295006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d295006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34328 (p : Pattern) (guard : d295007 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295006 p = 1 := by simpa only [d295007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34327 p hg
    simpa only [d295007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d295007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34329 (p : Pattern) (guard : d295008 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295007 p = 1 := by simpa only [d295008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34328 p hg
    simpa only [d295008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d295008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34330 (p : Pattern) (guard : d295009 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295008 p = 1 := by simpa only [d295009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34329 p hg
    simpa only [d295009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d295009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34331 (p : Pattern) (guard : d295712 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294992 p = 1 := by simpa only [d295712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34326 p hg
    simpa only [d295712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295009 p = 1 := by simpa only [d295712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34330 p hg
    simpa only [d295712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34332 (p : Pattern) (guard : d295713 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d295713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295712 p = 1 := by simpa only [d295713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34331 p hg
    simpa only [d295713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34333 (p : Pattern) (guard : d295714 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295713 p = 1 := by simpa only [d295714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34332 p hg
    simpa only [d295714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d295714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34334 (p : Pattern) (guard : d295715 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d295715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295714 p = 1 := by simpa only [d295715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34333 p hg
    simpa only [d295715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34335 (p : Pattern) (guard : d295716 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d295716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295715 p = 1 := by simpa only [d295716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34334 p hg
    simpa only [d295716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34336 (p : Pattern) (guard : d295717 p = 1) : d50042 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295717, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d295717, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295716 p = 1 := by simpa only [d295717, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34335 p hg
    simpa only [d295717, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34337 (p : Pattern) (guard : d295718 p = 1) : d50042 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34010 p hg
    simpa only [d295718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295717 p = 1 := by simpa only [d295718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34336 p hg
    simpa only [d295718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34338 (p : Pattern) (guard : d295719 p = 1) : d50042 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 69 with
  | false =>
    have hg : d295718 p = 1 := by simpa only [d295719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34337 p hg
    simpa only [d295719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34010 p hg
    simpa only [d295719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34339 (p : Pattern) (guard : d295720 p = 1) : d50042 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 51 with
  | false =>
    have hg : d295719 p = 1 := by simpa only [d295720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34338 p hg
    simpa only [d295720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34010 p hg
    simpa only [d295720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34340 (p : Pattern) (guard : d295721 p = 1) : d50042 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 50 with
  | false =>
    have hg : d295720 p = 1 := by simpa only [d295721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34339 p hg
    simpa only [d295721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34010 p hg
    simpa only [d295721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34341 (p : Pattern) (guard : d295722 p = 1) : d50100 p ≤ (0 : Int) + d47865 p := by
  cases selected : p 49 with
  | false =>
    have hg : d295721 p = 1 := by simpa only [d295722, d50100, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34340 p hg
    simpa only [d295722, d50100, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295722, d50100, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34102 p hg
    simpa only [d295722, d50100, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34342 (p : Pattern) (guard : d295723 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d295711 p = 1 := by simpa only [d295723, d50101, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34264 p hg
    simpa only [d295723, d50101, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295722 p = 1 := by simpa only [d295723, d50101, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34341 p hg
    simpa only [d295723, d50101, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34343 (p : Pattern) (guard : d295724 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295723 p = 1 := by simpa only [d295724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34342 p hg
    simpa only [d295724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34344 (p : Pattern) (guard : d295725 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295724 p = 1 := by simpa only [d295725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34343 p hg
    simpa only [d295725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34345 (p : Pattern) (guard : d295726 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295725 p = 1 := by simpa only [d295726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d295726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34346 (p : Pattern) (guard : d295727 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295726 p = 1 := by simpa only [d295727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34345 p hg
    simpa only [d295727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34347 (p : Pattern) (guard : d295728 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295727 p = 1 := by simpa only [d295728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34346 p hg
    simpa only [d295728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34348 (p : Pattern) (guard : d295729 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295728 p = 1 := by simpa only [d295729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34347 p hg
    simpa only [d295729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34349 (p : Pattern) (guard : d295730 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295729 p = 1 := by simpa only [d295730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34348 p hg
    simpa only [d295730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34350 (p : Pattern) (guard : d295731 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295730 p = 1 := by simpa only [d295731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34349 p hg
    simpa only [d295731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34351 (p : Pattern) (guard : d295732 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d295703 p = 1 := by simpa only [d295732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34112 p hg
    simpa only [d295732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295731 p = 1 := by simpa only [d295732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34350 p hg
    simpa only [d295732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34352 (p : Pattern) (guard : d1532 p = 1) : d47617 p ≤ (0 : Int) + d47617 p := by
  omega
theorem compare34353 (p : Pattern) (guard : d25764 p = 1) : d49795 p ≤ (0 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1532 p = 1 := by simpa only [d25764, d49795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34352 p hg
    simpa only [d25764, d49795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25764, d49795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33833 p hg
    simpa only [d25764, d49795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34354 (p : Pattern) (guard : d25765 p = 1) : d49795 p ≤ (0 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d25764 p = 1 := by simpa only [d25765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34353 p hg
    simpa only [d25765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33831 p hg
    simpa only [d25765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34355 (p : Pattern) (guard : d25766 p = 1) : d49795 p ≤ (0 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d25765 p = 1 := by simpa only [d25766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34354 p hg
    simpa only [d25766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33831 p hg
    simpa only [d25766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34356 (p : Pattern) (guard : d31739 p = 1) : d49795 p ≤ (0 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d31739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33831 p hg
    simpa only [d31739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d25766 p = 1 := by simpa only [d31739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34355 p hg
    simpa only [d31739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34357 (p : Pattern) (guard : d294870 p = 1) : d49795 p ≤ (0 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33831 p hg
    simpa only [d294870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d31739 p = 1 := by simpa only [d294870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34356 p hg
    simpa only [d294870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34358 (p : Pattern) (guard : d294871 p = 1) : d49797 p ≤ (0 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d294870 p = 1 := by simpa only [d294871, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34357 p hg
    simpa only [d294871, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294871, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33839 p hg
    simpa only [d294871, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34359 (p : Pattern) (guard : d294872 p = 1) : d49797 p ≤ (0 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d294871 p = 1 := by simpa only [d294872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34358 p hg
    simpa only [d294872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33841 p hg
    simpa only [d294872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34360 (p : Pattern) (guard : d294873 p = 1) : d49838 p ≤ (0 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d294872 p = 1 := by simpa only [d294873, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34359 p hg
    simpa only [d294873, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294873, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33843 p hg
    simpa only [d294873, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34361 (p : Pattern) (guard : d294874 p = 1) : d49841 p ≤ (0 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d294873 p = 1 := by simpa only [d294874, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34360 p hg
    simpa only [d294874, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294874, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33845 p hg
    simpa only [d294874, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34362 (p : Pattern) (guard : d294875 p = 1) : d49864 p ≤ (0 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294875, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33830 p hg
    simpa only [d294875, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294874 p = 1 := by simpa only [d294875, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34361 p hg
    simpa only [d294875, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34363 (p : Pattern) (guard : d294876 p = 1) : d49868 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d294875 p = 1 := by simpa only [d294876, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34362 p hg
    simpa only [d294876, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294876, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33848 p hg
    simpa only [d294876, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34364 (p : Pattern) (guard : d294877 p = 1) : d49868 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33829 p hg
    simpa only [d294877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294876 p = 1 := by simpa only [d294877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34363 p hg
    simpa only [d294877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34365 (p : Pattern) (guard : d293903 p = 1) : d49795 p ≤ (0 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d31739 p = 1 := by simpa only [d293903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34356 p hg
    simpa only [d293903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33831 p hg
    simpa only [d293903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34366 (p : Pattern) (guard : d293904 p = 1) : d49797 p ≤ (0 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d293903 p = 1 := by simpa only [d293904, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34365 p hg
    simpa only [d293904, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293904, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33839 p hg
    simpa only [d293904, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34367 (p : Pattern) (guard : d293905 p = 1) : d49797 p ≤ (0 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d293904 p = 1 := by simpa only [d293905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34366 p hg
    simpa only [d293905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33841 p hg
    simpa only [d293905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34368 (p : Pattern) (guard : d293906 p = 1) : d49838 p ≤ (0 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d293905 p = 1 := by simpa only [d293906, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d293906, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293906, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33843 p hg
    simpa only [d293906, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34369 (p : Pattern) (guard : d293907 p = 1) : d49841 p ≤ (0 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d293906 p = 1 := by simpa only [d293907, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34368 p hg
    simpa only [d293907, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293907, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33845 p hg
    simpa only [d293907, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34370 (p : Pattern) (guard : d293908 p = 1) : d49864 p ≤ (0 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d293908, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33830 p hg
    simpa only [d293908, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d293907 p = 1 := by simpa only [d293908, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34369 p hg
    simpa only [d293908, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34371 (p : Pattern) (guard : d293909 p = 1) : d49868 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d293908 p = 1 := by simpa only [d293909, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34370 p hg
    simpa only [d293909, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293909, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33848 p hg
    simpa only [d293909, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34372 (p : Pattern) (guard : d295031 p = 1) : d49868 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33829 p hg
    simpa only [d295031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d293909 p = 1 := by simpa only [d295031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34371 p hg
    simpa only [d295031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34373 (p : Pattern) (guard : d295032 p = 1) : d49868 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294877 p = 1 := by simpa only [d295032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34364 p hg
    simpa only [d295032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295031 p = 1 := by simpa only [d295032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34372 p hg
    simpa only [d295032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34374 (p : Pattern) (guard : d293921 p = 1) : d49868 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d293909 p = 1 := by simpa only [d293921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34371 p hg
    simpa only [d293921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33829 p hg
    simpa only [d293921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34375 (p : Pattern) (guard : d295033 p = 1) : d49868 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d295031 p = 1 := by simpa only [d295033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34372 p hg
    simpa only [d295033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d293921 p = 1 := by simpa only [d295033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34374 p hg
    simpa only [d295033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34376 (p : Pattern) (guard : d295034 p = 1) : d49868 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d295032 p = 1 := by simpa only [d295034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34373 p hg
    simpa only [d295034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295033 p = 1 := by simpa only [d295034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34375 p hg
    simpa only [d295034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34377 (p : Pattern) (guard : d295035 p = 1) : d49869 p ≤ (0 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295035, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33828 p hg
    simpa only [d295035, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295034 p = 1 := by simpa only [d295035, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34376 p hg
    simpa only [d295035, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34378 (p : Pattern) (guard : d295036 p = 1) : d49913 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295036, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33827 p hg
    simpa only [d295036, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295035 p = 1 := by simpa only [d295036, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34377 p hg
    simpa only [d295036, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34379 (p : Pattern) (guard : d295037 p = 1) : d49868 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d293921 p = 1 := by simpa only [d295037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34374 p hg
    simpa only [d295037, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33829 p hg
    simpa only [d295037, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34380 (p : Pattern) (guard : d295038 p = 1) : d49868 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d295033 p = 1 := by simpa only [d295038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34375 p hg
    simpa only [d295038, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295037 p = 1 := by simpa only [d295038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34379 p hg
    simpa only [d295038, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34381 (p : Pattern) (guard : d295039 p = 1) : d49869 p ≤ (0 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295039, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33828 p hg
    simpa only [d295039, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295038 p = 1 := by simpa only [d295039, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34380 p hg
    simpa only [d295039, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34382 (p : Pattern) (guard : d295040 p = 1) : d49913 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295040, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33827 p hg
    simpa only [d295040, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295039 p = 1 := by simpa only [d295040, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34381 p hg
    simpa only [d295040, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34383 (p : Pattern) (guard : d295041 p = 1) : d49913 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d295036 p = 1 := by simpa only [d295041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34378 p hg
    simpa only [d295041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295040 p = 1 := by simpa only [d295041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34382 p hg
    simpa only [d295041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34384 (p : Pattern) (guard : d295042 p = 1) : d49913 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d295040 p = 1 := by simpa only [d295042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34382 p hg
    simpa only [d295042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33870 p hg
    simpa only [d295042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34385 (p : Pattern) (guard : d295043 p = 1) : d49913 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d295041 p = 1 := by simpa only [d295043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34383 p hg
    simpa only [d295043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295042 p = 1 := by simpa only [d295043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34384 p hg
    simpa only [d295043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34386 (p : Pattern) (guard : d295044 p = 1) : d49913 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d295043 p = 1 := by simpa only [d295044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34385 p hg
    simpa only [d295044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33870 p hg
    simpa only [d295044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34387 (p : Pattern) (guard : d295045 p = 1) : d49914 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d295044 p = 1 := by simpa only [d295045, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34386 p hg
    simpa only [d295045, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295045, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33874 p hg
    simpa only [d295045, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34388 (p : Pattern) (guard : d295046 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295046, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33826 p hg
    simpa only [d295046, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295045 p = 1 := by simpa only [d295046, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34387 p hg
    simpa only [d295046, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34389 (p : Pattern) (guard : d295047 p = 1) : d49913 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d295042 p = 1 := by simpa only [d295047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34384 p hg
    simpa only [d295047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33870 p hg
    simpa only [d295047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34390 (p : Pattern) (guard : d295048 p = 1) : d49913 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d295047 p = 1 := by simpa only [d295048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34389 p hg
    simpa only [d295048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33870 p hg
    simpa only [d295048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34391 (p : Pattern) (guard : d295049 p = 1) : d49914 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d295048 p = 1 := by simpa only [d295049, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34390 p hg
    simpa only [d295049, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295049, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33874 p hg
    simpa only [d295049, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34392 (p : Pattern) (guard : d295050 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295050, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33826 p hg
    simpa only [d295050, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295049 p = 1 := by simpa only [d295050, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34391 p hg
    simpa only [d295050, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34393 (p : Pattern) (guard : d295051 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295046 p = 1 := by simpa only [d295051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34388 p hg
    simpa only [d295051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295050 p = 1 := by simpa only [d295051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34392 p hg
    simpa only [d295051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34394 (p : Pattern) (guard : d295052 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295051 p = 1 := by simpa only [d295052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34393 p hg
    simpa only [d295052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d295052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34395 (p : Pattern) (guard : d295053 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295052 p = 1 := by simpa only [d295053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34394 p hg
    simpa only [d295053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d295053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34396 (p : Pattern) (guard : d295054 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d295054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295053 p = 1 := by simpa only [d295054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34395 p hg
    simpa only [d295054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34397 (p : Pattern) (guard : d295055 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295050 p = 1 := by simpa only [d295055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34392 p hg
    simpa only [d295055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d295055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34398 (p : Pattern) (guard : d295056 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295055 p = 1 := by simpa only [d295056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34397 p hg
    simpa only [d295056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d295056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34399 (p : Pattern) (guard : d295057 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295056 p = 1 := by simpa only [d295057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34398 p hg
    simpa only [d295057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d295057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34400 (p : Pattern) (guard : d295058 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d295058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295057 p = 1 := by simpa only [d295058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34399 p hg
    simpa only [d295058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34401 (p : Pattern) (guard : d295059 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295054 p = 1 := by simpa only [d295059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34396 p hg
    simpa only [d295059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295058 p = 1 := by simpa only [d295059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34400 p hg
    simpa only [d295059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34402 (p : Pattern) (guard : d295060 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d295060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295059 p = 1 := by simpa only [d295060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34401 p hg
    simpa only [d295060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34403 (p : Pattern) (guard : d295061 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295060 p = 1 := by simpa only [d295061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34402 p hg
    simpa only [d295061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d295061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34404 (p : Pattern) (guard : d295062 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d295062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295061 p = 1 := by simpa only [d295062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34403 p hg
    simpa only [d295062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34405 (p : Pattern) (guard : d295063 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d295063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295062 p = 1 := by simpa only [d295063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34404 p hg
    simpa only [d295063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34406 (p : Pattern) (guard : d295064 p = 1) : d49916 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295064, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d295064, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295063 p = 1 := by simpa only [d295064, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34405 p hg
    simpa only [d295064, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34407 (p : Pattern) (guard : d295036 p = 1) : d49892 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295036, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33896 p hg
    simpa only [d295036, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295035 p = 1 := by simpa only [d295036, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34377 p hg
    simpa only [d295036, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34408 (p : Pattern) (guard : d295040 p = 1) : d49892 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295040, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33896 p hg
    simpa only [d295040, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295039 p = 1 := by simpa only [d295040, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34381 p hg
    simpa only [d295040, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34409 (p : Pattern) (guard : d295041 p = 1) : d49892 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d295036 p = 1 := by simpa only [d295041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34407 p hg
    simpa only [d295041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295040 p = 1 := by simpa only [d295041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34408 p hg
    simpa only [d295041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34410 (p : Pattern) (guard : d295042 p = 1) : d49892 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d295040 p = 1 := by simpa only [d295042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34408 p hg
    simpa only [d295042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33900 p hg
    simpa only [d295042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34411 (p : Pattern) (guard : d295043 p = 1) : d49892 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d295041 p = 1 := by simpa only [d295043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34409 p hg
    simpa only [d295043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295042 p = 1 := by simpa only [d295043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34410 p hg
    simpa only [d295043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34412 (p : Pattern) (guard : d295044 p = 1) : d49892 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d295043 p = 1 := by simpa only [d295044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34411 p hg
    simpa only [d295044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33900 p hg
    simpa only [d295044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34413 (p : Pattern) (guard : d295045 p = 1) : d49894 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d295044 p = 1 := by simpa only [d295045, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34412 p hg
    simpa only [d295045, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295045, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33874 p hg
    simpa only [d295045, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34414 (p : Pattern) (guard : d295046 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295046, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33895 p hg
    simpa only [d295046, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295045 p = 1 := by simpa only [d295046, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34413 p hg
    simpa only [d295046, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34415 (p : Pattern) (guard : d295047 p = 1) : d49892 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d295042 p = 1 := by simpa only [d295047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34410 p hg
    simpa only [d295047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33900 p hg
    simpa only [d295047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34416 (p : Pattern) (guard : d295048 p = 1) : d49892 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d295047 p = 1 := by simpa only [d295048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34415 p hg
    simpa only [d295048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33900 p hg
    simpa only [d295048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34417 (p : Pattern) (guard : d295049 p = 1) : d49894 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d295048 p = 1 := by simpa only [d295049, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34416 p hg
    simpa only [d295049, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295049, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33874 p hg
    simpa only [d295049, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34418 (p : Pattern) (guard : d295050 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295050, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33895 p hg
    simpa only [d295050, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295049 p = 1 := by simpa only [d295050, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34417 p hg
    simpa only [d295050, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34419 (p : Pattern) (guard : d295051 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295046 p = 1 := by simpa only [d295051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34414 p hg
    simpa only [d295051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295050 p = 1 := by simpa only [d295051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34418 p hg
    simpa only [d295051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34420 (p : Pattern) (guard : d295052 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295051 p = 1 := by simpa only [d295052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34419 p hg
    simpa only [d295052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d295052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34421 (p : Pattern) (guard : d295053 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295052 p = 1 := by simpa only [d295053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34420 p hg
    simpa only [d295053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d295053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34422 (p : Pattern) (guard : d295054 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d295054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295053 p = 1 := by simpa only [d295054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34421 p hg
    simpa only [d295054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34423 (p : Pattern) (guard : d295055 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295050 p = 1 := by simpa only [d295055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34418 p hg
    simpa only [d295055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d295055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34424 (p : Pattern) (guard : d295056 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295055 p = 1 := by simpa only [d295056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34423 p hg
    simpa only [d295056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d295056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34425 (p : Pattern) (guard : d295057 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295056 p = 1 := by simpa only [d295057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34424 p hg
    simpa only [d295057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d295057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34426 (p : Pattern) (guard : d295058 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d295058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295057 p = 1 := by simpa only [d295058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34425 p hg
    simpa only [d295058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34427 (p : Pattern) (guard : d295059 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295054 p = 1 := by simpa only [d295059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34422 p hg
    simpa only [d295059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295058 p = 1 := by simpa only [d295059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34426 p hg
    simpa only [d295059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34428 (p : Pattern) (guard : d295060 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d295060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295059 p = 1 := by simpa only [d295060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34427 p hg
    simpa only [d295060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34429 (p : Pattern) (guard : d295061 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295060 p = 1 := by simpa only [d295061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34428 p hg
    simpa only [d295061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d295061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34430 (p : Pattern) (guard : d295062 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d295062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295061 p = 1 := by simpa only [d295062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34429 p hg
    simpa only [d295062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34431 (p : Pattern) (guard : d295063 p = 1) : d49895 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d295063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295062 p = 1 := by simpa only [d295063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34430 p hg
    simpa only [d295063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34432 (p : Pattern) (guard : d295067 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295053 p = 1 := by simpa only [d295067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34395 p hg
    simpa only [d295067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d295067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34433 (p : Pattern) (guard : d295068 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295057 p = 1 := by simpa only [d295068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34399 p hg
    simpa only [d295068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d295068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34434 (p : Pattern) (guard : d295069 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295067 p = 1 := by simpa only [d295069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34432 p hg
    simpa only [d295069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295068 p = 1 := by simpa only [d295069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34433 p hg
    simpa only [d295069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34435 (p : Pattern) (guard : d295070 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d295070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295069 p = 1 := by simpa only [d295070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34434 p hg
    simpa only [d295070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34436 (p : Pattern) (guard : d295071 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295070 p = 1 := by simpa only [d295071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34435 p hg
    simpa only [d295071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d295071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34437 (p : Pattern) (guard : d295072 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d295072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295071 p = 1 := by simpa only [d295072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34436 p hg
    simpa only [d295072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34438 (p : Pattern) (guard : d295073 p = 1) : d49915 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33825 p hg
    simpa only [d295073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295072 p = 1 := by simpa only [d295073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34437 p hg
    simpa only [d295073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34439 (p : Pattern) (guard : d295074 p = 1) : d49916 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d295063 p = 1 := by simpa only [d295074, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34431 p hg
    simpa only [d295074, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295073 p = 1 := by simpa only [d295074, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34438 p hg
    simpa only [d295074, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34440 (p : Pattern) (guard : d295075 p = 1) : d49916 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d295064 p = 1 := by simpa only [d295075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34406 p hg
    simpa only [d295075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295074 p = 1 := by simpa only [d295075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34439 p hg
    simpa only [d295075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34441 (p : Pattern) (guard : d295076 p = 1) : d49916 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d295075 p = 1 := by simpa only [d295076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34440 p hg
    simpa only [d295076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33823 p hg
    simpa only [d295076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34442 (p : Pattern) (guard : d295733 p = 1) : d49916 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d295076 p = 1 := by simpa only [d295733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34441 p hg
    simpa only [d295733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33823 p hg
    simpa only [d295733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34443 (p : Pattern) (guard : d295734 p = 1) : d49916 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33823 p hg
    simpa only [d295734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295733 p = 1 := by simpa only [d295734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34442 p hg
    simpa only [d295734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34444 (p : Pattern) (guard : d1532 p = 1) : d47706 p ≤ (0 : Int) + d47706 p := by
  omega
theorem compare34445 (p : Pattern) (guard : d25764 p = 1) : d49927 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1532 p = 1 := by simpa only [d25764, d49927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34444 p hg
    simpa only [d25764, d49927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25764, d49927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33944 p hg
    simpa only [d25764, d49927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34446 (p : Pattern) (guard : d25765 p = 1) : d49927 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d25764 p = 1 := by simpa only [d25765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34445 p hg
    simpa only [d25765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33942 p hg
    simpa only [d25765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34447 (p : Pattern) (guard : d25766 p = 1) : d49927 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d25765 p = 1 := by simpa only [d25766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34446 p hg
    simpa only [d25766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33942 p hg
    simpa only [d25766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34448 (p : Pattern) (guard : d31739 p = 1) : d49927 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d31739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33942 p hg
    simpa only [d31739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d25766 p = 1 := by simpa only [d31739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34447 p hg
    simpa only [d31739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34449 (p : Pattern) (guard : d294870 p = 1) : d49927 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33942 p hg
    simpa only [d294870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d31739 p = 1 := by simpa only [d294870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34448 p hg
    simpa only [d294870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34450 (p : Pattern) (guard : d294871 p = 1) : d49929 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d294870 p = 1 := by simpa only [d294871, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34449 p hg
    simpa only [d294871, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294871, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33950 p hg
    simpa only [d294871, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34451 (p : Pattern) (guard : d294872 p = 1) : d49929 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d294871 p = 1 := by simpa only [d294872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34450 p hg
    simpa only [d294872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33952 p hg
    simpa only [d294872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34452 (p : Pattern) (guard : d294873 p = 1) : d49957 p ≤ (0 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d294872 p = 1 := by simpa only [d294873, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34451 p hg
    simpa only [d294873, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294873, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33954 p hg
    simpa only [d294873, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34453 (p : Pattern) (guard : d294874 p = 1) : d49958 p ≤ (0 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d294873 p = 1 := by simpa only [d294874, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34452 p hg
    simpa only [d294874, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294874, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d294874, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34454 (p : Pattern) (guard : d294875 p = 1) : d49978 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294875, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33941 p hg
    simpa only [d294875, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294874 p = 1 := by simpa only [d294875, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34453 p hg
    simpa only [d294875, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34455 (p : Pattern) (guard : d294876 p = 1) : d49982 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d294875 p = 1 := by simpa only [d294876, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34454 p hg
    simpa only [d294876, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294876, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33958 p hg
    simpa only [d294876, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34456 (p : Pattern) (guard : d294877 p = 1) : d49982 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33940 p hg
    simpa only [d294877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294876 p = 1 := by simpa only [d294877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d294877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34457 (p : Pattern) (guard : d293903 p = 1) : d49927 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d31739 p = 1 := by simpa only [d293903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34448 p hg
    simpa only [d293903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33942 p hg
    simpa only [d293903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34458 (p : Pattern) (guard : d293904 p = 1) : d49929 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d293903 p = 1 := by simpa only [d293904, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34457 p hg
    simpa only [d293904, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293904, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33950 p hg
    simpa only [d293904, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34459 (p : Pattern) (guard : d293905 p = 1) : d49929 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d293904 p = 1 := by simpa only [d293905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34458 p hg
    simpa only [d293905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33952 p hg
    simpa only [d293905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34460 (p : Pattern) (guard : d293906 p = 1) : d49957 p ≤ (0 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d293905 p = 1 := by simpa only [d293906, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34459 p hg
    simpa only [d293906, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293906, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33954 p hg
    simpa only [d293906, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34461 (p : Pattern) (guard : d293907 p = 1) : d49958 p ≤ (0 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d293906 p = 1 := by simpa only [d293907, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34460 p hg
    simpa only [d293907, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293907, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d293907, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34462 (p : Pattern) (guard : d293908 p = 1) : d49978 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d293908, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33941 p hg
    simpa only [d293908, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d293907 p = 1 := by simpa only [d293908, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34461 p hg
    simpa only [d293908, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34463 (p : Pattern) (guard : d293909 p = 1) : d49982 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d293908 p = 1 := by simpa only [d293909, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34462 p hg
    simpa only [d293909, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293909, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33958 p hg
    simpa only [d293909, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34464 (p : Pattern) (guard : d295031 p = 1) : d49982 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33940 p hg
    simpa only [d295031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d293909 p = 1 := by simpa only [d295031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34463 p hg
    simpa only [d295031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34465 (p : Pattern) (guard : d295032 p = 1) : d49982 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294877 p = 1 := by simpa only [d295032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34456 p hg
    simpa only [d295032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295031 p = 1 := by simpa only [d295032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34464 p hg
    simpa only [d295032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34466 (p : Pattern) (guard : d293921 p = 1) : d49982 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d293909 p = 1 := by simpa only [d293921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34463 p hg
    simpa only [d293921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33940 p hg
    simpa only [d293921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34467 (p : Pattern) (guard : d295033 p = 1) : d49982 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d295031 p = 1 := by simpa only [d295033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34464 p hg
    simpa only [d295033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d293921 p = 1 := by simpa only [d295033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34466 p hg
    simpa only [d295033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34468 (p : Pattern) (guard : d295034 p = 1) : d49982 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d295032 p = 1 := by simpa only [d295034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34465 p hg
    simpa only [d295034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295033 p = 1 := by simpa only [d295034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34467 p hg
    simpa only [d295034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34469 (p : Pattern) (guard : d295035 p = 1) : d49983 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295035, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33939 p hg
    simpa only [d295035, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295034 p = 1 := by simpa only [d295035, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34468 p hg
    simpa only [d295035, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34470 (p : Pattern) (guard : d295036 p = 1) : d49997 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295036, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33938 p hg
    simpa only [d295036, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295035 p = 1 := by simpa only [d295036, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34469 p hg
    simpa only [d295036, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34471 (p : Pattern) (guard : d295037 p = 1) : d49982 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d293921 p = 1 := by simpa only [d295037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34466 p hg
    simpa only [d295037, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33940 p hg
    simpa only [d295037, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34472 (p : Pattern) (guard : d295038 p = 1) : d49982 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d295033 p = 1 := by simpa only [d295038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34467 p hg
    simpa only [d295038, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295037 p = 1 := by simpa only [d295038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34471 p hg
    simpa only [d295038, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34473 (p : Pattern) (guard : d295039 p = 1) : d49983 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295039, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33939 p hg
    simpa only [d295039, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295038 p = 1 := by simpa only [d295039, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34472 p hg
    simpa only [d295039, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34474 (p : Pattern) (guard : d295040 p = 1) : d49997 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295040, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33938 p hg
    simpa only [d295040, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295039 p = 1 := by simpa only [d295040, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34473 p hg
    simpa only [d295040, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34475 (p : Pattern) (guard : d295041 p = 1) : d49997 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d295036 p = 1 := by simpa only [d295041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34470 p hg
    simpa only [d295041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295040 p = 1 := by simpa only [d295041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34474 p hg
    simpa only [d295041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34476 (p : Pattern) (guard : d295042 p = 1) : d49997 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d295040 p = 1 := by simpa only [d295042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34474 p hg
    simpa only [d295042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33980 p hg
    simpa only [d295042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34477 (p : Pattern) (guard : d295043 p = 1) : d49997 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d295041 p = 1 := by simpa only [d295043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34475 p hg
    simpa only [d295043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295042 p = 1 := by simpa only [d295043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34476 p hg
    simpa only [d295043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34478 (p : Pattern) (guard : d295044 p = 1) : d49997 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d295043 p = 1 := by simpa only [d295044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34477 p hg
    simpa only [d295044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33980 p hg
    simpa only [d295044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34479 (p : Pattern) (guard : d295045 p = 1) : d49999 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d295044 p = 1 := by simpa only [d295045, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34478 p hg
    simpa only [d295045, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295045, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33984 p hg
    simpa only [d295045, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34480 (p : Pattern) (guard : d295046 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295046, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33937 p hg
    simpa only [d295046, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295045 p = 1 := by simpa only [d295046, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34479 p hg
    simpa only [d295046, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34481 (p : Pattern) (guard : d295047 p = 1) : d49997 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d295042 p = 1 := by simpa only [d295047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34476 p hg
    simpa only [d295047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33980 p hg
    simpa only [d295047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34482 (p : Pattern) (guard : d295048 p = 1) : d49997 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d295047 p = 1 := by simpa only [d295048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34481 p hg
    simpa only [d295048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33980 p hg
    simpa only [d295048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34483 (p : Pattern) (guard : d295049 p = 1) : d49999 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d295048 p = 1 := by simpa only [d295049, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34482 p hg
    simpa only [d295049, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295049, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33984 p hg
    simpa only [d295049, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34484 (p : Pattern) (guard : d295050 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295050, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33937 p hg
    simpa only [d295050, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295049 p = 1 := by simpa only [d295050, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34483 p hg
    simpa only [d295050, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34485 (p : Pattern) (guard : d295051 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295046 p = 1 := by simpa only [d295051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34480 p hg
    simpa only [d295051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295050 p = 1 := by simpa only [d295051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34484 p hg
    simpa only [d295051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34486 (p : Pattern) (guard : d295052 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295051 p = 1 := by simpa only [d295052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34485 p hg
    simpa only [d295052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d295052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34487 (p : Pattern) (guard : d295053 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295052 p = 1 := by simpa only [d295053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34486 p hg
    simpa only [d295053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d295053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34488 (p : Pattern) (guard : d295067 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295053 p = 1 := by simpa only [d295067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34487 p hg
    simpa only [d295067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d295067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34489 (p : Pattern) (guard : d295055 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295050 p = 1 := by simpa only [d295055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34484 p hg
    simpa only [d295055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d295055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34490 (p : Pattern) (guard : d295056 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295055 p = 1 := by simpa only [d295056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34489 p hg
    simpa only [d295056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d295056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34491 (p : Pattern) (guard : d295057 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295056 p = 1 := by simpa only [d295057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34490 p hg
    simpa only [d295057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d295057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34492 (p : Pattern) (guard : d295068 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295057 p = 1 := by simpa only [d295068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34491 p hg
    simpa only [d295068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d295068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34493 (p : Pattern) (guard : d295069 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295067 p = 1 := by simpa only [d295069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d295069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295068 p = 1 := by simpa only [d295069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34492 p hg
    simpa only [d295069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34494 (p : Pattern) (guard : d295070 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d295070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295069 p = 1 := by simpa only [d295070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34493 p hg
    simpa only [d295070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34495 (p : Pattern) (guard : d295071 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295070 p = 1 := by simpa only [d295071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34494 p hg
    simpa only [d295071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d295071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34496 (p : Pattern) (guard : d295072 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d295072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295071 p = 1 := by simpa only [d295072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34495 p hg
    simpa only [d295072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34497 (p : Pattern) (guard : d295073 p = 1) : d50000 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33936 p hg
    simpa only [d295073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295072 p = 1 := by simpa only [d295073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34496 p hg
    simpa only [d295073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34498 (p : Pattern) (guard : d295735 p = 1) : d50001 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295735, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d295735, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295073 p = 1 := by simpa only [d295735, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34497 p hg
    simpa only [d295735, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34499 (p : Pattern) (guard : d295736 p = 1) : d50001 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33935 p hg
    simpa only [d295736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295735 p = 1 := by simpa only [d295736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34498 p hg
    simpa only [d295736, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
