import NetHack.Soko22Hazard87.Compare152
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare38250 (p : Pattern) (guard : d286110 p = 1) : d50248 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d286105 p = 1 := by simpa only [d286110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38245 p hg
    simpa only [d286110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37872 p hg
    simpa only [d286110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38251 (p : Pattern) (guard : d286111 p = 1) : d50248 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d286110 p = 1 := by simpa only [d286111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38250 p hg
    simpa only [d286111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37872 p hg
    simpa only [d286111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38252 (p : Pattern) (guard : d286112 p = 1) : d50250 p ≤ (2 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d286111 p = 1 := by simpa only [d286112, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38251 p hg
    simpa only [d286112, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286112, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37856 p hg
    simpa only [d286112, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38253 (p : Pattern) (guard : d286113 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286113, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37869 p hg
    simpa only [d286113, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286112 p = 1 := by simpa only [d286113, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38252 p hg
    simpa only [d286113, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38254 (p : Pattern) (guard : d316319 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d316318 p = 1 := by simpa only [d316319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38249 p hg
    simpa only [d316319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286113 p = 1 := by simpa only [d316319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38253 p hg
    simpa only [d316319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38255 (p : Pattern) (guard : d316320 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d316319 p = 1 := by simpa only [d316320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38254 p hg
    simpa only [d316320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d316320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38256 (p : Pattern) (guard : d316321 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d316320 p = 1 := by simpa only [d316321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38255 p hg
    simpa only [d316321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d316321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38257 (p : Pattern) (guard : d316322 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d316322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316321 p = 1 := by simpa only [d316322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38256 p hg
    simpa only [d316322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38258 (p : Pattern) (guard : d286118 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d286113 p = 1 := by simpa only [d286118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38253 p hg
    simpa only [d286118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d286118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38259 (p : Pattern) (guard : d286119 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d286118 p = 1 := by simpa only [d286119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38258 p hg
    simpa only [d286119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d286119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38260 (p : Pattern) (guard : d286120 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d286119 p = 1 := by simpa only [d286120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38259 p hg
    simpa only [d286120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d286120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38261 (p : Pattern) (guard : d286121 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d286121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286120 p = 1 := by simpa only [d286121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38260 p hg
    simpa only [d286121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38262 (p : Pattern) (guard : d316323 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d316322 p = 1 := by simpa only [d316323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38257 p hg
    simpa only [d316323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286121 p = 1 := by simpa only [d316323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38261 p hg
    simpa only [d316323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38263 (p : Pattern) (guard : d316324 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d316324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316323 p = 1 := by simpa only [d316324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38262 p hg
    simpa only [d316324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38264 (p : Pattern) (guard : d316325 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d316324 p = 1 := by simpa only [d316325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38263 p hg
    simpa only [d316325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d316325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38265 (p : Pattern) (guard : d316326 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d316326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316325 p = 1 := by simpa only [d316326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38264 p hg
    simpa only [d316326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38266 (p : Pattern) (guard : d316327 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d316327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316326 p = 1 := by simpa only [d316327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38265 p hg
    simpa only [d316327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38267 (p : Pattern) (guard : d316331 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d316321 p = 1 := by simpa only [d316331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38231 p hg
    simpa only [d316331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d316331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38268 (p : Pattern) (guard : d286131 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d286120 p = 1 := by simpa only [d286131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38235 p hg
    simpa only [d286131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d286131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38269 (p : Pattern) (guard : d316332 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d316331 p = 1 := by simpa only [d316332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38267 p hg
    simpa only [d316332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286131 p = 1 := by simpa only [d316332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38268 p hg
    simpa only [d316332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38270 (p : Pattern) (guard : d316333 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d316333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316332 p = 1 := by simpa only [d316333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38269 p hg
    simpa only [d316333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38271 (p : Pattern) (guard : d316334 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d316333 p = 1 := by simpa only [d316334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38270 p hg
    simpa only [d316334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d316334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38272 (p : Pattern) (guard : d316335 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d316335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316334 p = 1 := by simpa only [d316335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38271 p hg
    simpa only [d316335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38273 (p : Pattern) (guard : d316336 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d316336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316335 p = 1 := by simpa only [d316336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38272 p hg
    simpa only [d316336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38274 (p : Pattern) (guard : d316337 p = 1) : d50274 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d316327 p = 1 := by simpa only [d316337, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38266 p hg
    simpa only [d316337, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316336 p = 1 := by simpa only [d316337, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38273 p hg
    simpa only [d316337, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38275 (p : Pattern) (guard : d316338 p = 1) : d50274 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d316328 p = 1 := by simpa only [d316338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38242 p hg
    simpa only [d316338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316337 p = 1 := by simpa only [d316338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38274 p hg
    simpa only [d316338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38276 (p : Pattern) (guard : d316339 p = 1) : d50274 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d316338 p = 1 := by simpa only [d316339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38275 p hg
    simpa only [d316339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37817 p hg
    simpa only [d316339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38277 (p : Pattern) (guard : d318228 p = 1) : d50274 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d316339 p = 1 := by simpa only [d318228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38276 p hg
    simpa only [d318228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37817 p hg
    simpa only [d318228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38278 (p : Pattern) (guard : d318229 p = 1) : d50274 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37817 p hg
    simpa only [d318229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318228 p = 1 := by simpa only [d318229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38277 p hg
    simpa only [d318229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38279 (p : Pattern) (guard : d1520 p = 1) : d47706 p ≤ (2 : Int) + d47706 p := by
  omega
theorem compare38280 (p : Pattern) (guard : d33554 p = 1) : d50288 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1520 p = 1 := by simpa only [d33554, d50288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38279 p hg
    simpa only [d33554, d50288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d33554, d50288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37906 p hg
    simpa only [d33554, d50288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38281 (p : Pattern) (guard : d286611 p = 1) : d50288 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37904 p hg
    simpa only [d286611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d33554 p = 1 := by simpa only [d286611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38280 p hg
    simpa only [d286611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38282 (p : Pattern) (guard : d286612 p = 1) : d50288 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d286611 p = 1 := by simpa only [d286612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38281 p hg
    simpa only [d286612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37904 p hg
    simpa only [d286612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38283 (p : Pattern) (guard : d286613 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d286612 p = 1 := by simpa only [d286613, d50291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38282 p hg
    simpa only [d286613, d50291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286613, d50291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37910 p hg
    simpa only [d286613, d50291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38284 (p : Pattern) (guard : d316227 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d286613 p = 1 := by simpa only [d316227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38283 p hg
    simpa only [d316227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285867 p = 1 := by simpa only [d316227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38095 p hg
    simpa only [d316227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38285 (p : Pattern) (guard : d534 p = 1) : d47706 p ≤ (2 : Int) + d47706 p := by
  omega
theorem compare38286 (p : Pattern) (guard : d33559 p = 1) : d50288 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d534 p = 1 := by simpa only [d33559, d50288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38285 p hg
    simpa only [d33559, d50288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d33559, d50288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37906 p hg
    simpa only [d33559, d50288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38287 (p : Pattern) (guard : d316228 p = 1) : d50288 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37904 p hg
    simpa only [d316228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d33559 p = 1 := by simpa only [d316228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38286 p hg
    simpa only [d316228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38288 (p : Pattern) (guard : d316229 p = 1) : d50288 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d316228 p = 1 := by simpa only [d316229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38287 p hg
    simpa only [d316229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37904 p hg
    simpa only [d316229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38289 (p : Pattern) (guard : d316230 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d316229 p = 1 := by simpa only [d316230, d50291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38288 p hg
    simpa only [d316230, d50291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316230, d50291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37910 p hg
    simpa only [d316230, d50291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38290 (p : Pattern) (guard : d316231 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d316230 p = 1 := by simpa only [d316231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38289 p hg
    simpa only [d316231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257184 p = 1 := by simpa only [d316231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37911 p hg
    simpa only [d316231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38291 (p : Pattern) (guard : d316232 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316227 p = 1 := by simpa only [d316232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38284 p hg
    simpa only [d316232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316231 p = 1 := by simpa only [d316232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38290 p hg
    simpa only [d316232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38292 (p : Pattern) (guard : d316233 p = 1) : d50347 p ≤ (2 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316232 p = 1 := by simpa only [d316233, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38291 p hg
    simpa only [d316233, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316233, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37915 p hg
    simpa only [d316233, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38293 (p : Pattern) (guard : d316234 p = 1) : d50347 p ≤ (2 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316233 p = 1 := by simpa only [d316234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38292 p hg
    simpa only [d316234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285870 p = 1 := by simpa only [d316234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38098 p hg
    simpa only [d316234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38294 (p : Pattern) (guard : d316235 p = 1) : d50362 p ≤ (2 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316234 p = 1 := by simpa only [d316235, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38293 p hg
    simpa only [d316235, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316235, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37919 p hg
    simpa only [d316235, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38295 (p : Pattern) (guard : d316236 p = 1) : d50363 p ≤ (2 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316235 p = 1 := by simpa only [d316236, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38294 p hg
    simpa only [d316236, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316236, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d316236, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38296 (p : Pattern) (guard : d316237 p = 1) : d50364 p ≤ (2 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316237, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37903 p hg
    simpa only [d316237, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316236 p = 1 := by simpa only [d316237, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38295 p hg
    simpa only [d316237, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38297 (p : Pattern) (guard : d316238 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d316237 p = 1 := by simpa only [d316238, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38296 p hg
    simpa only [d316238, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316238, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37924 p hg
    simpa only [d316238, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38298 (p : Pattern) (guard : d316239 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d316238 p = 1 := by simpa only [d316239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38297 p hg
    simpa only [d316239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285875 p = 1 := by simpa only [d316239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38103 p hg
    simpa only [d316239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38299 (p : Pattern) (guard : d285991 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d285868 p = 1 := by simpa only [d285991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38096 p hg
    simpa only [d285991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37912 p hg
    simpa only [d285991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38300 (p : Pattern) (guard : d285992 p = 1) : d50347 p ≤ (2 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d285991 p = 1 := by simpa only [d285992, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38299 p hg
    simpa only [d285992, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285992, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37915 p hg
    simpa only [d285992, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38301 (p : Pattern) (guard : d285993 p = 1) : d50347 p ≤ (2 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d285992 p = 1 := by simpa only [d285993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38300 p hg
    simpa only [d285993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257187 p = 1 := by simpa only [d285993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37916 p hg
    simpa only [d285993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38302 (p : Pattern) (guard : d285994 p = 1) : d50362 p ≤ (2 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d285993 p = 1 := by simpa only [d285994, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38301 p hg
    simpa only [d285994, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285994, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37919 p hg
    simpa only [d285994, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38303 (p : Pattern) (guard : d285995 p = 1) : d50363 p ≤ (2 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d285994 p = 1 := by simpa only [d285995, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38302 p hg
    simpa only [d285995, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285995, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d285995, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38304 (p : Pattern) (guard : d285996 p = 1) : d50364 p ≤ (2 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285996, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37903 p hg
    simpa only [d285996, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285995 p = 1 := by simpa only [d285996, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38303 p hg
    simpa only [d285996, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38305 (p : Pattern) (guard : d285997 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d285996 p = 1 := by simpa only [d285997, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38304 p hg
    simpa only [d285997, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285997, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37924 p hg
    simpa only [d285997, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38306 (p : Pattern) (guard : d285998 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d285997 p = 1 := by simpa only [d285998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38305 p hg
    simpa only [d285998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257192 p = 1 := by simpa only [d285998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37925 p hg
    simpa only [d285998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38307 (p : Pattern) (guard : d316240 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d316239 p = 1 := by simpa only [d316240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38298 p hg
    simpa only [d316240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285998 p = 1 := by simpa only [d316240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38306 p hg
    simpa only [d316240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38308 (p : Pattern) (guard : d316241 p = 1) : d50368 p ≤ (2 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d316240 p = 1 := by simpa only [d316241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38307 p hg
    simpa only [d316241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285877 p = 1 := by simpa only [d316241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38105 p hg
    simpa only [d316241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38309 (p : Pattern) (guard : d316242 p = 1) : d50369 p ≤ (2 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316242, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37902 p hg
    simpa only [d316242, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316241 p = 1 := by simpa only [d316242, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38308 p hg
    simpa only [d316242, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38310 (p : Pattern) (guard : d316243 p = 1) : d50385 p ≤ (2 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316243, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37901 p hg
    simpa only [d316243, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316242 p = 1 := by simpa only [d316243, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38309 p hg
    simpa only [d316243, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38311 (p : Pattern) (guard : d316244 p = 1) : d50385 p ≤ (2 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d316243 p = 1 := by simpa only [d316244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38310 p hg
    simpa only [d316244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285880 p = 1 := by simpa only [d316244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38108 p hg
    simpa only [d316244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38312 (p : Pattern) (guard : d286105 p = 1) : d50385 p ≤ (2 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d285880 p = 1 := by simpa only [d286105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38108 p hg
    simpa only [d286105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37932 p hg
    simpa only [d286105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38313 (p : Pattern) (guard : d316315 p = 1) : d50385 p ≤ (2 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d316244 p = 1 := by simpa only [d316315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38311 p hg
    simpa only [d316315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286105 p = 1 := by simpa only [d316315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38312 p hg
    simpa only [d316315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38314 (p : Pattern) (guard : d316316 p = 1) : d50385 p ≤ (2 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d316315 p = 1 := by simpa only [d316316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38313 p hg
    simpa only [d316316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37932 p hg
    simpa only [d316316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38315 (p : Pattern) (guard : d316317 p = 1) : d50387 p ≤ (2 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d316316 p = 1 := by simpa only [d316317, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38314 p hg
    simpa only [d316317, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316317, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37936 p hg
    simpa only [d316317, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38316 (p : Pattern) (guard : d316318 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316318, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37900 p hg
    simpa only [d316318, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316317 p = 1 := by simpa only [d316318, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38315 p hg
    simpa only [d316318, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38317 (p : Pattern) (guard : d286110 p = 1) : d50385 p ≤ (2 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d286105 p = 1 := by simpa only [d286110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38312 p hg
    simpa only [d286110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37932 p hg
    simpa only [d286110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38318 (p : Pattern) (guard : d286111 p = 1) : d50385 p ≤ (2 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d286110 p = 1 := by simpa only [d286111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38317 p hg
    simpa only [d286111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37932 p hg
    simpa only [d286111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38319 (p : Pattern) (guard : d286112 p = 1) : d50387 p ≤ (2 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d286111 p = 1 := by simpa only [d286112, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38318 p hg
    simpa only [d286112, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286112, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37936 p hg
    simpa only [d286112, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38320 (p : Pattern) (guard : d286113 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286113, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37900 p hg
    simpa only [d286113, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286112 p = 1 := by simpa only [d286113, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38319 p hg
    simpa only [d286113, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38321 (p : Pattern) (guard : d316319 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d316318 p = 1 := by simpa only [d316319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38316 p hg
    simpa only [d316319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286113 p = 1 := by simpa only [d316319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38320 p hg
    simpa only [d316319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38322 (p : Pattern) (guard : d316320 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d316319 p = 1 := by simpa only [d316320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38321 p hg
    simpa only [d316320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d316320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38323 (p : Pattern) (guard : d316321 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d316320 p = 1 := by simpa only [d316321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38322 p hg
    simpa only [d316321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d316321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38324 (p : Pattern) (guard : d316331 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d316321 p = 1 := by simpa only [d316331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38323 p hg
    simpa only [d316331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d316331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38325 (p : Pattern) (guard : d286118 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d286113 p = 1 := by simpa only [d286118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38320 p hg
    simpa only [d286118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d286118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38326 (p : Pattern) (guard : d286119 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d286118 p = 1 := by simpa only [d286119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38325 p hg
    simpa only [d286119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d286119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38327 (p : Pattern) (guard : d286120 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d286119 p = 1 := by simpa only [d286120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38326 p hg
    simpa only [d286120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d286120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38328 (p : Pattern) (guard : d286131 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d286120 p = 1 := by simpa only [d286131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38327 p hg
    simpa only [d286131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d286131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38329 (p : Pattern) (guard : d316332 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d316331 p = 1 := by simpa only [d316332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38324 p hg
    simpa only [d316332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286131 p = 1 := by simpa only [d316332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38328 p hg
    simpa only [d316332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38330 (p : Pattern) (guard : d316333 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d316333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316332 p = 1 := by simpa only [d316333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38329 p hg
    simpa only [d316333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38331 (p : Pattern) (guard : d316334 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d316333 p = 1 := by simpa only [d316334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38330 p hg
    simpa only [d316334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d316334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38332 (p : Pattern) (guard : d316335 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d316335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316334 p = 1 := by simpa only [d316335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38331 p hg
    simpa only [d316335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38333 (p : Pattern) (guard : d316336 p = 1) : d50388 p ≤ (2 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37899 p hg
    simpa only [d316336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316335 p = 1 := by simpa only [d316336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38332 p hg
    simpa only [d316336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38334 (p : Pattern) (guard : d318230 p = 1) : d50389 p ≤ (2 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318230, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d318230, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316336 p = 1 := by simpa only [d318230, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38333 p hg
    simpa only [d318230, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38335 (p : Pattern) (guard : d318231 p = 1) : d50389 p ≤ (2 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37898 p hg
    simpa only [d318231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318230 p = 1 := by simpa only [d318231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38334 p hg
    simpa only [d318231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38336 (p : Pattern) (guard : d318232 p = 1) : d50389 p ≤ (2 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d318231 p = 1 := by simpa only [d318232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38335 p hg
    simpa only [d318232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37898 p hg
    simpa only [d318232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38337 (p : Pattern) (guard : d318233 p = 1) : d50389 p ≤ (2 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d318232 p = 1 := by simpa only [d318233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38336 p hg
    simpa only [d318233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37898 p hg
    simpa only [d318233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38338 (p : Pattern) (guard : d318234 p = 1) : d50389 p ≤ (2 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d318233 p = 1 := by simpa only [d318234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38337 p hg
    simpa only [d318234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37898 p hg
    simpa only [d318234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38339 (p : Pattern) (guard : d318235 p = 1) : d50390 p ≤ (2 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d318229 p = 1 := by simpa only [d318235, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38278 p hg
    simpa only [d318235, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318234 p = 1 := by simpa only [d318235, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38338 p hg
    simpa only [d318235, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38340 (p : Pattern) (guard : d1520 p = 1) : d47630 p ≤ (2 : Int) + d47630 p := by
  omega
theorem compare38341 (p : Pattern) (guard : d33554 p = 1) : d50139 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1520 p = 1 := by simpa only [d33554, d50139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38340 p hg
    simpa only [d33554, d50139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d33554, d50139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37961 p hg
    simpa only [d33554, d50139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38342 (p : Pattern) (guard : d286611 p = 1) : d50139 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37959 p hg
    simpa only [d286611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d33554 p = 1 := by simpa only [d286611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38341 p hg
    simpa only [d286611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38343 (p : Pattern) (guard : d286612 p = 1) : d50139 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d286611 p = 1 := by simpa only [d286612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38342 p hg
    simpa only [d286612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37959 p hg
    simpa only [d286612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38344 (p : Pattern) (guard : d286613 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d286612 p = 1 := by simpa only [d286613, d50168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38343 p hg
    simpa only [d286613, d50168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286613, d50168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37965 p hg
    simpa only [d286613, d50168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38345 (p : Pattern) (guard : d316227 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d286613 p = 1 := by simpa only [d316227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38344 p hg
    simpa only [d316227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285867 p = 1 := by simpa only [d316227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38133 p hg
    simpa only [d316227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38346 (p : Pattern) (guard : d534 p = 1) : d47630 p ≤ (2 : Int) + d47630 p := by
  omega
theorem compare38347 (p : Pattern) (guard : d33559 p = 1) : d50139 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d534 p = 1 := by simpa only [d33559, d50139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38346 p hg
    simpa only [d33559, d50139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d33559, d50139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37961 p hg
    simpa only [d33559, d50139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38348 (p : Pattern) (guard : d316228 p = 1) : d50139 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37959 p hg
    simpa only [d316228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d33559 p = 1 := by simpa only [d316228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38347 p hg
    simpa only [d316228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38349 (p : Pattern) (guard : d316229 p = 1) : d50139 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d316228 p = 1 := by simpa only [d316229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38348 p hg
    simpa only [d316229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37959 p hg
    simpa only [d316229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38350 (p : Pattern) (guard : d316230 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d316229 p = 1 := by simpa only [d316230, d50168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38349 p hg
    simpa only [d316230, d50168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316230, d50168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37965 p hg
    simpa only [d316230, d50168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38351 (p : Pattern) (guard : d316231 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d316230 p = 1 := by simpa only [d316231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38350 p hg
    simpa only [d316231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257184 p = 1 := by simpa only [d316231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37966 p hg
    simpa only [d316231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38352 (p : Pattern) (guard : d316232 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316227 p = 1 := by simpa only [d316232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38345 p hg
    simpa only [d316232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316231 p = 1 := by simpa only [d316232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38351 p hg
    simpa only [d316232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38353 (p : Pattern) (guard : d316233 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316232 p = 1 := by simpa only [d316233, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38352 p hg
    simpa only [d316233, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316233, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37970 p hg
    simpa only [d316233, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38354 (p : Pattern) (guard : d316234 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316233 p = 1 := by simpa only [d316234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38353 p hg
    simpa only [d316234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285870 p = 1 := by simpa only [d316234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38136 p hg
    simpa only [d316234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38355 (p : Pattern) (guard : d316278 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37958 p hg
    simpa only [d316278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316234 p = 1 := by simpa only [d316278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38354 p hg
    simpa only [d316278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38356 (p : Pattern) (guard : d316235 p = 1) : d50420 p ≤ (2 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316234 p = 1 := by simpa only [d316235, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38201 p hg
    simpa only [d316235, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316235, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37919 p hg
    simpa only [d316235, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38357 (p : Pattern) (guard : d316279 p = 1) : d50421 p ≤ (2 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316278 p = 1 := by simpa only [d316279, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38355 p hg
    simpa only [d316279, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316235 p = 1 := by simpa only [d316279, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38356 p hg
    simpa only [d316279, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38358 (p : Pattern) (guard : d1520 p = 1) : d47634 p ≤ (2 : Int) + d47634 p := by
  omega
theorem compare38359 (p : Pattern) (guard : d33554 p = 1) : d50144 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1520 p = 1 := by simpa only [d33554, d50144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38358 p hg
    simpa only [d33554, d50144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d33554, d50144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37978 p hg
    simpa only [d33554, d50144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38360 (p : Pattern) (guard : d286611 p = 1) : d50144 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37976 p hg
    simpa only [d286611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d33554 p = 1 := by simpa only [d286611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38359 p hg
    simpa only [d286611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38361 (p : Pattern) (guard : d286612 p = 1) : d50144 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 223 with
  | false =>
    have hg : d286611 p = 1 := by simpa only [d286612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38360 p hg
    simpa only [d286612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37976 p hg
    simpa only [d286612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38362 (p : Pattern) (guard : d286613 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 204 with
  | false =>
    have hg : d286612 p = 1 := by simpa only [d286613, d50211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38361 p hg
    simpa only [d286613, d50211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286613, d50211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37982 p hg
    simpa only [d286613, d50211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38363 (p : Pattern) (guard : d316227 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d286613 p = 1 := by simpa only [d316227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38362 p hg
    simpa only [d316227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285867 p = 1 := by simpa only [d316227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38145 p hg
    simpa only [d316227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38364 (p : Pattern) (guard : d534 p = 1) : d47634 p ≤ (2 : Int) + d47634 p := by
  omega
theorem compare38365 (p : Pattern) (guard : d33559 p = 1) : d50144 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 225 with
  | false =>
    have hg : d534 p = 1 := by simpa only [d33559, d50144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38364 p hg
    simpa only [d33559, d50144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d33559, d50144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37978 p hg
    simpa only [d33559, d50144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38366 (p : Pattern) (guard : d316228 p = 1) : d50144 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37976 p hg
    simpa only [d316228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d33559 p = 1 := by simpa only [d316228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38365 p hg
    simpa only [d316228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38367 (p : Pattern) (guard : d316229 p = 1) : d50144 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 223 with
  | false =>
    have hg : d316228 p = 1 := by simpa only [d316229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38366 p hg
    simpa only [d316229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37976 p hg
    simpa only [d316229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38368 (p : Pattern) (guard : d316230 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 204 with
  | false =>
    have hg : d316229 p = 1 := by simpa only [d316230, d50211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38367 p hg
    simpa only [d316230, d50211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316230, d50211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37982 p hg
    simpa only [d316230, d50211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38369 (p : Pattern) (guard : d316231 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d316230 p = 1 := by simpa only [d316231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38368 p hg
    simpa only [d316231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257184 p = 1 := by simpa only [d316231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37983 p hg
    simpa only [d316231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38370 (p : Pattern) (guard : d316232 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316227 p = 1 := by simpa only [d316232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38363 p hg
    simpa only [d316232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316231 p = 1 := by simpa only [d316232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38369 p hg
    simpa only [d316232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38371 (p : Pattern) (guard : d316233 p = 1) : d50212 p ≤ (2 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316232 p = 1 := by simpa only [d316233, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38370 p hg
    simpa only [d316233, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316233, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37987 p hg
    simpa only [d316233, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38372 (p : Pattern) (guard : d316234 p = 1) : d50212 p ≤ (2 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316233 p = 1 := by simpa only [d316234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38371 p hg
    simpa only [d316234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285870 p = 1 := by simpa only [d316234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38148 p hg
    simpa only [d316234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38373 (p : Pattern) (guard : d316235 p = 1) : d50223 p ≤ (2 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316234 p = 1 := by simpa only [d316235, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38372 p hg
    simpa only [d316235, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316235, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d316235, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38374 (p : Pattern) (guard : d316236 p = 1) : d50224 p ≤ (2 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316235 p = 1 := by simpa only [d316236, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38373 p hg
    simpa only [d316236, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316236, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d316236, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38375 (p : Pattern) (guard : d316280 p = 1) : d50422 p ≤ (2 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d316279 p = 1 := by simpa only [d316280, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38357 p hg
    simpa only [d316280, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316236 p = 1 := by simpa only [d316280, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38374 p hg
    simpa only [d316280, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38376 (p : Pattern) (guard : d316281 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d316280 p = 1 := by simpa only [d316281, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38375 p hg
    simpa only [d316281, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316281, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37994 p hg
    simpa only [d316281, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38377 (p : Pattern) (guard : d316282 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d316281 p = 1 := by simpa only [d316282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38376 p hg
    simpa only [d316282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285918 p = 1 := by simpa only [d316282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38153 p hg
    simpa only [d316282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38378 (p : Pattern) (guard : d285991 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d285868 p = 1 := by simpa only [d285991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38134 p hg
    simpa only [d285991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37967 p hg
    simpa only [d285991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38379 (p : Pattern) (guard : d285992 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d285991 p = 1 := by simpa only [d285992, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38378 p hg
    simpa only [d285992, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285992, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37970 p hg
    simpa only [d285992, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38380 (p : Pattern) (guard : d285993 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d285992 p = 1 := by simpa only [d285993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38379 p hg
    simpa only [d285993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257187 p = 1 := by simpa only [d285993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37971 p hg
    simpa only [d285993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38381 (p : Pattern) (guard : d286062 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37958 p hg
    simpa only [d286062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285993 p = 1 := by simpa only [d286062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38380 p hg
    simpa only [d286062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38382 (p : Pattern) (guard : d285994 p = 1) : d50420 p ≤ (2 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d285993 p = 1 := by simpa only [d285994, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38209 p hg
    simpa only [d285994, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285994, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37919 p hg
    simpa only [d285994, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38383 (p : Pattern) (guard : d286063 p = 1) : d50421 p ≤ (2 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d286062 p = 1 := by simpa only [d286063, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38381 p hg
    simpa only [d286063, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285994 p = 1 := by simpa only [d286063, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38382 p hg
    simpa only [d286063, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38384 (p : Pattern) (guard : d285991 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d285868 p = 1 := by simpa only [d285991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38146 p hg
    simpa only [d285991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37984 p hg
    simpa only [d285991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38385 (p : Pattern) (guard : d285992 p = 1) : d50212 p ≤ (2 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d285991 p = 1 := by simpa only [d285992, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38384 p hg
    simpa only [d285992, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285992, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37987 p hg
    simpa only [d285992, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38386 (p : Pattern) (guard : d285993 p = 1) : d50212 p ≤ (2 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d285992 p = 1 := by simpa only [d285993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38385 p hg
    simpa only [d285993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257187 p = 1 := by simpa only [d285993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37988 p hg
    simpa only [d285993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38387 (p : Pattern) (guard : d285994 p = 1) : d50223 p ≤ (2 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d285993 p = 1 := by simpa only [d285994, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38386 p hg
    simpa only [d285994, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285994, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d285994, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38388 (p : Pattern) (guard : d285995 p = 1) : d50224 p ≤ (2 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d285994 p = 1 := by simpa only [d285995, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38387 p hg
    simpa only [d285995, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d285995, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d285995, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38389 (p : Pattern) (guard : d286064 p = 1) : d50422 p ≤ (2 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d286063 p = 1 := by simpa only [d286064, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38383 p hg
    simpa only [d286064, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285995 p = 1 := by simpa only [d286064, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38388 p hg
    simpa only [d286064, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38390 (p : Pattern) (guard : d286065 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d286064 p = 1 := by simpa only [d286065, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38389 p hg
    simpa only [d286065, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286065, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37994 p hg
    simpa only [d286065, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38391 (p : Pattern) (guard : d286066 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d286065 p = 1 := by simpa only [d286066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38390 p hg
    simpa only [d286066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257233 p = 1 := by simpa only [d286066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37995 p hg
    simpa only [d286066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38392 (p : Pattern) (guard : d316283 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d316282 p = 1 := by simpa only [d316283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38377 p hg
    simpa only [d316283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286066 p = 1 := by simpa only [d316283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38391 p hg
    simpa only [d316283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38393 (p : Pattern) (guard : d316284 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d316283 p = 1 := by simpa only [d316284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38392 p hg
    simpa only [d316284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285920 p = 1 := by simpa only [d316284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38155 p hg
    simpa only [d316284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38394 (p : Pattern) (guard : d316285 p = 1) : d50427 p ≤ (2 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316285, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37957 p hg
    simpa only [d316285, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316284 p = 1 := by simpa only [d316285, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38393 p hg
    simpa only [d316285, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38395 (p : Pattern) (guard : d316286 p = 1) : d50428 p ≤ (2 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316286, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37956 p hg
    simpa only [d316286, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316285 p = 1 := by simpa only [d316286, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38394 p hg
    simpa only [d316286, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38396 (p : Pattern) (guard : d316287 p = 1) : d50428 p ≤ (2 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d316286 p = 1 := by simpa only [d316287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38395 p hg
    simpa only [d316287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d285923 p = 1 := by simpa only [d316287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38158 p hg
    simpa only [d316287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38397 (p : Pattern) (guard : d286288 p = 1) : d50428 p ≤ (2 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d285923 p = 1 := by simpa only [d286288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38158 p hg
    simpa only [d286288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38002 p hg
    simpa only [d286288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38398 (p : Pattern) (guard : d316469 p = 1) : d50428 p ≤ (2 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d316287 p = 1 := by simpa only [d316469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38396 p hg
    simpa only [d316469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286288 p = 1 := by simpa only [d316469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38397 p hg
    simpa only [d316469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38399 (p : Pattern) (guard : d316470 p = 1) : d50428 p ≤ (2 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d316469 p = 1 := by simpa only [d316470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38398 p hg
    simpa only [d316470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38002 p hg
    simpa only [d316470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38400 (p : Pattern) (guard : d316471 p = 1) : d50430 p ≤ (2 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d316470 p = 1 := by simpa only [d316471, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38399 p hg
    simpa only [d316471, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316471, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38006 p hg
    simpa only [d316471, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38401 (p : Pattern) (guard : d316472 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316472, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37820 p hg
    simpa only [d316472, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316471 p = 1 := by simpa only [d316472, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38400 p hg
    simpa only [d316472, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38402 (p : Pattern) (guard : d286297 p = 1) : d50428 p ≤ (2 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d286288 p = 1 := by simpa only [d286297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38397 p hg
    simpa only [d286297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38002 p hg
    simpa only [d286297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38403 (p : Pattern) (guard : d286298 p = 1) : d50428 p ≤ (2 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d286297 p = 1 := by simpa only [d286298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38402 p hg
    simpa only [d286298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38002 p hg
    simpa only [d286298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38404 (p : Pattern) (guard : d286299 p = 1) : d50430 p ≤ (2 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d286298 p = 1 := by simpa only [d286299, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38403 p hg
    simpa only [d286299, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286299, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38006 p hg
    simpa only [d286299, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38405 (p : Pattern) (guard : d286300 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d286300, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37820 p hg
    simpa only [d286300, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286299 p = 1 := by simpa only [d286300, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38404 p hg
    simpa only [d286300, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38406 (p : Pattern) (guard : d316477 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d316472 p = 1 := by simpa only [d316477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38401 p hg
    simpa only [d316477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286300 p = 1 := by simpa only [d316477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38405 p hg
    simpa only [d316477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38407 (p : Pattern) (guard : d316478 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d316477 p = 1 := by simpa only [d316478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38406 p hg
    simpa only [d316478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d316478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38408 (p : Pattern) (guard : d316479 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d316478 p = 1 := by simpa only [d316479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38407 p hg
    simpa only [d316479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d316479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38409 (p : Pattern) (guard : d316480 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d316479 p = 1 := by simpa only [d316480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38408 p hg
    simpa only [d316480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d316480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38410 (p : Pattern) (guard : d286318 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d286300 p = 1 := by simpa only [d286318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38405 p hg
    simpa only [d286318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d286318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38411 (p : Pattern) (guard : d286319 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d286318 p = 1 := by simpa only [d286319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38410 p hg
    simpa only [d286319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d286319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38412 (p : Pattern) (guard : d286320 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d286319 p = 1 := by simpa only [d286320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38411 p hg
    simpa only [d286320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d286320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38413 (p : Pattern) (guard : d286321 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d286320 p = 1 := by simpa only [d286321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38412 p hg
    simpa only [d286321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d286321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38414 (p : Pattern) (guard : d318236 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d316480 p = 1 := by simpa only [d318236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38409 p hg
    simpa only [d318236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286321 p = 1 := by simpa only [d318236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38413 p hg
    simpa only [d318236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38415 (p : Pattern) (guard : d318237 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d318237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318236 p = 1 := by simpa only [d318237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38414 p hg
    simpa only [d318237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38416 (p : Pattern) (guard : d318238 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d318237 p = 1 := by simpa only [d318238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38415 p hg
    simpa only [d318238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d318238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38417 (p : Pattern) (guard : d318239 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d318239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318238 p = 1 := by simpa only [d318239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38416 p hg
    simpa only [d318239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38418 (p : Pattern) (guard : d318240 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d318240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318239 p = 1 := by simpa only [d318240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38417 p hg
    simpa only [d318240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38419 (p : Pattern) (guard : d318241 p = 1) : d50432 p ≤ (2 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318241, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d318241, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318240 p = 1 := by simpa only [d318241, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38418 p hg
    simpa only [d318241, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38420 (p : Pattern) (guard : d318242 p = 1) : d50432 p ≤ (2 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37954 p hg
    simpa only [d318242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318241 p = 1 := by simpa only [d318242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38419 p hg
    simpa only [d318242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38421 (p : Pattern) (guard : d318243 p = 1) : d50432 p ≤ (2 : Int) + d47809 p := by
  cases selected : p 69 with
  | false =>
    have hg : d318242 p = 1 := by simpa only [d318243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38420 p hg
    simpa only [d318243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37954 p hg
    simpa only [d318243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38422 (p : Pattern) (guard : d318244 p = 1) : d50432 p ≤ (2 : Int) + d47809 p := by
  cases selected : p 51 with
  | false =>
    have hg : d318243 p = 1 := by simpa only [d318244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38421 p hg
    simpa only [d318244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37954 p hg
    simpa only [d318244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38423 (p : Pattern) (guard : d318245 p = 1) : d50432 p ≤ (2 : Int) + d47809 p := by
  cases selected : p 50 with
  | false =>
    have hg : d318244 p = 1 := by simpa only [d318245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38422 p hg
    simpa only [d318245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37954 p hg
    simpa only [d318245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38424 (p : Pattern) (guard : d318246 p = 1) : d50492 p ≤ (2 : Int) + d47865 p := by
  cases selected : p 49 with
  | false =>
    have hg : d318245 p = 1 := by simpa only [d318246, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38423 p hg
    simpa only [d318246, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318246, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38023 p hg
    simpa only [d318246, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38425 (p : Pattern) (guard : d318247 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d318235 p = 1 := by simpa only [d318247, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38339 p hg
    simpa only [d318247, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318246 p = 1 := by simpa only [d318247, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38424 p hg
    simpa only [d318247, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38426 (p : Pattern) (guard : d318248 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318247 p = 1 := by simpa only [d318248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38425 p hg
    simpa only [d318248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38427 (p : Pattern) (guard : d318249 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318248 p = 1 := by simpa only [d318249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38426 p hg
    simpa only [d318249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38428 (p : Pattern) (guard : d318250 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318249 p = 1 := by simpa only [d318250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38427 p hg
    simpa only [d318250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38429 (p : Pattern) (guard : d318251 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318250 p = 1 := by simpa only [d318251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38428 p hg
    simpa only [d318251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38430 (p : Pattern) (guard : d318252 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318251 p = 1 := by simpa only [d318252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38429 p hg
    simpa only [d318252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38431 (p : Pattern) (guard : d318253 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318252 p = 1 := by simpa only [d318253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38430 p hg
    simpa only [d318253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38432 (p : Pattern) (guard : d318254 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318253 p = 1 := by simpa only [d318254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38431 p hg
    simpa only [d318254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38433 (p : Pattern) (guard : d318255 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d287276 p = 1 := by simpa only [d318255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38186 p hg
    simpa only [d318255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318254 p = 1 := by simpa only [d318255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38432 p hg
    simpa only [d318255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38434 (p : Pattern) (guard : d316353 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37832 p hg
    simpa only [d316353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d286613 p = 1 := by simpa only [d316353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38191 p hg
    simpa only [d316353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38435 (p : Pattern) (guard : d825 p = 1) : d47617 p ≤ (2 : Int) + d47617 p := by
  omega
theorem compare38436 (p : Pattern) (guard : d5121 p = 1) : d50119 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d825 p = 1 := by simpa only [d5121, d50119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38435 p hg
    simpa only [d5121, d50119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5121, d50119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37826 p hg
    simpa only [d5121, d50119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38437 (p : Pattern) (guard : d34352 p = 1) : d50119 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d34352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37824 p hg
    simpa only [d34352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5121 p = 1 := by simpa only [d34352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38436 p hg
    simpa only [d34352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38438 (p : Pattern) (guard : d34353 p = 1) : d50119 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d34352 p = 1 := by simpa only [d34353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38437 p hg
    simpa only [d34353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37824 p hg
    simpa only [d34353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38439 (p : Pattern) (guard : d34354 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d34353 p = 1 := by simpa only [d34354, d50122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38438 p hg
    simpa only [d34354, d50122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34354, d50122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37830 p hg
    simpa only [d34354, d50122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38440 (p : Pattern) (guard : d316354 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d34354 p = 1 := by simpa only [d316354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38439 p hg
    simpa only [d316354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316230 p = 1 := by simpa only [d316354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38197 p hg
    simpa only [d316354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38441 (p : Pattern) (guard : d316355 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316353 p = 1 := by simpa only [d316355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38434 p hg
    simpa only [d316355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316354 p = 1 := by simpa only [d316355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38440 p hg
    simpa only [d316355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38442 (p : Pattern) (guard : d316356 p = 1) : d50202 p ≤ (2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316355 p = 1 := by simpa only [d316356, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38441 p hg
    simpa only [d316356, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316356, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37835 p hg
    simpa only [d316356, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38443 (p : Pattern) (guard : d40149 p = 1) : d47617 p ≤ (2 : Int) + d47617 p := by
  omega
theorem compare38444 (p : Pattern) (guard : d317407 p = 1) : d50119 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d40149 p = 1 := by simpa only [d317407, d50119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38443 p hg
    simpa only [d317407, d50119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317407, d50119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37826 p hg
    simpa only [d317407, d50119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38445 (p : Pattern) (guard : d317408 p = 1) : d50119 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37824 p hg
    simpa only [d317408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317407 p = 1 := by simpa only [d317408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38444 p hg
    simpa only [d317408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38446 (p : Pattern) (guard : d317409 p = 1) : d50119 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d317408 p = 1 := by simpa only [d317409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38445 p hg
    simpa only [d317409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37824 p hg
    simpa only [d317409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38447 (p : Pattern) (guard : d317410 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d317409 p = 1 := by simpa only [d317410, d50122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38446 p hg
    simpa only [d317410, d50122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317410, d50122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37830 p hg
    simpa only [d317410, d50122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38448 (p : Pattern) (guard : d317411 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d286613 p = 1 := by simpa only [d317411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38191 p hg
    simpa only [d317411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317410 p = 1 := by simpa only [d317411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38447 p hg
    simpa only [d317411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38449 (p : Pattern) (guard : d317412 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317411 p = 1 := by simpa only [d317412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38448 p hg
    simpa only [d317412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316231 p = 1 := by simpa only [d317412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38198 p hg
    simpa only [d317412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38450 (p : Pattern) (guard : d317413 p = 1) : d50202 p ≤ (2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317412 p = 1 := by simpa only [d317413, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38449 p hg
    simpa only [d317413, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317413, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37835 p hg
    simpa only [d317413, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38451 (p : Pattern) (guard : d317414 p = 1) : d50202 p ≤ (2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316356 p = 1 := by simpa only [d317414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38442 p hg
    simpa only [d317414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317413 p = 1 := by simpa only [d317414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38450 p hg
    simpa only [d317414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38452 (p : Pattern) (guard : d317415 p = 1) : d50220 p ≤ (2 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317414 p = 1 := by simpa only [d317415, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38451 p hg
    simpa only [d317415, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317415, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37839 p hg
    simpa only [d317415, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38453 (p : Pattern) (guard : d317416 p = 1) : d50221 p ≤ (2 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317415 p = 1 := by simpa only [d317416, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38452 p hg
    simpa only [d317416, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317416, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37841 p hg
    simpa only [d317416, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38454 (p : Pattern) (guard : d317417 p = 1) : d50222 p ≤ (2 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317417, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37823 p hg
    simpa only [d317417, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317416 p = 1 := by simpa only [d317417, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38453 p hg
    simpa only [d317417, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38455 (p : Pattern) (guard : d317418 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317417 p = 1 := by simpa only [d317418, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38454 p hg
    simpa only [d317418, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317418, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37844 p hg
    simpa only [d317418, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38456 (p : Pattern) (guard : d1540 p = 1) : d47617 p ≤ (2 : Int) + d47617 p := by
  omega
theorem compare38457 (p : Pattern) (guard : d1541 p = 1) : d50119 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1540 p = 1 := by simpa only [d1541, d50119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38456 p hg
    simpa only [d1541, d50119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1541, d50119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37826 p hg
    simpa only [d1541, d50119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38458 (p : Pattern) (guard : d258089 p = 1) : d50119 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37824 p hg
    simpa only [d258089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1541 p = 1 := by simpa only [d258089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38457 p hg
    simpa only [d258089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38459 (p : Pattern) (guard : d316362 p = 1) : d50119 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d258089 p = 1 := by simpa only [d316362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38458 p hg
    simpa only [d316362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37824 p hg
    simpa only [d316362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38460 (p : Pattern) (guard : d316363 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d316362 p = 1 := by simpa only [d316363, d50122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38459 p hg
    simpa only [d316363, d50122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316363, d50122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37830 p hg
    simpa only [d316363, d50122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38461 (p : Pattern) (guard : d316364 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d316363 p = 1 := by simpa only [d316364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38460 p hg
    simpa only [d316364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257184 p = 1 := by simpa only [d316364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37831 p hg
    simpa only [d316364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38462 (p : Pattern) (guard : d316365 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316364 p = 1 := by simpa only [d316365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38461 p hg
    simpa only [d316365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37832 p hg
    simpa only [d316365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38463 (p : Pattern) (guard : d316366 p = 1) : d50202 p ≤ (2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316365 p = 1 := by simpa only [d316366, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38462 p hg
    simpa only [d316366, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316366, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37835 p hg
    simpa only [d316366, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38464 (p : Pattern) (guard : d317419 p = 1) : d50202 p ≤ (2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317413 p = 1 := by simpa only [d317419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38450 p hg
    simpa only [d317419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316366 p = 1 := by simpa only [d317419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38463 p hg
    simpa only [d317419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38465 (p : Pattern) (guard : d317420 p = 1) : d50220 p ≤ (2 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317419 p = 1 := by simpa only [d317420, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38464 p hg
    simpa only [d317420, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317420, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37839 p hg
    simpa only [d317420, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38466 (p : Pattern) (guard : d317421 p = 1) : d50221 p ≤ (2 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317420 p = 1 := by simpa only [d317421, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38465 p hg
    simpa only [d317421, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317421, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37841 p hg
    simpa only [d317421, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38467 (p : Pattern) (guard : d317422 p = 1) : d50222 p ≤ (2 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317422, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37823 p hg
    simpa only [d317422, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317421 p = 1 := by simpa only [d317422, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38466 p hg
    simpa only [d317422, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38468 (p : Pattern) (guard : d317423 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317422 p = 1 := by simpa only [d317423, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38467 p hg
    simpa only [d317423, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317423, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37844 p hg
    simpa only [d317423, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38469 (p : Pattern) (guard : d317424 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317418 p = 1 := by simpa only [d317424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38455 p hg
    simpa only [d317424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317423 p = 1 := by simpa only [d317424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38468 p hg
    simpa only [d317424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38470 (p : Pattern) (guard : d316373 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d286613 p = 1 := by simpa only [d316373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38191 p hg
    simpa only [d316373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316363 p = 1 := by simpa only [d316373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38460 p hg
    simpa only [d316373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38471 (p : Pattern) (guard : d316374 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316373 p = 1 := by simpa only [d316374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38470 p hg
    simpa only [d316374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37832 p hg
    simpa only [d316374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38472 (p : Pattern) (guard : d316375 p = 1) : d50202 p ≤ (2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316374 p = 1 := by simpa only [d316375, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38471 p hg
    simpa only [d316375, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316375, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37835 p hg
    simpa only [d316375, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38473 (p : Pattern) (guard : d316376 p = 1) : d50202 p ≤ (2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316375 p = 1 := by simpa only [d316376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38472 p hg
    simpa only [d316376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316366 p = 1 := by simpa only [d316376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38463 p hg
    simpa only [d316376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38474 (p : Pattern) (guard : d316377 p = 1) : d50220 p ≤ (2 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316376 p = 1 := by simpa only [d316377, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38473 p hg
    simpa only [d316377, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316377, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37839 p hg
    simpa only [d316377, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38475 (p : Pattern) (guard : d316378 p = 1) : d50221 p ≤ (2 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316377 p = 1 := by simpa only [d316378, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38474 p hg
    simpa only [d316378, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316378, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37841 p hg
    simpa only [d316378, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38476 (p : Pattern) (guard : d316379 p = 1) : d50222 p ≤ (2 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316379, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37823 p hg
    simpa only [d316379, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316378 p = 1 := by simpa only [d316379, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38475 p hg
    simpa only [d316379, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38477 (p : Pattern) (guard : d316380 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d316379 p = 1 := by simpa only [d316380, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38476 p hg
    simpa only [d316380, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316380, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37844 p hg
    simpa only [d316380, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38478 (p : Pattern) (guard : d317425 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d317410 p = 1 := by simpa only [d317425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38447 p hg
    simpa only [d317425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257184 p = 1 := by simpa only [d317425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37831 p hg
    simpa only [d317425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38479 (p : Pattern) (guard : d317426 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317425 p = 1 := by simpa only [d317426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38478 p hg
    simpa only [d317426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257185 p = 1 := by simpa only [d317426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37833 p hg
    simpa only [d317426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38480 (p : Pattern) (guard : d317427 p = 1) : d50202 p ≤ (2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317426 p = 1 := by simpa only [d317427, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38479 p hg
    simpa only [d317427, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317427, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37835 p hg
    simpa only [d317427, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38481 (p : Pattern) (guard : d317428 p = 1) : d50202 p ≤ (2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317427 p = 1 := by simpa only [d317428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38480 p hg
    simpa only [d317428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37837 p hg
    simpa only [d317428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38482 (p : Pattern) (guard : d317429 p = 1) : d50220 p ≤ (2 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317428 p = 1 := by simpa only [d317429, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38481 p hg
    simpa only [d317429, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317429, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37839 p hg
    simpa only [d317429, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38483 (p : Pattern) (guard : d317430 p = 1) : d50221 p ≤ (2 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317429 p = 1 := by simpa only [d317430, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38482 p hg
    simpa only [d317430, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317430, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37841 p hg
    simpa only [d317430, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38484 (p : Pattern) (guard : d317431 p = 1) : d50222 p ≤ (2 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317431, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37823 p hg
    simpa only [d317431, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317430 p = 1 := by simpa only [d317431, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38483 p hg
    simpa only [d317431, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38485 (p : Pattern) (guard : d317432 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317431 p = 1 := by simpa only [d317432, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38484 p hg
    simpa only [d317432, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317432, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37844 p hg
    simpa only [d317432, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38486 (p : Pattern) (guard : d317433 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d316380 p = 1 := by simpa only [d317433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38477 p hg
    simpa only [d317433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317432 p = 1 := by simpa only [d317433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38485 p hg
    simpa only [d317433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38487 (p : Pattern) (guard : d317434 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317424 p = 1 := by simpa only [d317434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38469 p hg
    simpa only [d317434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317433 p = 1 := by simpa only [d317434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38486 p hg
    simpa only [d317434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38488 (p : Pattern) (guard : d317435 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d317410 p = 1 := by simpa only [d317435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38447 p hg
    simpa only [d317435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37832 p hg
    simpa only [d317435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38489 (p : Pattern) (guard : d317436 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317435 p = 1 := by simpa only [d317436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38488 p hg
    simpa only [d317436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257185 p = 1 := by simpa only [d317436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37833 p hg
    simpa only [d317436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38490 (p : Pattern) (guard : d317437 p = 1) : d50202 p ≤ (2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317436 p = 1 := by simpa only [d317437, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38489 p hg
    simpa only [d317437, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317437, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37835 p hg
    simpa only [d317437, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38491 (p : Pattern) (guard : d317438 p = 1) : d50202 p ≤ (2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317413 p = 1 := by simpa only [d317438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38450 p hg
    simpa only [d317438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317437 p = 1 := by simpa only [d317438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38490 p hg
    simpa only [d317438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38492 (p : Pattern) (guard : d317439 p = 1) : d50220 p ≤ (2 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317438 p = 1 := by simpa only [d317439, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38491 p hg
    simpa only [d317439, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317439, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37839 p hg
    simpa only [d317439, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38493 (p : Pattern) (guard : d317440 p = 1) : d50221 p ≤ (2 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317439 p = 1 := by simpa only [d317440, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38492 p hg
    simpa only [d317440, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317440, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37841 p hg
    simpa only [d317440, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38494 (p : Pattern) (guard : d317441 p = 1) : d50222 p ≤ (2 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317441, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37823 p hg
    simpa only [d317441, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317440 p = 1 := by simpa only [d317441, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38493 p hg
    simpa only [d317441, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38495 (p : Pattern) (guard : d317442 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317441 p = 1 := by simpa only [d317442, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38494 p hg
    simpa only [d317442, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317442, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37844 p hg
    simpa only [d317442, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38496 (p : Pattern) (guard : d317443 p = 1) : d50202 p ≤ (2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317437 p = 1 := by simpa only [d317443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38490 p hg
    simpa only [d317443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37837 p hg
    simpa only [d317443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38497 (p : Pattern) (guard : d317444 p = 1) : d50220 p ≤ (2 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317443 p = 1 := by simpa only [d317444, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38496 p hg
    simpa only [d317444, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317444, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37839 p hg
    simpa only [d317444, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38498 (p : Pattern) (guard : d317445 p = 1) : d50221 p ≤ (2 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317444 p = 1 := by simpa only [d317445, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38497 p hg
    simpa only [d317445, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317445, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37841 p hg
    simpa only [d317445, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38499 (p : Pattern) (guard : d317446 p = 1) : d50222 p ≤ (2 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317446, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37823 p hg
    simpa only [d317446, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317445 p = 1 := by simpa only [d317446, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38498 p hg
    simpa only [d317446, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
