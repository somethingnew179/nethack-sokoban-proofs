import NetHack.Soko22Hazard87.Compare184
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare46250 (p : Pattern) (guard : d366942 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366940 p = 1 := by simpa only [d366942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46245 p hg
    simpa only [d366942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366941 p = 1 := by simpa only [d366942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46249 p hg
    simpa only [d366942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46251 (p : Pattern) (guard : d366943 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d366943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366942 p = 1 := by simpa only [d366943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46250 p hg
    simpa only [d366943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46252 (p : Pattern) (guard : d366944 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366943 p = 1 := by simpa only [d366944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46251 p hg
    simpa only [d366944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d366944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46253 (p : Pattern) (guard : d366945 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d366945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366944 p = 1 := by simpa only [d366945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46252 p hg
    simpa only [d366945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46254 (p : Pattern) (guard : d366946 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d366946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366945 p = 1 := by simpa only [d366946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46253 p hg
    simpa only [d366946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46255 (p : Pattern) (guard : d367498 p = 1) : d51469 p ≤ (7 : Int) + d338786 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367498, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d367498, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366946 p = 1 := by simpa only [d367498, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46254 p hg
    simpa only [d367498, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46256 (p : Pattern) (guard : d367499 p = 1) : d51469 p ≤ (7 : Int) + d338786 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45338 p hg
    simpa only [d367499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367498 p = 1 := by simpa only [d367499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46255 p hg
    simpa only [d367499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46257 (p : Pattern) (guard : d367500 p = 1) : d51469 p ≤ (7 : Int) + d338786 p := by
  cases selected : p 69 with
  | false =>
    have hg : d367499 p = 1 := by simpa only [d367500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46256 p hg
    simpa only [d367500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45338 p hg
    simpa only [d367500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46258 (p : Pattern) (guard : d367501 p = 1) : d51469 p ≤ (7 : Int) + d338786 p := by
  cases selected : p 51 with
  | false =>
    have hg : d367500 p = 1 := by simpa only [d367501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46257 p hg
    simpa only [d367501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45338 p hg
    simpa only [d367501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46259 (p : Pattern) (guard : d367502 p = 1) : d51469 p ≤ (7 : Int) + d338786 p := by
  cases selected : p 50 with
  | false =>
    have hg : d367501 p = 1 := by simpa only [d367502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46258 p hg
    simpa only [d367502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45338 p hg
    simpa only [d367502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46260 (p : Pattern) (guard : d367503 p = 1) : d51470 p ≤ (7 : Int) + d338787 p := by
  cases selected : p 49 with
  | false =>
    have hg : d367497 p = 1 := by simpa only [d367503, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46203 p hg
    simpa only [d367503, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367502 p = 1 := by simpa only [d367503, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46259 p hg
    simpa only [d367503, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46261 (p : Pattern) (guard : d2006 p = 1) : d47629 p ≤ (7 : Int) + d2 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2005 p = 1 := by simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45701 p hg
    simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45381 p hg
    simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46262 (p : Pattern) (guard : d2007 p = 1) : d47629 p ≤ (7 : Int) + d2 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45381 p hg
    simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2006 p = 1 := by simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46261 p hg
    simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46263 (p : Pattern) (guard : d2008 p = 1) : d47629 p ≤ (7 : Int) + d2 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45381 p hg
    simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2007 p = 1 := by simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46262 p hg
    simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46264 (p : Pattern) (guard : d34782 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2008 p = 1 := by simpa only [d34782, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46263 p hg
    simpa only [d34782, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34782, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45390 p hg
    simpa only [d34782, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46265 (p : Pattern) (guard : d34783 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d34783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45392 p hg
    simpa only [d34783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34782 p = 1 := by simpa only [d34783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46264 p hg
    simpa only [d34783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46266 (p : Pattern) (guard : d43846 p = 1) : d47629 p ≤ (7 : Int) + d2 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2007 p = 1 := by simpa only [d43846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46262 p hg
    simpa only [d43846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d43846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45381 p hg
    simpa only [d43846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46267 (p : Pattern) (guard : d43847 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 204 with
  | false =>
    have hg : d43846 p = 1 := by simpa only [d43847, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46266 p hg
    simpa only [d43847, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d43847, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45390 p hg
    simpa only [d43847, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46268 (p : Pattern) (guard : d43848 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d43848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45392 p hg
    simpa only [d43848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d43847 p = 1 := by simpa only [d43848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46267 p hg
    simpa only [d43848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46269 (p : Pattern) (guard : d311925 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 201 with
  | false =>
    have hg : d34783 p = 1 := by simpa only [d311925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46265 p hg
    simpa only [d311925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d43848 p = 1 := by simpa only [d311925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46268 p hg
    simpa only [d311925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46270 (p : Pattern) (guard : d311926 p = 1) : d51277 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 182 with
  | false =>
    have hg : d311925 p = 1 := by simpa only [d311926, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46269 p hg
    simpa only [d311926, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d311926, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45395 p hg
    simpa only [d311926, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46271 (p : Pattern) (guard : d43867 p = 1) : d47629 p ≤ (7 : Int) + d2 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2002 p = 1 := by simpa only [d43867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45700 p hg
    simpa only [d43867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2006 p = 1 := by simpa only [d43867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46261 p hg
    simpa only [d43867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46272 (p : Pattern) (guard : d10054 p = 1) : d47629 p ≤ (7 : Int) + d2 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2006 p = 1 := by simpa only [d10054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46261 p hg
    simpa only [d10054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45381 p hg
    simpa only [d10054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46273 (p : Pattern) (guard : d366854 p = 1) : d47629 p ≤ (7 : Int) + d2 p := by
  cases selected : p 223 with
  | false =>
    have hg : d43867 p = 1 := by simpa only [d366854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46271 p hg
    simpa only [d366854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10054 p = 1 := by simpa only [d366854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46272 p hg
    simpa only [d366854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46274 (p : Pattern) (guard : d366855 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 204 with
  | false =>
    have hg : d366854 p = 1 := by simpa only [d366855, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46273 p hg
    simpa only [d366855, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366855, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45390 p hg
    simpa only [d366855, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46275 (p : Pattern) (guard : d366856 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d34782 p = 1 := by simpa only [d366856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46264 p hg
    simpa only [d366856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366855 p = 1 := by simpa only [d366856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46274 p hg
    simpa only [d366856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46276 (p : Pattern) (guard : d343143 p = 1) : d47629 p ≤ (7 : Int) + d2 p := by
  cases selected : p 223 with
  | false =>
    have hg : d10054 p = 1 := by simpa only [d343143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46272 p hg
    simpa only [d343143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45381 p hg
    simpa only [d343143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46277 (p : Pattern) (guard : d343144 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 204 with
  | false =>
    have hg : d343143 p = 1 := by simpa only [d343144, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46276 p hg
    simpa only [d343144, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343144, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45390 p hg
    simpa only [d343144, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46278 (p : Pattern) (guard : d366857 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d43847 p = 1 := by simpa only [d366857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46267 p hg
    simpa only [d366857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343144 p = 1 := by simpa only [d366857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46277 p hg
    simpa only [d366857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46279 (p : Pattern) (guard : d366858 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 201 with
  | false =>
    have hg : d366856 p = 1 := by simpa only [d366858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46275 p hg
    simpa only [d366858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366857 p = 1 := by simpa only [d366858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46278 p hg
    simpa only [d366858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46280 (p : Pattern) (guard : d366859 p = 1) : d51277 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 182 with
  | false =>
    have hg : d366858 p = 1 := by simpa only [d366859, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46279 p hg
    simpa only [d366859, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366859, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45395 p hg
    simpa only [d366859, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46281 (p : Pattern) (guard : d366860 p = 1) : d51277 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 180 with
  | false =>
    have hg : d311926 p = 1 := by simpa only [d366860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46270 p hg
    simpa only [d366860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366859 p = 1 := by simpa only [d366860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46280 p hg
    simpa only [d366860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46282 (p : Pattern) (guard : d367083 p = 1) : d51529 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367083, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45380 p hg
    simpa only [d367083, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366860 p = 1 := by simpa only [d367083, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46281 p hg
    simpa only [d367083, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46283 (p : Pattern) (guard : d366861 p = 1) : d51530 p ≤ (7 : Int) + d338814 p := by
  cases selected : p 163 with
  | false =>
    have hg : d366860 p = 1 := by simpa only [d366861, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46088 p hg
    simpa only [d366861, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366861, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45400 p hg
    simpa only [d366861, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46284 (p : Pattern) (guard : d367084 p = 1) : d51531 p ≤ (7 : Int) + d338815 p := by
  cases selected : p 162 with
  | false =>
    have hg : d367083 p = 1 := by simpa only [d367084, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46282 p hg
    simpa only [d367084, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366861 p = 1 := by simpa only [d367084, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46283 p hg
    simpa only [d367084, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46285 (p : Pattern) (guard : d366862 p = 1) : d51291 p ≤ (7 : Int) + d338710 p := by
  have ha := bounds51291 p
  have hb := bounds338710 p
  omega
theorem compare46286 (p : Pattern) (guard : d367085 p = 1) : d51532 p ≤ (7 : Int) + d338816 p := by
  cases selected : p 161 with
  | false =>
    have hg : d367084 p = 1 := by simpa only [d367085, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46284 p hg
    simpa only [d367085, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366862 p = 1 := by simpa only [d367085, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46285 p hg
    simpa only [d367085, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46287 (p : Pattern) (guard : d367086 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d367085 p = 1 := by simpa only [d367086, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46286 p hg
    simpa only [d367086, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367086, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45405 p hg
    simpa only [d367086, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46288 (p : Pattern) (guard : d43868 p = 1) : d47629 p ≤ (7 : Int) + d2 p := by
  cases selected : p 223 with
  | false =>
    have hg : d43867 p = 1 := by simpa only [d43868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46271 p hg
    simpa only [d43868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d43868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45381 p hg
    simpa only [d43868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46289 (p : Pattern) (guard : d43869 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 204 with
  | false =>
    have hg : d43868 p = 1 := by simpa only [d43869, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46288 p hg
    simpa only [d43869, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d43869, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45390 p hg
    simpa only [d43869, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46290 (p : Pattern) (guard : d366865 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d43869 p = 1 := by simpa only [d366865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46289 p hg
    simpa only [d366865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343144 p = 1 := by simpa only [d366865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46277 p hg
    simpa only [d366865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46291 (p : Pattern) (guard : d366866 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 201 with
  | false =>
    have hg : d366856 p = 1 := by simpa only [d366866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46275 p hg
    simpa only [d366866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366865 p = 1 := by simpa only [d366866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46290 p hg
    simpa only [d366866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46292 (p : Pattern) (guard : d366867 p = 1) : d51277 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 182 with
  | false =>
    have hg : d366866 p = 1 := by simpa only [d366867, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46291 p hg
    simpa only [d366867, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366867, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45395 p hg
    simpa only [d366867, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46293 (p : Pattern) (guard : d32698 p = 1) : d47629 p ≤ (7 : Int) + d2 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2002 p = 1 := by simpa only [d32698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45700 p hg
    simpa only [d32698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d32698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45381 p hg
    simpa only [d32698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46294 (p : Pattern) (guard : d366868 p = 1) : d47629 p ≤ (7 : Int) + d2 p := by
  cases selected : p 223 with
  | false =>
    have hg : d32698 p = 1 := by simpa only [d366868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46293 p hg
    simpa only [d366868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32153 p = 1 := by simpa only [d366868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45974 p hg
    simpa only [d366868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46295 (p : Pattern) (guard : d0 p = 1) : d51182 p ≤ (7 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46296 (p : Pattern) (guard : d1086 p = 1) : d51183 p ≤ (7 : Int) + d2 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1085 p = 1 := by simpa only [d1086, d51183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45386 p hg
    simpa only [d1086, d51183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1086, d51183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46295 p hg
    simpa only [d1086, d51183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46297 (p : Pattern) (guard : d0 p = 1) : d51185 p ≤ (7 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46298 (p : Pattern) (guard : d9771 p = 1) : d51186 p ≤ (7 : Int) + d2 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1086 p = 1 := by simpa only [d9771, d51186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46296 p hg
    simpa only [d9771, d51186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9771, d51186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46297 p hg
    simpa only [d9771, d51186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46299 (p : Pattern) (guard : d32155 p = 1) : d51186 p ≤ (7 : Int) + d2 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d32155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45390 p hg
    simpa only [d32155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9771 p = 1 := by simpa only [d32155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46298 p hg
    simpa only [d32155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46300 (p : Pattern) (guard : d366869 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 204 with
  | false =>
    have hg : d366868 p = 1 := by simpa only [d366869, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46294 p hg
    simpa only [d366869, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32155 p = 1 := by simpa only [d366869, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46299 p hg
    simpa only [d366869, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46301 (p : Pattern) (guard : d366870 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d366869 p = 1 := by simpa only [d366870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46300 p hg
    simpa only [d366870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343144 p = 1 := by simpa only [d366870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46277 p hg
    simpa only [d366870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46302 (p : Pattern) (guard : d366871 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 201 with
  | false =>
    have hg : d366870 p = 1 := by simpa only [d366871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46301 p hg
    simpa only [d366871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45392 p hg
    simpa only [d366871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46303 (p : Pattern) (guard : d366872 p = 1) : d51277 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 182 with
  | false =>
    have hg : d366871 p = 1 := by simpa only [d366872, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46302 p hg
    simpa only [d366872, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366872, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45395 p hg
    simpa only [d366872, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46304 (p : Pattern) (guard : d366873 p = 1) : d51277 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 180 with
  | false =>
    have hg : d366867 p = 1 := by simpa only [d366873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46292 p hg
    simpa only [d366873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366872 p = 1 := by simpa only [d366873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46303 p hg
    simpa only [d366873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46305 (p : Pattern) (guard : d367087 p = 1) : d51529 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367087, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45380 p hg
    simpa only [d367087, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366873 p = 1 := by simpa only [d367087, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46304 p hg
    simpa only [d367087, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46306 (p : Pattern) (guard : d366874 p = 1) : d51530 p ≤ (7 : Int) + d338814 p := by
  cases selected : p 163 with
  | false =>
    have hg : d366873 p = 1 := by simpa only [d366874, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46109 p hg
    simpa only [d366874, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366874, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45400 p hg
    simpa only [d366874, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46307 (p : Pattern) (guard : d367088 p = 1) : d51531 p ≤ (7 : Int) + d338815 p := by
  cases selected : p 162 with
  | false =>
    have hg : d367087 p = 1 := by simpa only [d367088, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46305 p hg
    simpa only [d367088, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366874 p = 1 := by simpa only [d367088, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46306 p hg
    simpa only [d367088, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46308 (p : Pattern) (guard : d366875 p = 1) : d51291 p ≤ (7 : Int) + d338710 p := by
  have ha := bounds51291 p
  have hb := bounds338710 p
  omega
theorem compare46309 (p : Pattern) (guard : d367089 p = 1) : d51532 p ≤ (7 : Int) + d338816 p := by
  cases selected : p 161 with
  | false =>
    have hg : d367088 p = 1 := by simpa only [d367089, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46307 p hg
    simpa only [d367089, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366875 p = 1 := by simpa only [d367089, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46308 p hg
    simpa only [d367089, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46310 (p : Pattern) (guard : d367090 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d367089 p = 1 := by simpa only [d367090, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46309 p hg
    simpa only [d367090, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367090, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45405 p hg
    simpa only [d367090, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46311 (p : Pattern) (guard : d367091 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 159 with
  | false =>
    have hg : d367086 p = 1 := by simpa only [d367091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46287 p hg
    simpa only [d367091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367090 p = 1 := by simpa only [d367091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46310 p hg
    simpa only [d367091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46312 (p : Pattern) (guard : d308523 p = 1) : d47629 p ≤ (7 : Int) + d2 p := by
  cases selected : p 223 with
  | false =>
    have hg : d32698 p = 1 := by simpa only [d308523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46293 p hg
    simpa only [d308523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d308523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45381 p hg
    simpa only [d308523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46313 (p : Pattern) (guard : d308524 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 204 with
  | false =>
    have hg : d308523 p = 1 := by simpa only [d308524, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46312 p hg
    simpa only [d308524, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d308524, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45390 p hg
    simpa only [d308524, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46314 (p : Pattern) (guard : d366879 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d34782 p = 1 := by simpa only [d366879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46264 p hg
    simpa only [d366879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d308524 p = 1 := by simpa only [d366879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46313 p hg
    simpa only [d366879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46315 (p : Pattern) (guard : d366880 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 201 with
  | false =>
    have hg : d366879 p = 1 := by simpa only [d366880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46314 p hg
    simpa only [d366880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45392 p hg
    simpa only [d366880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46316 (p : Pattern) (guard : d366881 p = 1) : d51277 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 182 with
  | false =>
    have hg : d366880 p = 1 := by simpa only [d366881, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46315 p hg
    simpa only [d366881, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366881, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45395 p hg
    simpa only [d366881, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46317 (p : Pattern) (guard : d366882 p = 1) : d51277 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 180 with
  | false =>
    have hg : d366881 p = 1 := by simpa only [d366882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46316 p hg
    simpa only [d366882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366872 p = 1 := by simpa only [d366882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46303 p hg
    simpa only [d366882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46318 (p : Pattern) (guard : d367077 p = 1) : d51529 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367077, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45380 p hg
    simpa only [d367077, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366882 p = 1 := by simpa only [d367077, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46317 p hg
    simpa only [d367077, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46319 (p : Pattern) (guard : d366883 p = 1) : d51530 p ≤ (7 : Int) + d338814 p := by
  cases selected : p 163 with
  | false =>
    have hg : d366882 p = 1 := by simpa only [d366883, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46120 p hg
    simpa only [d366883, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366883, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45400 p hg
    simpa only [d366883, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46320 (p : Pattern) (guard : d367078 p = 1) : d51531 p ≤ (7 : Int) + d338815 p := by
  cases selected : p 162 with
  | false =>
    have hg : d367077 p = 1 := by simpa only [d367078, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46318 p hg
    simpa only [d367078, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366883 p = 1 := by simpa only [d367078, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46319 p hg
    simpa only [d367078, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46321 (p : Pattern) (guard : d366884 p = 1) : d51291 p ≤ (7 : Int) + d338710 p := by
  have ha := bounds51291 p
  have hb := bounds338710 p
  omega
theorem compare46322 (p : Pattern) (guard : d367079 p = 1) : d51532 p ≤ (7 : Int) + d338816 p := by
  cases selected : p 161 with
  | false =>
    have hg : d367078 p = 1 := by simpa only [d367079, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46320 p hg
    simpa only [d367079, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366884 p = 1 := by simpa only [d367079, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46321 p hg
    simpa only [d367079, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46323 (p : Pattern) (guard : d367080 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d367079 p = 1 := by simpa only [d367080, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46322 p hg
    simpa only [d367080, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367080, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45405 p hg
    simpa only [d367080, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46324 (p : Pattern) (guard : d366887 p = 1) : d47629 p ≤ (7 : Int) + d2 p := by
  cases selected : p 223 with
  | false =>
    have hg : d43867 p = 1 := by simpa only [d366887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46271 p hg
    simpa only [d366887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32153 p = 1 := by simpa only [d366887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45974 p hg
    simpa only [d366887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46325 (p : Pattern) (guard : d366888 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 204 with
  | false =>
    have hg : d366887 p = 1 := by simpa only [d366888, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46324 p hg
    simpa only [d366888, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32155 p = 1 := by simpa only [d366888, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46299 p hg
    simpa only [d366888, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46326 (p : Pattern) (guard : d366889 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d366888 p = 1 := by simpa only [d366889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46325 p hg
    simpa only [d366889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343144 p = 1 := by simpa only [d366889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46277 p hg
    simpa only [d366889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46327 (p : Pattern) (guard : d343638 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d343144 p = 1 := by simpa only [d343638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46277 p hg
    simpa only [d343638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45392 p hg
    simpa only [d343638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46328 (p : Pattern) (guard : d366890 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 201 with
  | false =>
    have hg : d366889 p = 1 := by simpa only [d366890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46326 p hg
    simpa only [d366890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343638 p = 1 := by simpa only [d366890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46327 p hg
    simpa only [d366890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46329 (p : Pattern) (guard : d366891 p = 1) : d51277 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 182 with
  | false =>
    have hg : d366890 p = 1 := by simpa only [d366891, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46328 p hg
    simpa only [d366891, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366891, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45395 p hg
    simpa only [d366891, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46330 (p : Pattern) (guard : d366892 p = 1) : d51277 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 180 with
  | false =>
    have hg : d366891 p = 1 := by simpa only [d366892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46329 p hg
    simpa only [d366892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45397 p hg
    simpa only [d366892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46331 (p : Pattern) (guard : d367092 p = 1) : d51529 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367092, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45380 p hg
    simpa only [d367092, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366892 p = 1 := by simpa only [d367092, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46330 p hg
    simpa only [d367092, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46332 (p : Pattern) (guard : d366893 p = 1) : d51530 p ≤ (7 : Int) + d338814 p := by
  cases selected : p 163 with
  | false =>
    have hg : d366892 p = 1 := by simpa only [d366893, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46131 p hg
    simpa only [d366893, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366893, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45400 p hg
    simpa only [d366893, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46333 (p : Pattern) (guard : d367093 p = 1) : d51531 p ≤ (7 : Int) + d338815 p := by
  cases selected : p 162 with
  | false =>
    have hg : d367092 p = 1 := by simpa only [d367093, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46331 p hg
    simpa only [d367093, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366893 p = 1 := by simpa only [d367093, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46332 p hg
    simpa only [d367093, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46334 (p : Pattern) (guard : d366894 p = 1) : d51291 p ≤ (7 : Int) + d338710 p := by
  have ha := bounds51291 p
  have hb := bounds338710 p
  omega
theorem compare46335 (p : Pattern) (guard : d367094 p = 1) : d51532 p ≤ (7 : Int) + d338816 p := by
  cases selected : p 161 with
  | false =>
    have hg : d367093 p = 1 := by simpa only [d367094, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46333 p hg
    simpa only [d367094, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366894 p = 1 := by simpa only [d367094, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46334 p hg
    simpa only [d367094, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46336 (p : Pattern) (guard : d367095 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d367094 p = 1 := by simpa only [d367095, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46335 p hg
    simpa only [d367095, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367095, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45405 p hg
    simpa only [d367095, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46337 (p : Pattern) (guard : d367096 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 159 with
  | false =>
    have hg : d367080 p = 1 := by simpa only [d367096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46323 p hg
    simpa only [d367096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367095 p = 1 := by simpa only [d367096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46336 p hg
    simpa only [d367096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46338 (p : Pattern) (guard : d367097 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 158 with
  | false =>
    have hg : d367091 p = 1 := by simpa only [d367097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46311 p hg
    simpa only [d367097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367096 p = 1 := by simpa only [d367097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46337 p hg
    simpa only [d367097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46339 (p : Pattern) (guard : d366899 p = 1) : d51277 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 180 with
  | false =>
    have hg : d366867 p = 1 := by simpa only [d366899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46292 p hg
    simpa only [d366899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366891 p = 1 := by simpa only [d366899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46329 p hg
    simpa only [d366899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46340 (p : Pattern) (guard : d367112 p = 1) : d51529 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367112, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45380 p hg
    simpa only [d367112, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366899 p = 1 := by simpa only [d367112, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46339 p hg
    simpa only [d367112, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46341 (p : Pattern) (guard : d366900 p = 1) : d51530 p ≤ (7 : Int) + d338814 p := by
  cases selected : p 163 with
  | false =>
    have hg : d366899 p = 1 := by simpa only [d366900, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46138 p hg
    simpa only [d366900, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366900, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45400 p hg
    simpa only [d366900, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46342 (p : Pattern) (guard : d367113 p = 1) : d51531 p ≤ (7 : Int) + d338815 p := by
  cases selected : p 162 with
  | false =>
    have hg : d367112 p = 1 := by simpa only [d367113, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46340 p hg
    simpa only [d367113, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366900 p = 1 := by simpa only [d367113, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46341 p hg
    simpa only [d367113, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46343 (p : Pattern) (guard : d366901 p = 1) : d51291 p ≤ (7 : Int) + d338710 p := by
  have ha := bounds51291 p
  have hb := bounds338710 p
  omega
theorem compare46344 (p : Pattern) (guard : d367114 p = 1) : d51532 p ≤ (7 : Int) + d338816 p := by
  cases selected : p 161 with
  | false =>
    have hg : d367113 p = 1 := by simpa only [d367114, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46342 p hg
    simpa only [d367114, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366901 p = 1 := by simpa only [d367114, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46343 p hg
    simpa only [d367114, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46345 (p : Pattern) (guard : d367115 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d367114 p = 1 := by simpa only [d367115, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46344 p hg
    simpa only [d367115, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367115, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45405 p hg
    simpa only [d367115, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46346 (p : Pattern) (guard : d367116 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 159 with
  | false =>
    have hg : d367115 p = 1 := by simpa only [d367116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46345 p hg
    simpa only [d367116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367095 p = 1 := by simpa only [d367116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46336 p hg
    simpa only [d367116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46347 (p : Pattern) (guard : d367106 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 159 with
  | false =>
    have hg : d367095 p = 1 := by simpa only [d367106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46336 p hg
    simpa only [d367106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45407 p hg
    simpa only [d367106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46348 (p : Pattern) (guard : d367117 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 158 with
  | false =>
    have hg : d367116 p = 1 := by simpa only [d367117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46346 p hg
    simpa only [d367117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367106 p = 1 := by simpa only [d367117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46347 p hg
    simpa only [d367117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46349 (p : Pattern) (guard : d367118 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 157 with
  | false =>
    have hg : d367097 p = 1 := by simpa only [d367118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46338 p hg
    simpa only [d367118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367117 p = 1 := by simpa only [d367118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46348 p hg
    simpa only [d367118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46350 (p : Pattern) (guard : d367119 p = 1) : d51537 p ≤ (7 : Int) + d338821 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367119, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45379 p hg
    simpa only [d367119, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367118 p = 1 := by simpa only [d367119, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46349 p hg
    simpa only [d367119, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46351 (p : Pattern) (guard : d367120 p = 1) : d51538 p ≤ (7 : Int) + d338822 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367120, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45378 p hg
    simpa only [d367120, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367119 p = 1 := by simpa only [d367120, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46350 p hg
    simpa only [d367120, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46352 (p : Pattern) (guard : d367121 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 158 with
  | false =>
    have hg : d367106 p = 1 := by simpa only [d367121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46347 p hg
    simpa only [d367121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45407 p hg
    simpa only [d367121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46353 (p : Pattern) (guard : d367122 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 157 with
  | false =>
    have hg : d367117 p = 1 := by simpa only [d367122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46348 p hg
    simpa only [d367122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367121 p = 1 := by simpa only [d367122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46352 p hg
    simpa only [d367122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46354 (p : Pattern) (guard : d367123 p = 1) : d51537 p ≤ (7 : Int) + d338821 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367123, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45379 p hg
    simpa only [d367123, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367122 p = 1 := by simpa only [d367123, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46353 p hg
    simpa only [d367123, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46355 (p : Pattern) (guard : d367124 p = 1) : d51538 p ≤ (7 : Int) + d338822 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367124, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45378 p hg
    simpa only [d367124, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367123 p = 1 := by simpa only [d367124, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46354 p hg
    simpa only [d367124, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46356 (p : Pattern) (guard : d367125 p = 1) : d51538 p ≤ (7 : Int) + d338822 p := by
  cases selected : p 136 with
  | false =>
    have hg : d367120 p = 1 := by simpa only [d367125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46351 p hg
    simpa only [d367125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367124 p = 1 := by simpa only [d367125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46355 p hg
    simpa only [d367125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46357 (p : Pattern) (guard : d367130 p = 1) : d51538 p ≤ (7 : Int) + d338822 p := by
  cases selected : p 136 with
  | false =>
    have hg : d367124 p = 1 := by simpa only [d367130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46355 p hg
    simpa only [d367130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45413 p hg
    simpa only [d367130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46358 (p : Pattern) (guard : d367131 p = 1) : d51538 p ≤ (7 : Int) + d338822 p := by
  cases selected : p 135 with
  | false =>
    have hg : d367125 p = 1 := by simpa only [d367131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46356 p hg
    simpa only [d367131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367130 p = 1 := by simpa only [d367131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46357 p hg
    simpa only [d367131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46359 (p : Pattern) (guard : d367132 p = 1) : d51538 p ≤ (7 : Int) + d338822 p := by
  cases selected : p 119 with
  | false =>
    have hg : d367131 p = 1 := by simpa only [d367132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46358 p hg
    simpa only [d367132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45413 p hg
    simpa only [d367132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46360 (p : Pattern) (guard : d367133 p = 1) : d51540 p ≤ (7 : Int) + d338824 p := by
  cases selected : p 116 with
  | false =>
    have hg : d367132 p = 1 := by simpa only [d367133, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46359 p hg
    simpa only [d367133, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367133, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45417 p hg
    simpa only [d367133, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46361 (p : Pattern) (guard : d367134 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367134, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45264 p hg
    simpa only [d367134, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367133 p = 1 := by simpa only [d367134, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46360 p hg
    simpa only [d367134, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46362 (p : Pattern) (guard : d367139 p = 1) : d51538 p ≤ (7 : Int) + d338822 p := by
  cases selected : p 135 with
  | false =>
    have hg : d367130 p = 1 := by simpa only [d367139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46357 p hg
    simpa only [d367139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45413 p hg
    simpa only [d367139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46363 (p : Pattern) (guard : d367140 p = 1) : d51538 p ≤ (7 : Int) + d338822 p := by
  cases selected : p 119 with
  | false =>
    have hg : d367139 p = 1 := by simpa only [d367140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46362 p hg
    simpa only [d367140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45413 p hg
    simpa only [d367140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46364 (p : Pattern) (guard : d367141 p = 1) : d51540 p ≤ (7 : Int) + d338824 p := by
  cases selected : p 116 with
  | false =>
    have hg : d367140 p = 1 := by simpa only [d367141, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46363 p hg
    simpa only [d367141, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367141, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45417 p hg
    simpa only [d367141, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46365 (p : Pattern) (guard : d367142 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367142, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45264 p hg
    simpa only [d367142, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367141 p = 1 := by simpa only [d367142, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46364 p hg
    simpa only [d367142, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46366 (p : Pattern) (guard : d367143 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 113 with
  | false =>
    have hg : d367134 p = 1 := by simpa only [d367143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46361 p hg
    simpa only [d367143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367142 p = 1 := by simpa only [d367143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46365 p hg
    simpa only [d367143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46367 (p : Pattern) (guard : d367144 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 96 with
  | false =>
    have hg : d367143 p = 1 := by simpa only [d367144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46366 p hg
    simpa only [d367144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d367144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46368 (p : Pattern) (guard : d367145 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 95 with
  | false =>
    have hg : d367144 p = 1 := by simpa only [d367145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46367 p hg
    simpa only [d367145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d367145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46369 (p : Pattern) (guard : d367146 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 93 with
  | false =>
    have hg : d367145 p = 1 := by simpa only [d367146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46368 p hg
    simpa only [d367146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d367146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46370 (p : Pattern) (guard : d367160 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 113 with
  | false =>
    have hg : d367142 p = 1 := by simpa only [d367160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46365 p hg
    simpa only [d367160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d367160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46371 (p : Pattern) (guard : d367161 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 96 with
  | false =>
    have hg : d367160 p = 1 := by simpa only [d367161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46370 p hg
    simpa only [d367161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d367161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46372 (p : Pattern) (guard : d367162 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 95 with
  | false =>
    have hg : d367161 p = 1 := by simpa only [d367162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46371 p hg
    simpa only [d367162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d367162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46373 (p : Pattern) (guard : d367163 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 93 with
  | false =>
    have hg : d367162 p = 1 := by simpa only [d367163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46372 p hg
    simpa only [d367163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d367163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46374 (p : Pattern) (guard : d367504 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 91 with
  | false =>
    have hg : d367146 p = 1 := by simpa only [d367504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46369 p hg
    simpa only [d367504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367163 p = 1 := by simpa only [d367504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46373 p hg
    simpa only [d367504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46375 (p : Pattern) (guard : d367505 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d367505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367504 p = 1 := by simpa only [d367505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46374 p hg
    simpa only [d367505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46376 (p : Pattern) (guard : d367506 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 89 with
  | false =>
    have hg : d367505 p = 1 := by simpa only [d367506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46375 p hg
    simpa only [d367506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d367506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46377 (p : Pattern) (guard : d367507 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d367507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367506 p = 1 := by simpa only [d367507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46376 p hg
    simpa only [d367507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46378 (p : Pattern) (guard : d367508 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d367508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367507 p = 1 := by simpa only [d367508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46377 p hg
    simpa only [d367508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46379 (p : Pattern) (guard : d367509 p = 1) : d51542 p ≤ (7 : Int) + d338826 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367509, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d367509, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367508 p = 1 := by simpa only [d367509, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46378 p hg
    simpa only [d367509, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46380 (p : Pattern) (guard : d367510 p = 1) : d51542 p ≤ (7 : Int) + d338826 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45376 p hg
    simpa only [d367510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367509 p = 1 := by simpa only [d367510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46379 p hg
    simpa only [d367510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46381 (p : Pattern) (guard : d367511 p = 1) : d51542 p ≤ (7 : Int) + d338826 p := by
  cases selected : p 69 with
  | false =>
    have hg : d367510 p = 1 := by simpa only [d367511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46380 p hg
    simpa only [d367511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45376 p hg
    simpa only [d367511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46382 (p : Pattern) (guard : d367512 p = 1) : d51542 p ≤ (7 : Int) + d338826 p := by
  cases selected : p 51 with
  | false =>
    have hg : d367511 p = 1 := by simpa only [d367512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46381 p hg
    simpa only [d367512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45376 p hg
    simpa only [d367512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46383 (p : Pattern) (guard : d367513 p = 1) : d51542 p ≤ (7 : Int) + d338826 p := by
  cases selected : p 50 with
  | false =>
    have hg : d367512 p = 1 := by simpa only [d367513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46382 p hg
    simpa only [d367513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45376 p hg
    simpa only [d367513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46384 (p : Pattern) (guard : d367514 p = 1) : d51634 p ≤ (7 : Int) + d338882 p := by
  cases selected : p 49 with
  | false =>
    have hg : d367513 p = 1 := by simpa only [d367514, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46383 p hg
    simpa only [d367514, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367514, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45434 p hg
    simpa only [d367514, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46385 (p : Pattern) (guard : d367515 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 48 with
  | false =>
    have hg : d367503 p = 1 := by simpa only [d367515, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46260 p hg
    simpa only [d367515, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367514 p = 1 := by simpa only [d367515, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46384 p hg
    simpa only [d367515, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46386 (p : Pattern) (guard : d367516 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367515 p = 1 := by simpa only [d367516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46385 p hg
    simpa only [d367516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46387 (p : Pattern) (guard : d367517 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367516 p = 1 := by simpa only [d367517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46386 p hg
    simpa only [d367517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46388 (p : Pattern) (guard : d367518 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367517 p = 1 := by simpa only [d367518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46387 p hg
    simpa only [d367518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46389 (p : Pattern) (guard : d367519 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367518 p = 1 := by simpa only [d367519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46388 p hg
    simpa only [d367519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46390 (p : Pattern) (guard : d367520 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367519 p = 1 := by simpa only [d367520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46389 p hg
    simpa only [d367520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46391 (p : Pattern) (guard : d367521 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367520 p = 1 := by simpa only [d367521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46390 p hg
    simpa only [d367521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46392 (p : Pattern) (guard : d367522 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367521 p = 1 := by simpa only [d367522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46391 p hg
    simpa only [d367522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46393 (p : Pattern) (guard : d367523 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367522 p = 1 := by simpa only [d367523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46392 p hg
    simpa only [d367523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46394 (p : Pattern) (guard : d367524 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367523 p = 1 := by simpa only [d367524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46393 p hg
    simpa only [d367524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46395 (p : Pattern) (guard : d367525 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d367495 p = 1 := by simpa only [d367525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46067 p hg
    simpa only [d367525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367524 p = 1 := by simpa only [d367525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46394 p hg
    simpa only [d367525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46396 (p : Pattern) (guard : d35372 p = 1) : d47616 p ≤ (7 : Int) + d4 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d35372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45268 p hg
    simpa only [d35372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32698 p = 1 := by simpa only [d35372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46098 p hg
    simpa only [d35372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46397 (p : Pattern) (guard : d2006 p = 1) : d51201 p ≤ (7 : Int) + d4 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2005 p = 1 := by simpa only [d2006, d51201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45581 p hg
    simpa only [d2006, d51201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2006, d51201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46100 p hg
    simpa only [d2006, d51201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46398 (p : Pattern) (guard : d10054 p = 1) : d51203 p ≤ (7 : Int) + d4 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2006 p = 1 := by simpa only [d10054, d51203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46397 p hg
    simpa only [d10054, d51203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10054, d51203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46102 p hg
    simpa only [d10054, d51203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46399 (p : Pattern) (guard : d10055 p = 1) : d51203 p ≤ (7 : Int) + d4 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45277 p hg
    simpa only [d10055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10054 p = 1 := by simpa only [d10055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46398 p hg
    simpa only [d10055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46400 (p : Pattern) (guard : d35373 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 204 with
  | false =>
    have hg : d35372 p = 1 := by simpa only [d35373, d51204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46396 p hg
    simpa only [d35373, d51204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10055 p = 1 := by simpa only [d35373, d51204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46399 p hg
    simpa only [d35373, d51204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46401 (p : Pattern) (guard : d44441 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 202 with
  | false =>
    have hg : d35373 p = 1 := by simpa only [d44441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46400 p hg
    simpa only [d44441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45279 p hg
    simpa only [d44441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46402 (p : Pattern) (guard : d44442 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 201 with
  | false =>
    have hg : d44441 p = 1 := by simpa only [d44442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46401 p hg
    simpa only [d44442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45279 p hg
    simpa only [d44442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46403 (p : Pattern) (guard : d44443 p = 1) : d51269 p ≤ (7 : Int) + d338656 p := by
  cases selected : p 182 with
  | false =>
    have hg : d44442 p = 1 := by simpa only [d44443, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46402 p hg
    simpa only [d44443, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44443, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45282 p hg
    simpa only [d44443, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46404 (p : Pattern) (guard : d44444 p = 1) : d51269 p ≤ (7 : Int) + d338656 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d44444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45284 p hg
    simpa only [d44444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44443 p = 1 := by simpa only [d44444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46403 p hg
    simpa only [d44444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46405 (p : Pattern) (guard : d44445 p = 1) : d51287 p ≤ (7 : Int) + d338687 p := by
  cases selected : p 163 with
  | false =>
    have hg : d44444 p = 1 := by simpa only [d44445, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46404 p hg
    simpa only [d44445, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44445, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45286 p hg
    simpa only [d44445, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46406 (p : Pattern) (guard : d44446 p = 1) : d51288 p ≤ (7 : Int) + d338690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d44445 p = 1 := by simpa only [d44446, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46405 p hg
    simpa only [d44446, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44446, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45288 p hg
    simpa only [d44446, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46407 (p : Pattern) (guard : d44447 p = 1) : d51289 p ≤ (7 : Int) + d338691 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d44447, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45267 p hg
    simpa only [d44447, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44446 p = 1 := by simpa only [d44447, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46406 p hg
    simpa only [d44447, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46408 (p : Pattern) (guard : d44448 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 160 with
  | false =>
    have hg : d44447 p = 1 := by simpa only [d44448, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46407 p hg
    simpa only [d44448, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44448, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45291 p hg
    simpa only [d44448, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46409 (p : Pattern) (guard : d44449 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d44449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45293 p hg
    simpa only [d44449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44448 p = 1 := by simpa only [d44449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46408 p hg
    simpa only [d44449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46410 (p : Pattern) (guard : d44609 p = 1) : d51269 p ≤ (7 : Int) + d338656 p := by
  cases selected : p 180 with
  | false =>
    have hg : d44443 p = 1 := by simpa only [d44609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46403 p hg
    simpa only [d44609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45284 p hg
    simpa only [d44609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46411 (p : Pattern) (guard : d44610 p = 1) : d51287 p ≤ (7 : Int) + d338687 p := by
  cases selected : p 163 with
  | false =>
    have hg : d44609 p = 1 := by simpa only [d44610, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46410 p hg
    simpa only [d44610, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44610, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45286 p hg
    simpa only [d44610, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46412 (p : Pattern) (guard : d44611 p = 1) : d51288 p ≤ (7 : Int) + d338690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d44610 p = 1 := by simpa only [d44611, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46411 p hg
    simpa only [d44611, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44611, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45288 p hg
    simpa only [d44611, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46413 (p : Pattern) (guard : d44612 p = 1) : d51289 p ≤ (7 : Int) + d338691 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d44612, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45267 p hg
    simpa only [d44612, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44611 p = 1 := by simpa only [d44612, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46412 p hg
    simpa only [d44612, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46414 (p : Pattern) (guard : d44613 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 160 with
  | false =>
    have hg : d44612 p = 1 := by simpa only [d44613, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46413 p hg
    simpa only [d44613, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44613, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45291 p hg
    simpa only [d44613, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46415 (p : Pattern) (guard : d367186 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 159 with
  | false =>
    have hg : d44448 p = 1 := by simpa only [d367186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46408 p hg
    simpa only [d367186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44613 p = 1 := by simpa only [d367186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46414 p hg
    simpa only [d367186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46416 (p : Pattern) (guard : d367187 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 158 with
  | false =>
    have hg : d44449 p = 1 := by simpa only [d367187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46409 p hg
    simpa only [d367187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367186 p = 1 := by simpa only [d367187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46415 p hg
    simpa only [d367187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46417 (p : Pattern) (guard : d44614 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 159 with
  | false =>
    have hg : d44613 p = 1 := by simpa only [d44614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46414 p hg
    simpa only [d44614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45293 p hg
    simpa only [d44614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46418 (p : Pattern) (guard : d367188 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 158 with
  | false =>
    have hg : d367186 p = 1 := by simpa only [d367188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46415 p hg
    simpa only [d367188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44614 p = 1 := by simpa only [d367188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46417 p hg
    simpa only [d367188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46419 (p : Pattern) (guard : d367189 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 157 with
  | false =>
    have hg : d367187 p = 1 := by simpa only [d367189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46416 p hg
    simpa only [d367189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367188 p = 1 := by simpa only [d367189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46418 p hg
    simpa only [d367189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46420 (p : Pattern) (guard : d367190 p = 1) : d51294 p ≤ (7 : Int) + d338713 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367190, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45266 p hg
    simpa only [d367190, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367189 p = 1 := by simpa only [d367190, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46419 p hg
    simpa only [d367190, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46421 (p : Pattern) (guard : d367191 p = 1) : d51314 p ≤ (7 : Int) + d338714 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367191, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45265 p hg
    simpa only [d367191, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367190 p = 1 := by simpa only [d367191, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46420 p hg
    simpa only [d367191, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46422 (p : Pattern) (guard : d44616 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 158 with
  | false =>
    have hg : d44614 p = 1 := by simpa only [d44616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46417 p hg
    simpa only [d44616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45293 p hg
    simpa only [d44616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46423 (p : Pattern) (guard : d367192 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 157 with
  | false =>
    have hg : d367188 p = 1 := by simpa only [d367192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46418 p hg
    simpa only [d367192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44616 p = 1 := by simpa only [d367192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46422 p hg
    simpa only [d367192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46424 (p : Pattern) (guard : d367193 p = 1) : d51294 p ≤ (7 : Int) + d338713 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367193, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45266 p hg
    simpa only [d367193, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367192 p = 1 := by simpa only [d367193, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46423 p hg
    simpa only [d367193, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46425 (p : Pattern) (guard : d367194 p = 1) : d51314 p ≤ (7 : Int) + d338714 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367194, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45265 p hg
    simpa only [d367194, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367193 p = 1 := by simpa only [d367194, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46424 p hg
    simpa only [d367194, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46426 (p : Pattern) (guard : d367195 p = 1) : d51314 p ≤ (7 : Int) + d338714 p := by
  cases selected : p 136 with
  | false =>
    have hg : d367191 p = 1 := by simpa only [d367195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46421 p hg
    simpa only [d367195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367194 p = 1 := by simpa only [d367195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46425 p hg
    simpa only [d367195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46427 (p : Pattern) (guard : d367196 p = 1) : d51314 p ≤ (7 : Int) + d338714 p := by
  cases selected : p 136 with
  | false =>
    have hg : d367194 p = 1 := by simpa only [d367196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46425 p hg
    simpa only [d367196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45299 p hg
    simpa only [d367196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46428 (p : Pattern) (guard : d367197 p = 1) : d51314 p ≤ (7 : Int) + d338714 p := by
  cases selected : p 135 with
  | false =>
    have hg : d367195 p = 1 := by simpa only [d367197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46426 p hg
    simpa only [d367197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367196 p = 1 := by simpa only [d367197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46427 p hg
    simpa only [d367197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46429 (p : Pattern) (guard : d367198 p = 1) : d51314 p ≤ (7 : Int) + d338714 p := by
  cases selected : p 119 with
  | false =>
    have hg : d367197 p = 1 := by simpa only [d367198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46428 p hg
    simpa only [d367198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45299 p hg
    simpa only [d367198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46430 (p : Pattern) (guard : d367199 p = 1) : d51316 p ≤ (7 : Int) + d338726 p := by
  cases selected : p 116 with
  | false =>
    have hg : d367198 p = 1 := by simpa only [d367199, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46429 p hg
    simpa only [d367199, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367199, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45303 p hg
    simpa only [d367199, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46431 (p : Pattern) (guard : d367200 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367200, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45264 p hg
    simpa only [d367200, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367199 p = 1 := by simpa only [d367200, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46430 p hg
    simpa only [d367200, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46432 (p : Pattern) (guard : d367201 p = 1) : d51314 p ≤ (7 : Int) + d338714 p := by
  cases selected : p 135 with
  | false =>
    have hg : d367196 p = 1 := by simpa only [d367201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46427 p hg
    simpa only [d367201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45299 p hg
    simpa only [d367201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46433 (p : Pattern) (guard : d367202 p = 1) : d51314 p ≤ (7 : Int) + d338714 p := by
  cases selected : p 119 with
  | false =>
    have hg : d367201 p = 1 := by simpa only [d367202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46432 p hg
    simpa only [d367202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45299 p hg
    simpa only [d367202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46434 (p : Pattern) (guard : d367203 p = 1) : d51316 p ≤ (7 : Int) + d338726 p := by
  cases selected : p 116 with
  | false =>
    have hg : d367202 p = 1 := by simpa only [d367203, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46433 p hg
    simpa only [d367203, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367203, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45303 p hg
    simpa only [d367203, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46435 (p : Pattern) (guard : d367204 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367204, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45264 p hg
    simpa only [d367204, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367203 p = 1 := by simpa only [d367204, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46434 p hg
    simpa only [d367204, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46436 (p : Pattern) (guard : d367205 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d367200 p = 1 := by simpa only [d367205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46431 p hg
    simpa only [d367205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367204 p = 1 := by simpa only [d367205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46435 p hg
    simpa only [d367205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46437 (p : Pattern) (guard : d367206 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d367205 p = 1 := by simpa only [d367206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46436 p hg
    simpa only [d367206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d367206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46438 (p : Pattern) (guard : d367207 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d367206 p = 1 := by simpa only [d367207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46437 p hg
    simpa only [d367207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d367207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46439 (p : Pattern) (guard : d367208 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d367208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367207 p = 1 := by simpa only [d367208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46438 p hg
    simpa only [d367208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46440 (p : Pattern) (guard : d367209 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d367204 p = 1 := by simpa only [d367209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46435 p hg
    simpa only [d367209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d367209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46441 (p : Pattern) (guard : d367210 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d367209 p = 1 := by simpa only [d367210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46440 p hg
    simpa only [d367210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d367210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46442 (p : Pattern) (guard : d367211 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d367210 p = 1 := by simpa only [d367211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46441 p hg
    simpa only [d367211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d367211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46443 (p : Pattern) (guard : d367212 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d367212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367211 p = 1 := by simpa only [d367212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46442 p hg
    simpa only [d367212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46444 (p : Pattern) (guard : d367213 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d367208 p = 1 := by simpa only [d367213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46439 p hg
    simpa only [d367213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367212 p = 1 := by simpa only [d367213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46443 p hg
    simpa only [d367213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46445 (p : Pattern) (guard : d367214 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d367214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367213 p = 1 := by simpa only [d367214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46444 p hg
    simpa only [d367214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46446 (p : Pattern) (guard : d367215 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d367214 p = 1 := by simpa only [d367215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46445 p hg
    simpa only [d367215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d367215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46447 (p : Pattern) (guard : d367216 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d367216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367215 p = 1 := by simpa only [d367216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46446 p hg
    simpa only [d367216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46448 (p : Pattern) (guard : d367217 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d367217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367216 p = 1 := by simpa only [d367217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46447 p hg
    simpa only [d367217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46449 (p : Pattern) (guard : d367218 p = 1) : d51331 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367218, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d367218, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367217 p = 1 := by simpa only [d367218, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46448 p hg
    simpa only [d367218, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46450 (p : Pattern) (guard : d367200 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367200, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45316 p hg
    simpa only [d367200, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367199 p = 1 := by simpa only [d367200, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46430 p hg
    simpa only [d367200, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46451 (p : Pattern) (guard : d367204 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367204, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45316 p hg
    simpa only [d367204, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367203 p = 1 := by simpa only [d367204, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46434 p hg
    simpa only [d367204, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46452 (p : Pattern) (guard : d367205 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d367200 p = 1 := by simpa only [d367205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46450 p hg
    simpa only [d367205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367204 p = 1 := by simpa only [d367205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46451 p hg
    simpa only [d367205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46453 (p : Pattern) (guard : d367206 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d367205 p = 1 := by simpa only [d367206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46452 p hg
    simpa only [d367206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d367206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46454 (p : Pattern) (guard : d367207 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d367206 p = 1 := by simpa only [d367207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46453 p hg
    simpa only [d367207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d367207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46455 (p : Pattern) (guard : d367208 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d367208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367207 p = 1 := by simpa only [d367208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46454 p hg
    simpa only [d367208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46456 (p : Pattern) (guard : d367209 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d367204 p = 1 := by simpa only [d367209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46451 p hg
    simpa only [d367209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d367209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46457 (p : Pattern) (guard : d367210 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d367209 p = 1 := by simpa only [d367210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46456 p hg
    simpa only [d367210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d367210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46458 (p : Pattern) (guard : d367211 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d367210 p = 1 := by simpa only [d367211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46457 p hg
    simpa only [d367211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d367211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46459 (p : Pattern) (guard : d367212 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d367212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367211 p = 1 := by simpa only [d367212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46458 p hg
    simpa only [d367212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46460 (p : Pattern) (guard : d367213 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d367208 p = 1 := by simpa only [d367213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46455 p hg
    simpa only [d367213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367212 p = 1 := by simpa only [d367213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46459 p hg
    simpa only [d367213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46461 (p : Pattern) (guard : d367214 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d367214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367213 p = 1 := by simpa only [d367214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46460 p hg
    simpa only [d367214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46462 (p : Pattern) (guard : d367215 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d367214 p = 1 := by simpa only [d367215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46461 p hg
    simpa only [d367215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d367215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46463 (p : Pattern) (guard : d367216 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d367216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367215 p = 1 := by simpa only [d367216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46462 p hg
    simpa only [d367216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46464 (p : Pattern) (guard : d367217 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d367217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367216 p = 1 := by simpa only [d367217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46463 p hg
    simpa only [d367217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46465 (p : Pattern) (guard : d367221 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d367207 p = 1 := by simpa only [d367221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46438 p hg
    simpa only [d367221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d367221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46466 (p : Pattern) (guard : d367222 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d367211 p = 1 := by simpa only [d367222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46442 p hg
    simpa only [d367222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d367222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46467 (p : Pattern) (guard : d367223 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d367221 p = 1 := by simpa only [d367223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46465 p hg
    simpa only [d367223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367222 p = 1 := by simpa only [d367223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46466 p hg
    simpa only [d367223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46468 (p : Pattern) (guard : d367224 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d367224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367223 p = 1 := by simpa only [d367224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46467 p hg
    simpa only [d367224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46469 (p : Pattern) (guard : d367225 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d367224 p = 1 := by simpa only [d367225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46468 p hg
    simpa only [d367225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d367225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46470 (p : Pattern) (guard : d367226 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d367226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367225 p = 1 := by simpa only [d367226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46469 p hg
    simpa only [d367226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46471 (p : Pattern) (guard : d367227 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d367227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367226 p = 1 := by simpa only [d367227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46470 p hg
    simpa only [d367227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46472 (p : Pattern) (guard : d367228 p = 1) : d51331 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d367217 p = 1 := by simpa only [d367228, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46464 p hg
    simpa only [d367228, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367227 p = 1 := by simpa only [d367228, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46471 p hg
    simpa only [d367228, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46473 (p : Pattern) (guard : d367229 p = 1) : d51331 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 70 with
  | false =>
    have hg : d367218 p = 1 := by simpa only [d367229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46449 p hg
    simpa only [d367229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367228 p = 1 := by simpa only [d367229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46472 p hg
    simpa only [d367229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46474 (p : Pattern) (guard : d367230 p = 1) : d51331 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 69 with
  | false =>
    have hg : d367229 p = 1 := by simpa only [d367230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46473 p hg
    simpa only [d367230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45261 p hg
    simpa only [d367230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46475 (p : Pattern) (guard : d367526 p = 1) : d51331 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 51 with
  | false =>
    have hg : d367230 p = 1 := by simpa only [d367526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46474 p hg
    simpa only [d367526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45261 p hg
    simpa only [d367526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46476 (p : Pattern) (guard : d367527 p = 1) : d51331 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45261 p hg
    simpa only [d367527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367526 p = 1 := by simpa only [d367527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46475 p hg
    simpa only [d367527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46477 (p : Pattern) (guard : d44446 p = 1) : d51447 p ≤ (7 : Int) + d338755 p := by
  have ha := bounds51447 p
  have hb := bounds338755 p
  omega
theorem compare46478 (p : Pattern) (guard : d44447 p = 1) : d51448 p ≤ (7 : Int) + d338756 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d44447, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45343 p hg
    simpa only [d44447, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44446 p = 1 := by simpa only [d44447, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46477 p hg
    simpa only [d44447, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46479 (p : Pattern) (guard : d44448 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d44447 p = 1 := by simpa only [d44448, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46478 p hg
    simpa only [d44448, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44448, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45346 p hg
    simpa only [d44448, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46480 (p : Pattern) (guard : d44449 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d44449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45348 p hg
    simpa only [d44449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44448 p = 1 := by simpa only [d44449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46479 p hg
    simpa only [d44449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46481 (p : Pattern) (guard : d44611 p = 1) : d51447 p ≤ (7 : Int) + d338755 p := by
  have ha := bounds51447 p
  have hb := bounds338755 p
  omega
theorem compare46482 (p : Pattern) (guard : d44612 p = 1) : d51448 p ≤ (7 : Int) + d338756 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d44612, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45343 p hg
    simpa only [d44612, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44611 p = 1 := by simpa only [d44612, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46481 p hg
    simpa only [d44612, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46483 (p : Pattern) (guard : d44613 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d44612 p = 1 := by simpa only [d44613, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46482 p hg
    simpa only [d44613, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44613, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45346 p hg
    simpa only [d44613, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46484 (p : Pattern) (guard : d367186 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 159 with
  | false =>
    have hg : d44448 p = 1 := by simpa only [d367186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46479 p hg
    simpa only [d367186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44613 p = 1 := by simpa only [d367186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46483 p hg
    simpa only [d367186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46485 (p : Pattern) (guard : d367187 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 158 with
  | false =>
    have hg : d44449 p = 1 := by simpa only [d367187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46480 p hg
    simpa only [d367187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367186 p = 1 := by simpa only [d367187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46484 p hg
    simpa only [d367187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46486 (p : Pattern) (guard : d44614 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 159 with
  | false =>
    have hg : d44613 p = 1 := by simpa only [d44614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46483 p hg
    simpa only [d44614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45348 p hg
    simpa only [d44614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46487 (p : Pattern) (guard : d367188 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 158 with
  | false =>
    have hg : d367186 p = 1 := by simpa only [d367188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46484 p hg
    simpa only [d367188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44614 p = 1 := by simpa only [d367188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46486 p hg
    simpa only [d367188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46488 (p : Pattern) (guard : d367189 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 157 with
  | false =>
    have hg : d367187 p = 1 := by simpa only [d367189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46485 p hg
    simpa only [d367189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367188 p = 1 := by simpa only [d367189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46487 p hg
    simpa only [d367189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46489 (p : Pattern) (guard : d367190 p = 1) : d51453 p ≤ (7 : Int) + d338775 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367190, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45342 p hg
    simpa only [d367190, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367189 p = 1 := by simpa only [d367190, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46488 p hg
    simpa only [d367190, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46490 (p : Pattern) (guard : d367191 p = 1) : d51465 p ≤ (7 : Int) + d338776 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367191, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45341 p hg
    simpa only [d367191, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367190 p = 1 := by simpa only [d367191, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46489 p hg
    simpa only [d367191, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46491 (p : Pattern) (guard : d44616 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 158 with
  | false =>
    have hg : d44614 p = 1 := by simpa only [d44616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46486 p hg
    simpa only [d44616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45348 p hg
    simpa only [d44616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46492 (p : Pattern) (guard : d367192 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 157 with
  | false =>
    have hg : d367188 p = 1 := by simpa only [d367192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46487 p hg
    simpa only [d367192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44616 p = 1 := by simpa only [d367192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46491 p hg
    simpa only [d367192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46493 (p : Pattern) (guard : d367193 p = 1) : d51453 p ≤ (7 : Int) + d338775 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367193, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45342 p hg
    simpa only [d367193, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367192 p = 1 := by simpa only [d367193, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46492 p hg
    simpa only [d367193, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46494 (p : Pattern) (guard : d367194 p = 1) : d51465 p ≤ (7 : Int) + d338776 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367194, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45341 p hg
    simpa only [d367194, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367193 p = 1 := by simpa only [d367194, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46493 p hg
    simpa only [d367194, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46495 (p : Pattern) (guard : d367195 p = 1) : d51465 p ≤ (7 : Int) + d338776 p := by
  cases selected : p 136 with
  | false =>
    have hg : d367191 p = 1 := by simpa only [d367195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46490 p hg
    simpa only [d367195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367194 p = 1 := by simpa only [d367195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46494 p hg
    simpa only [d367195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46496 (p : Pattern) (guard : d367196 p = 1) : d51465 p ≤ (7 : Int) + d338776 p := by
  cases selected : p 136 with
  | false =>
    have hg : d367194 p = 1 := by simpa only [d367196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46494 p hg
    simpa only [d367196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45354 p hg
    simpa only [d367196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46497 (p : Pattern) (guard : d367197 p = 1) : d51465 p ≤ (7 : Int) + d338776 p := by
  cases selected : p 135 with
  | false =>
    have hg : d367195 p = 1 := by simpa only [d367197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46495 p hg
    simpa only [d367197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367196 p = 1 := by simpa only [d367197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46496 p hg
    simpa only [d367197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46498 (p : Pattern) (guard : d367198 p = 1) : d51465 p ≤ (7 : Int) + d338776 p := by
  cases selected : p 119 with
  | false =>
    have hg : d367197 p = 1 := by simpa only [d367198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46497 p hg
    simpa only [d367198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45354 p hg
    simpa only [d367198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46499 (p : Pattern) (guard : d367199 p = 1) : d51467 p ≤ (7 : Int) + d338784 p := by
  cases selected : p 116 with
  | false =>
    have hg : d367198 p = 1 := by simpa only [d367199, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46498 p hg
    simpa only [d367199, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367199, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45358 p hg
    simpa only [d367199, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
