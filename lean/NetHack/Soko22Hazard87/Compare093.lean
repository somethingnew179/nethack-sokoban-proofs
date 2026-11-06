import NetHack.Soko22Hazard87.Compare092
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare23250 (p : Pattern) (guard : d180232 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 250 with
  | false =>
    have hg : d180231 p = 1 := by simpa only [d180232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23249 p hg
    simpa only [d180232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23251 (p : Pattern) (guard : d180233 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 249 with
  | false =>
    have hg : d180232 p = 1 := by simpa only [d180233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23250 p hg
    simpa only [d180233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23252 (p : Pattern) (guard : d180234 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 245 with
  | false =>
    have hg : d180233 p = 1 := by simpa only [d180234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23251 p hg
    simpa only [d180234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23253 (p : Pattern) (guard : d180235 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 200 with
  | false =>
    have hg : d180234 p = 1 := by simpa only [d180235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23252 p hg
    simpa only [d180235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23254 (p : Pattern) (guard : d180236 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 199 with
  | false =>
    have hg : d180235 p = 1 := by simpa only [d180236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23253 p hg
    simpa only [d180236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23255 (p : Pattern) (guard : d180237 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 186 with
  | false =>
    have hg : d180236 p = 1 := by simpa only [d180237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23254 p hg
    simpa only [d180237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23256 (p : Pattern) (guard : d180238 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 185 with
  | false =>
    have hg : d180237 p = 1 := by simpa only [d180238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23255 p hg
    simpa only [d180238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23257 (p : Pattern) (guard : d180239 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 184 with
  | false =>
    have hg : d180238 p = 1 := by simpa only [d180239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23256 p hg
    simpa only [d180239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23258 (p : Pattern) (guard : d180240 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 181 with
  | false =>
    have hg : d180239 p = 1 := by simpa only [d180240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23257 p hg
    simpa only [d180240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23259 (p : Pattern) (guard : d180241 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 177 with
  | false =>
    have hg : d180240 p = 1 := by simpa only [d180241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23258 p hg
    simpa only [d180241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23260 (p : Pattern) (guard : d180242 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 164 with
  | false =>
    have hg : d180241 p = 1 := by simpa only [d180242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23259 p hg
    simpa only [d180242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23261 (p : Pattern) (guard : d180243 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 156 with
  | false =>
    have hg : d180242 p = 1 := by simpa only [d180243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23260 p hg
    simpa only [d180243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23262 (p : Pattern) (guard : d180244 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 155 with
  | false =>
    have hg : d180243 p = 1 := by simpa only [d180244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23261 p hg
    simpa only [d180244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23263 (p : Pattern) (guard : d180245 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 134 with
  | false =>
    have hg : d180244 p = 1 := by simpa only [d180245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23262 p hg
    simpa only [d180245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23264 (p : Pattern) (guard : d180246 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 133 with
  | false =>
    have hg : d180245 p = 1 := by simpa only [d180246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23263 p hg
    simpa only [d180246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23265 (p : Pattern) (guard : d180247 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 120 with
  | false =>
    have hg : d180246 p = 1 := by simpa only [d180247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23264 p hg
    simpa only [d180247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23266 (p : Pattern) (guard : d180248 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 118 with
  | false =>
    have hg : d180247 p = 1 := by simpa only [d180248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23265 p hg
    simpa only [d180248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23267 (p : Pattern) (guard : d180249 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 114 with
  | false =>
    have hg : d180248 p = 1 := by simpa only [d180249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23266 p hg
    simpa only [d180249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23268 (p : Pattern) (guard : d180250 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 111 with
  | false =>
    have hg : d180249 p = 1 := by simpa only [d180250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23267 p hg
    simpa only [d180250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23269 (p : Pattern) (guard : d180251 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 98 with
  | false =>
    have hg : d180250 p = 1 := by simpa only [d180251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23268 p hg
    simpa only [d180251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23270 (p : Pattern) (guard : d180252 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 97 with
  | false =>
    have hg : d180251 p = 1 := by simpa only [d180252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23269 p hg
    simpa only [d180252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23271 (p : Pattern) (guard : d180253 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 94 with
  | false =>
    have hg : d180252 p = 1 := by simpa only [d180253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23270 p hg
    simpa only [d180253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23272 (p : Pattern) (guard : d180254 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 76 with
  | false =>
    have hg : d180253 p = 1 := by simpa only [d180254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23271 p hg
    simpa only [d180254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23273 (p : Pattern) (guard : d180255 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 67 with
  | false =>
    have hg : d180254 p = 1 := by simpa only [d180255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23272 p hg
    simpa only [d180255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23274 (p : Pattern) (guard : d180256 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 52 with
  | false =>
    have hg : d180255 p = 1 := by simpa only [d180256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23273 p hg
    simpa only [d180256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23275 (p : Pattern) (guard : d180257 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 47 with
  | false =>
    have hg : d180256 p = 1 := by simpa only [d180257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23274 p hg
    simpa only [d180257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23276 (p : Pattern) (guard : d180258 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 46 with
  | false =>
    have hg : d180257 p = 1 := by simpa only [d180258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23275 p hg
    simpa only [d180258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23277 (p : Pattern) (guard : d180259 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 45 with
  | false =>
    have hg : d180258 p = 1 := by simpa only [d180259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23276 p hg
    simpa only [d180259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23278 (p : Pattern) (guard : d180260 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 30 with
  | false =>
    have hg : d180259 p = 1 := by simpa only [d180260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23277 p hg
    simpa only [d180260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23279 (p : Pattern) (guard : d180261 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 29 with
  | false =>
    have hg : d180260 p = 1 := by simpa only [d180261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23278 p hg
    simpa only [d180261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23280 (p : Pattern) (guard : d180262 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 28 with
  | false =>
    have hg : d180261 p = 1 := by simpa only [d180262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23279 p hg
    simpa only [d180262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23281 (p : Pattern) (guard : d180263 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 27 with
  | false =>
    have hg : d180262 p = 1 := by simpa only [d180263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23280 p hg
    simpa only [d180263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23282 (p : Pattern) (guard : d180264 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 25 with
  | false =>
    have hg : d180263 p = 1 := by simpa only [d180264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23281 p hg
    simpa only [d180264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23283 (p : Pattern) (guard : d0 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23284 (p : Pattern) (guard : d0 p = 1) : d48340 p ≤ (0 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23285 (p : Pattern) (guard : d0 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23286 (p : Pattern) (guard : d0 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23287 (p : Pattern) (guard : d0 p = 1) : d48336 p ≤ (0 : Int) + d47697 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23288 (p : Pattern) (guard : d0 p = 1) : d48317 p ≤ (0 : Int) + d47676 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23289 (p : Pattern) (guard : d0 p = 1) : d48325 p ≤ (0 : Int) + d47681 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23290 (p : Pattern) (guard : d0 p = 1) : d48313 p ≤ (0 : Int) + d47685 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23291 (p : Pattern) (guard : d29117 p = 1) : d47664 p ≤ (0 : Int) + d47664 p := by
  omega
theorem compare23292 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d47684 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23293 (p : Pattern) (guard : d29118 p = 1) : d48313 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d29117 p = 1 := by simpa only [d29118, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23291 p hg
    simpa only [d29118, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d29118, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23292 p hg
    simpa only [d29118, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23294 (p : Pattern) (guard : d179108 p = 1) : d48313 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23290 p hg
    simpa only [d179108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d29118 p = 1 := by simpa only [d179108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23293 p hg
    simpa only [d179108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23295 (p : Pattern) (guard : d179109 p = 1) : d48313 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179108 p = 1 := by simpa only [d179109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23294 p hg
    simpa only [d179109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23290 p hg
    simpa only [d179109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23296 (p : Pattern) (guard : d179110 p = 1) : d48313 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179109 p = 1 := by simpa only [d179110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23295 p hg
    simpa only [d179110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23290 p hg
    simpa only [d179110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23297 (p : Pattern) (guard : d179111 p = 1) : d48326 p ≤ (0 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179111, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23289 p hg
    simpa only [d179111, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179110 p = 1 := by simpa only [d179111, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23296 p hg
    simpa only [d179111, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23298 (p : Pattern) (guard : d179112 p = 1) : d48337 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179112, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23288 p hg
    simpa only [d179112, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179111 p = 1 := by simpa only [d179112, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23297 p hg
    simpa only [d179112, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23299 (p : Pattern) (guard : d0 p = 1) : d48337 p ≤ (0 : Int) + d47687 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23300 (p : Pattern) (guard : d179113 p = 1) : d48337 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179112 p = 1 := by simpa only [d179113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23298 p hg
    simpa only [d179113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23299 p hg
    simpa only [d179113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23301 (p : Pattern) (guard : d179114 p = 1) : d48337 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179113 p = 1 := by simpa only [d179114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23300 p hg
    simpa only [d179114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23299 p hg
    simpa only [d179114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23302 (p : Pattern) (guard : d179115 p = 1) : d48337 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179114 p = 1 := by simpa only [d179115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23301 p hg
    simpa only [d179115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23299 p hg
    simpa only [d179115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23303 (p : Pattern) (guard : d0 p = 1) : d48328 p ≤ (0 : Int) + d47698 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23304 (p : Pattern) (guard : d179116 p = 1) : d48338 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179115 p = 1 := by simpa only [d179116, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23302 p hg
    simpa only [d179116, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179116, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23303 p hg
    simpa only [d179116, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23305 (p : Pattern) (guard : d179117 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179117, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23287 p hg
    simpa only [d179117, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179116 p = 1 := by simpa only [d179117, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23304 p hg
    simpa only [d179117, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23306 (p : Pattern) (guard : d179118 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179117 p = 1 := by simpa only [d179118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23305 p hg
    simpa only [d179118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23307 (p : Pattern) (guard : d179119 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179118 p = 1 := by simpa only [d179119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23306 p hg
    simpa only [d179119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23308 (p : Pattern) (guard : d179120 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179119 p = 1 := by simpa only [d179120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23307 p hg
    simpa only [d179120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23309 (p : Pattern) (guard : d179121 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179120 p = 1 := by simpa only [d179121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23308 p hg
    simpa only [d179121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23310 (p : Pattern) (guard : d179122 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179121 p = 1 := by simpa only [d179122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23309 p hg
    simpa only [d179122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23311 (p : Pattern) (guard : d179177 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179122 p = 1 := by simpa only [d179177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23310 p hg
    simpa only [d179177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23312 (p : Pattern) (guard : d179178 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179177 p = 1 := by simpa only [d179178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23311 p hg
    simpa only [d179178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23313 (p : Pattern) (guard : d179179 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179178 p = 1 := by simpa only [d179179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23312 p hg
    simpa only [d179179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23314 (p : Pattern) (guard : d179180 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179179 p = 1 := by simpa only [d179180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23313 p hg
    simpa only [d179180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23315 (p : Pattern) (guard : d179181 p = 1) : d48340 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179181, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d179181, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179180 p = 1 := by simpa only [d179181, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23314 p hg
    simpa only [d179181, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23316 (p : Pattern) (guard : d0 p = 1) : d48321 p ≤ (0 : Int) + d47697 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23317 (p : Pattern) (guard : d0 p = 1) : d48324 p ≤ (0 : Int) + d47676 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23318 (p : Pattern) (guard : d179112 p = 1) : d48327 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179112, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23317 p hg
    simpa only [d179112, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179111 p = 1 := by simpa only [d179112, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23297 p hg
    simpa only [d179112, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23319 (p : Pattern) (guard : d0 p = 1) : d48327 p ≤ (0 : Int) + d47687 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23320 (p : Pattern) (guard : d179113 p = 1) : d48327 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179112 p = 1 := by simpa only [d179113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23318 p hg
    simpa only [d179113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23319 p hg
    simpa only [d179113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23321 (p : Pattern) (guard : d179114 p = 1) : d48327 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179113 p = 1 := by simpa only [d179114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23320 p hg
    simpa only [d179114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23319 p hg
    simpa only [d179114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23322 (p : Pattern) (guard : d179115 p = 1) : d48327 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179114 p = 1 := by simpa only [d179115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23321 p hg
    simpa only [d179115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23319 p hg
    simpa only [d179115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23323 (p : Pattern) (guard : d179116 p = 1) : d48329 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179115 p = 1 := by simpa only [d179116, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23322 p hg
    simpa only [d179116, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179116, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23303 p hg
    simpa only [d179116, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23324 (p : Pattern) (guard : d179117 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179117, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23316 p hg
    simpa only [d179117, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179116 p = 1 := by simpa only [d179117, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23323 p hg
    simpa only [d179117, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23325 (p : Pattern) (guard : d179118 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179117 p = 1 := by simpa only [d179118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23324 p hg
    simpa only [d179118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d179118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23326 (p : Pattern) (guard : d179119 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179118 p = 1 := by simpa only [d179119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23325 p hg
    simpa only [d179119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d179119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23327 (p : Pattern) (guard : d179120 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179119 p = 1 := by simpa only [d179120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23326 p hg
    simpa only [d179120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d179120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23328 (p : Pattern) (guard : d179121 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d179121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179120 p = 1 := by simpa only [d179121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23327 p hg
    simpa only [d179121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23329 (p : Pattern) (guard : d179122 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179121 p = 1 := by simpa only [d179122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23328 p hg
    simpa only [d179122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d179122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23330 (p : Pattern) (guard : d179177 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d179177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179122 p = 1 := by simpa only [d179177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23329 p hg
    simpa only [d179177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23331 (p : Pattern) (guard : d179178 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179177 p = 1 := by simpa only [d179178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23330 p hg
    simpa only [d179178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d179178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23332 (p : Pattern) (guard : d179179 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d179179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179178 p = 1 := by simpa only [d179179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23331 p hg
    simpa only [d179179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23333 (p : Pattern) (guard : d179180 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d179180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179179 p = 1 := by simpa only [d179180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23332 p hg
    simpa only [d179180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23334 (p : Pattern) (guard : d179128 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179120 p = 1 := by simpa only [d179128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23308 p hg
    simpa only [d179128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23335 (p : Pattern) (guard : d179129 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179128 p = 1 := by simpa only [d179129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23334 p hg
    simpa only [d179129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23336 (p : Pattern) (guard : d179184 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179129 p = 1 := by simpa only [d179184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23335 p hg
    simpa only [d179184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23337 (p : Pattern) (guard : d179185 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179184 p = 1 := by simpa only [d179185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23336 p hg
    simpa only [d179185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23338 (p : Pattern) (guard : d179186 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179185 p = 1 := by simpa only [d179186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23337 p hg
    simpa only [d179186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23339 (p : Pattern) (guard : d179187 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179186 p = 1 := by simpa only [d179187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23338 p hg
    simpa only [d179187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23340 (p : Pattern) (guard : d179188 p = 1) : d48340 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d179180 p = 1 := by simpa only [d179188, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23333 p hg
    simpa only [d179188, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179187 p = 1 := by simpa only [d179188, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23339 p hg
    simpa only [d179188, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23341 (p : Pattern) (guard : d179189 p = 1) : d48340 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d179181 p = 1 := by simpa only [d179189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23315 p hg
    simpa only [d179189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179188 p = 1 := by simpa only [d179189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23340 p hg
    simpa only [d179189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23342 (p : Pattern) (guard : d179190 p = 1) : d48340 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d179189 p = 1 := by simpa only [d179190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23341 p hg
    simpa only [d179190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23284 p hg
    simpa only [d179190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23343 (p : Pattern) (guard : d180426 p = 1) : d48340 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d179190 p = 1 := by simpa only [d180426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23342 p hg
    simpa only [d180426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23284 p hg
    simpa only [d180426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23344 (p : Pattern) (guard : d180427 p = 1) : d48340 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23284 p hg
    simpa only [d180427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180426 p = 1 := by simpa only [d180427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23343 p hg
    simpa only [d180427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23345 (p : Pattern) (guard : d0 p = 1) : d48358 p ≤ (0 : Int) + d47767 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23346 (p : Pattern) (guard : d0 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23347 (p : Pattern) (guard : d0 p = 1) : d48351 p ≤ (0 : Int) + d47763 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23348 (p : Pattern) (guard : d0 p = 1) : d48353 p ≤ (0 : Int) + d47746 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23349 (p : Pattern) (guard : d0 p = 1) : d48344 p ≤ (0 : Int) + d47751 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23350 (p : Pattern) (guard : d0 p = 1) : d48345 p ≤ (0 : Int) + d47755 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23351 (p : Pattern) (guard : d29117 p = 1) : d47737 p ≤ (0 : Int) + d47737 p := by
  omega
theorem compare23352 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d47754 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23353 (p : Pattern) (guard : d29118 p = 1) : d48345 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d29117 p = 1 := by simpa only [d29118, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23351 p hg
    simpa only [d29118, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d29118, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23352 p hg
    simpa only [d29118, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23354 (p : Pattern) (guard : d179108 p = 1) : d48345 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23350 p hg
    simpa only [d179108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d29118 p = 1 := by simpa only [d179108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23353 p hg
    simpa only [d179108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23355 (p : Pattern) (guard : d179109 p = 1) : d48345 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179108 p = 1 := by simpa only [d179109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23354 p hg
    simpa only [d179109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23350 p hg
    simpa only [d179109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23356 (p : Pattern) (guard : d179110 p = 1) : d48345 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179109 p = 1 := by simpa only [d179110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23355 p hg
    simpa only [d179110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23350 p hg
    simpa only [d179110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23357 (p : Pattern) (guard : d179111 p = 1) : d48346 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179111, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23349 p hg
    simpa only [d179111, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179110 p = 1 := by simpa only [d179111, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23356 p hg
    simpa only [d179111, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23358 (p : Pattern) (guard : d179112 p = 1) : d48354 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179112, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23348 p hg
    simpa only [d179112, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179111 p = 1 := by simpa only [d179112, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23357 p hg
    simpa only [d179112, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23359 (p : Pattern) (guard : d0 p = 1) : d48354 p ≤ (0 : Int) + d47757 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23360 (p : Pattern) (guard : d179113 p = 1) : d48354 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179112 p = 1 := by simpa only [d179113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23358 p hg
    simpa only [d179113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23359 p hg
    simpa only [d179113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23361 (p : Pattern) (guard : d179114 p = 1) : d48354 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179113 p = 1 := by simpa only [d179114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23360 p hg
    simpa only [d179114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23359 p hg
    simpa only [d179114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23362 (p : Pattern) (guard : d179115 p = 1) : d48354 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179114 p = 1 := by simpa only [d179115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23361 p hg
    simpa only [d179115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23359 p hg
    simpa only [d179115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23363 (p : Pattern) (guard : d0 p = 1) : d48355 p ≤ (0 : Int) + d47764 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23364 (p : Pattern) (guard : d179116 p = 1) : d48356 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179115 p = 1 := by simpa only [d179116, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23362 p hg
    simpa only [d179116, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179116, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23363 p hg
    simpa only [d179116, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23365 (p : Pattern) (guard : d179117 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179117, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23347 p hg
    simpa only [d179117, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179116 p = 1 := by simpa only [d179117, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23364 p hg
    simpa only [d179117, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23366 (p : Pattern) (guard : d179118 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179117 p = 1 := by simpa only [d179118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23365 p hg
    simpa only [d179118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d179118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23367 (p : Pattern) (guard : d179119 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179118 p = 1 := by simpa only [d179119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23366 p hg
    simpa only [d179119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d179119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23368 (p : Pattern) (guard : d179120 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179119 p = 1 := by simpa only [d179120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23367 p hg
    simpa only [d179120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d179120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23369 (p : Pattern) (guard : d179128 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179120 p = 1 := by simpa only [d179128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23368 p hg
    simpa only [d179128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d179128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23370 (p : Pattern) (guard : d179129 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179128 p = 1 := by simpa only [d179129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23369 p hg
    simpa only [d179129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d179129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23371 (p : Pattern) (guard : d179184 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d179184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179129 p = 1 := by simpa only [d179184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23370 p hg
    simpa only [d179184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23372 (p : Pattern) (guard : d179185 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179184 p = 1 := by simpa only [d179185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23371 p hg
    simpa only [d179185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d179185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23373 (p : Pattern) (guard : d179186 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d179186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179185 p = 1 := by simpa only [d179186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23372 p hg
    simpa only [d179186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23374 (p : Pattern) (guard : d179187 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d179187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179186 p = 1 := by simpa only [d179187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23373 p hg
    simpa only [d179187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23375 (p : Pattern) (guard : d180428 p = 1) : d48358 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180428, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d180428, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179187 p = 1 := by simpa only [d180428, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23374 p hg
    simpa only [d180428, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23376 (p : Pattern) (guard : d180429 p = 1) : d48358 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23345 p hg
    simpa only [d180429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180428 p = 1 := by simpa only [d180429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23375 p hg
    simpa only [d180429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23377 (p : Pattern) (guard : d180430 p = 1) : d48358 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d180429 p = 1 := by simpa only [d180430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23376 p hg
    simpa only [d180430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23345 p hg
    simpa only [d180430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23378 (p : Pattern) (guard : d180431 p = 1) : d48358 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d180430 p = 1 := by simpa only [d180431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23377 p hg
    simpa only [d180431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23345 p hg
    simpa only [d180431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23379 (p : Pattern) (guard : d180432 p = 1) : d48358 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d180431 p = 1 := by simpa only [d180432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23378 p hg
    simpa only [d180432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23345 p hg
    simpa only [d180432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23380 (p : Pattern) (guard : d180433 p = 1) : d48359 p ≤ (0 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d180427 p = 1 := by simpa only [d180433, d48359, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23344 p hg
    simpa only [d180433, d48359, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180432 p = 1 := by simpa only [d180433, d48359, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23379 p hg
    simpa only [d180433, d48359, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23381 (p : Pattern) (guard : d0 p = 1) : d48367 p ≤ (0 : Int) + d47809 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23382 (p : Pattern) (guard : d0 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23383 (p : Pattern) (guard : d0 p = 1) : d48317 p ≤ (0 : Int) + d47786 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23384 (p : Pattern) (guard : d0 p = 1) : d48360 p ≤ (0 : Int) + d47796 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23385 (p : Pattern) (guard : d0 p = 1) : d48361 p ≤ (0 : Int) + d47803 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23386 (p : Pattern) (guard : d29397 p = 1) : d47799 p ≤ (0 : Int) + d47799 p := by
  omega
theorem compare23387 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d47802 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23388 (p : Pattern) (guard : d29398 p = 1) : d48361 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d29397 p = 1 := by simpa only [d29398, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23386 p hg
    simpa only [d29398, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d29398, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23387 p hg
    simpa only [d29398, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23389 (p : Pattern) (guard : d179145 p = 1) : d48361 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23385 p hg
    simpa only [d179145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d29398 p = 1 := by simpa only [d179145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23388 p hg
    simpa only [d179145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23390 (p : Pattern) (guard : d179146 p = 1) : d48361 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179145 p = 1 := by simpa only [d179146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23389 p hg
    simpa only [d179146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23385 p hg
    simpa only [d179146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23391 (p : Pattern) (guard : d179147 p = 1) : d48361 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179146 p = 1 := by simpa only [d179147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23390 p hg
    simpa only [d179147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23385 p hg
    simpa only [d179147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23392 (p : Pattern) (guard : d179148 p = 1) : d48362 p ≤ (0 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179148, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23384 p hg
    simpa only [d179148, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179147 p = 1 := by simpa only [d179148, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23391 p hg
    simpa only [d179148, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23393 (p : Pattern) (guard : d179149 p = 1) : d48363 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179149, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23383 p hg
    simpa only [d179149, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179148 p = 1 := by simpa only [d179149, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23392 p hg
    simpa only [d179149, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23394 (p : Pattern) (guard : d0 p = 1) : d48363 p ≤ (0 : Int) + d47805 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23395 (p : Pattern) (guard : d179150 p = 1) : d48363 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179149 p = 1 := by simpa only [d179150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23393 p hg
    simpa only [d179150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23394 p hg
    simpa only [d179150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23396 (p : Pattern) (guard : d179151 p = 1) : d48363 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179150 p = 1 := by simpa only [d179151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23395 p hg
    simpa only [d179151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23394 p hg
    simpa only [d179151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23397 (p : Pattern) (guard : d179152 p = 1) : d48363 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179151 p = 1 := by simpa only [d179152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23396 p hg
    simpa only [d179152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23394 p hg
    simpa only [d179152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23398 (p : Pattern) (guard : d0 p = 1) : d48364 p ≤ (0 : Int) + d47806 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23399 (p : Pattern) (guard : d179153 p = 1) : d48365 p ≤ (0 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179152 p = 1 := by simpa only [d179153, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23397 p hg
    simpa only [d179153, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179153, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23398 p hg
    simpa only [d179153, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23400 (p : Pattern) (guard : d179154 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179154, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23287 p hg
    simpa only [d179154, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179153 p = 1 := by simpa only [d179154, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23399 p hg
    simpa only [d179154, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23401 (p : Pattern) (guard : d179155 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179154 p = 1 := by simpa only [d179155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23400 p hg
    simpa only [d179155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d179155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23402 (p : Pattern) (guard : d179156 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179155 p = 1 := by simpa only [d179156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23401 p hg
    simpa only [d179156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d179156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23403 (p : Pattern) (guard : d179157 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179156 p = 1 := by simpa only [d179157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23402 p hg
    simpa only [d179157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d179157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23404 (p : Pattern) (guard : d179158 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179157 p = 1 := by simpa only [d179158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23403 p hg
    simpa only [d179158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d179158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23405 (p : Pattern) (guard : d179159 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179158 p = 1 := by simpa only [d179159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23404 p hg
    simpa only [d179159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d179159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23406 (p : Pattern) (guard : d180434 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d180434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179159 p = 1 := by simpa only [d180434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23405 p hg
    simpa only [d180434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23407 (p : Pattern) (guard : d180435 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d180434 p = 1 := by simpa only [d180435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23406 p hg
    simpa only [d180435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d180435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23408 (p : Pattern) (guard : d180436 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d180436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180435 p = 1 := by simpa only [d180436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23407 p hg
    simpa only [d180436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23409 (p : Pattern) (guard : d180437 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d180437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180436 p = 1 := by simpa only [d180437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23408 p hg
    simpa only [d180437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23410 (p : Pattern) (guard : d180438 p = 1) : d48367 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180438, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d180438, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180437 p = 1 := by simpa only [d180438, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23409 p hg
    simpa only [d180438, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23411 (p : Pattern) (guard : d180439 p = 1) : d48367 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23381 p hg
    simpa only [d180439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180438 p = 1 := by simpa only [d180439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23410 p hg
    simpa only [d180439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23412 (p : Pattern) (guard : d180440 p = 1) : d48367 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 69 with
  | false =>
    have hg : d180439 p = 1 := by simpa only [d180440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23411 p hg
    simpa only [d180440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23381 p hg
    simpa only [d180440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23413 (p : Pattern) (guard : d180441 p = 1) : d48367 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 51 with
  | false =>
    have hg : d180440 p = 1 := by simpa only [d180441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23412 p hg
    simpa only [d180441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23381 p hg
    simpa only [d180441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23414 (p : Pattern) (guard : d180442 p = 1) : d48367 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 50 with
  | false =>
    have hg : d180441 p = 1 := by simpa only [d180442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23413 p hg
    simpa only [d180442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23381 p hg
    simpa only [d180442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23415 (p : Pattern) (guard : d0 p = 1) : d48386 p ≤ (0 : Int) + d47864 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare23416 (p : Pattern) (guard : d180443 p = 1) : d48387 p ≤ (0 : Int) + d47865 p := by
  cases selected : p 49 with
  | false =>
    have hg : d180442 p = 1 := by simpa only [d180443, d48387, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23414 p hg
    simpa only [d180443, d48387, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180443, d48387, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23415 p hg
    simpa only [d180443, d48387, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23417 (p : Pattern) (guard : d180444 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d180433 p = 1 := by simpa only [d180444, d48388, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23380 p hg
    simpa only [d180444, d48388, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180443 p = 1 := by simpa only [d180444, d48388, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23416 p hg
    simpa only [d180444, d48388, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23418 (p : Pattern) (guard : d180445 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180444 p = 1 := by simpa only [d180445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23417 p hg
    simpa only [d180445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23419 (p : Pattern) (guard : d180446 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180445 p = 1 := by simpa only [d180446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23418 p hg
    simpa only [d180446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23420 (p : Pattern) (guard : d180447 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180446 p = 1 := by simpa only [d180447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23419 p hg
    simpa only [d180447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23421 (p : Pattern) (guard : d180448 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180447 p = 1 := by simpa only [d180448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23420 p hg
    simpa only [d180448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23422 (p : Pattern) (guard : d180449 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180448 p = 1 := by simpa only [d180449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23421 p hg
    simpa only [d180449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23423 (p : Pattern) (guard : d180450 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180449 p = 1 := by simpa only [d180450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23422 p hg
    simpa only [d180450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23424 (p : Pattern) (guard : d180451 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180450 p = 1 := by simpa only [d180451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23423 p hg
    simpa only [d180451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23425 (p : Pattern) (guard : d179211 p = 1) : d47664 p ≤ (0 : Int) + d47664 p := by
  omega
theorem compare23426 (p : Pattern) (guard : d179212 p = 1) : d48313 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179211 p = 1 := by simpa only [d179212, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23425 p hg
    simpa only [d179212, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179212, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23292 p hg
    simpa only [d179212, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23427 (p : Pattern) (guard : d179213 p = 1) : d48313 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23290 p hg
    simpa only [d179213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179212 p = 1 := by simpa only [d179213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23426 p hg
    simpa only [d179213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23428 (p : Pattern) (guard : d179214 p = 1) : d48313 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179213 p = 1 := by simpa only [d179214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23427 p hg
    simpa only [d179214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23290 p hg
    simpa only [d179214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23429 (p : Pattern) (guard : d179300 p = 1) : d48313 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179214 p = 1 := by simpa only [d179300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23428 p hg
    simpa only [d179300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23290 p hg
    simpa only [d179300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23430 (p : Pattern) (guard : d179301 p = 1) : d48326 p ≤ (0 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179301, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23289 p hg
    simpa only [d179301, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179300 p = 1 := by simpa only [d179301, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23429 p hg
    simpa only [d179301, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23431 (p : Pattern) (guard : d179302 p = 1) : d48337 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179302, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23288 p hg
    simpa only [d179302, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179301 p = 1 := by simpa only [d179302, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23430 p hg
    simpa only [d179302, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23432 (p : Pattern) (guard : d179303 p = 1) : d48337 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179302 p = 1 := by simpa only [d179303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23431 p hg
    simpa only [d179303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23299 p hg
    simpa only [d179303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23433 (p : Pattern) (guard : d179304 p = 1) : d48337 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179303 p = 1 := by simpa only [d179304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23432 p hg
    simpa only [d179304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23299 p hg
    simpa only [d179304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23434 (p : Pattern) (guard : d179305 p = 1) : d48337 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179304 p = 1 := by simpa only [d179305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23433 p hg
    simpa only [d179305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23299 p hg
    simpa only [d179305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23435 (p : Pattern) (guard : d179306 p = 1) : d48338 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179305 p = 1 := by simpa only [d179306, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23434 p hg
    simpa only [d179306, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179306, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23303 p hg
    simpa only [d179306, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23436 (p : Pattern) (guard : d179307 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179307, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23287 p hg
    simpa only [d179307, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179306 p = 1 := by simpa only [d179307, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23435 p hg
    simpa only [d179307, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23437 (p : Pattern) (guard : d179308 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179307 p = 1 := by simpa only [d179308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23436 p hg
    simpa only [d179308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23438 (p : Pattern) (guard : d179309 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179308 p = 1 := by simpa only [d179309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23437 p hg
    simpa only [d179309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23439 (p : Pattern) (guard : d179310 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179309 p = 1 := by simpa only [d179310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23438 p hg
    simpa only [d179310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23440 (p : Pattern) (guard : d179311 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179310 p = 1 := by simpa only [d179311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23439 p hg
    simpa only [d179311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23441 (p : Pattern) (guard : d179312 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179311 p = 1 := by simpa only [d179312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23440 p hg
    simpa only [d179312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23442 (p : Pattern) (guard : d179313 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179312 p = 1 := by simpa only [d179313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23441 p hg
    simpa only [d179313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23443 (p : Pattern) (guard : d179314 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179313 p = 1 := by simpa only [d179314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23442 p hg
    simpa only [d179314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23444 (p : Pattern) (guard : d179315 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179314 p = 1 := by simpa only [d179315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23443 p hg
    simpa only [d179315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23445 (p : Pattern) (guard : d179316 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179315 p = 1 := by simpa only [d179316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23444 p hg
    simpa only [d179316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23446 (p : Pattern) (guard : d179317 p = 1) : d48340 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179317, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d179317, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179316 p = 1 := by simpa only [d179317, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23445 p hg
    simpa only [d179317, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23447 (p : Pattern) (guard : d179302 p = 1) : d48327 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179302, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23317 p hg
    simpa only [d179302, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179301 p = 1 := by simpa only [d179302, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23430 p hg
    simpa only [d179302, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23448 (p : Pattern) (guard : d179303 p = 1) : d48327 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179302 p = 1 := by simpa only [d179303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23447 p hg
    simpa only [d179303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23319 p hg
    simpa only [d179303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23449 (p : Pattern) (guard : d179304 p = 1) : d48327 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179303 p = 1 := by simpa only [d179304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23448 p hg
    simpa only [d179304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23319 p hg
    simpa only [d179304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23450 (p : Pattern) (guard : d179305 p = 1) : d48327 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179304 p = 1 := by simpa only [d179305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23449 p hg
    simpa only [d179305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23319 p hg
    simpa only [d179305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23451 (p : Pattern) (guard : d179306 p = 1) : d48329 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179305 p = 1 := by simpa only [d179306, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23450 p hg
    simpa only [d179306, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179306, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23303 p hg
    simpa only [d179306, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23452 (p : Pattern) (guard : d179307 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179307, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23316 p hg
    simpa only [d179307, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179306 p = 1 := by simpa only [d179307, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23451 p hg
    simpa only [d179307, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23453 (p : Pattern) (guard : d179308 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179307 p = 1 := by simpa only [d179308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23452 p hg
    simpa only [d179308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d179308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23454 (p : Pattern) (guard : d179309 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179308 p = 1 := by simpa only [d179309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23453 p hg
    simpa only [d179309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d179309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23455 (p : Pattern) (guard : d179310 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179309 p = 1 := by simpa only [d179310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23454 p hg
    simpa only [d179310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d179310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23456 (p : Pattern) (guard : d179311 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d179311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179310 p = 1 := by simpa only [d179311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23455 p hg
    simpa only [d179311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23457 (p : Pattern) (guard : d179312 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179311 p = 1 := by simpa only [d179312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23456 p hg
    simpa only [d179312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d179312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23458 (p : Pattern) (guard : d179313 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d179313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179312 p = 1 := by simpa only [d179313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23457 p hg
    simpa only [d179313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23459 (p : Pattern) (guard : d179314 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179313 p = 1 := by simpa only [d179314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23458 p hg
    simpa only [d179314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d179314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23460 (p : Pattern) (guard : d179315 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d179315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179314 p = 1 := by simpa only [d179315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23459 p hg
    simpa only [d179315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23461 (p : Pattern) (guard : d179316 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d179316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179315 p = 1 := by simpa only [d179316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23460 p hg
    simpa only [d179316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23462 (p : Pattern) (guard : d179320 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179310 p = 1 := by simpa only [d179320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23439 p hg
    simpa only [d179320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23463 (p : Pattern) (guard : d179321 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179320 p = 1 := by simpa only [d179321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23462 p hg
    simpa only [d179321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23464 (p : Pattern) (guard : d179322 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179321 p = 1 := by simpa only [d179322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23463 p hg
    simpa only [d179322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23465 (p : Pattern) (guard : d179323 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179322 p = 1 := by simpa only [d179323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23464 p hg
    simpa only [d179323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23466 (p : Pattern) (guard : d179324 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179323 p = 1 := by simpa only [d179324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23465 p hg
    simpa only [d179324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23467 (p : Pattern) (guard : d179325 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179324 p = 1 := by simpa only [d179325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23466 p hg
    simpa only [d179325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23468 (p : Pattern) (guard : d179326 p = 1) : d48340 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d179316 p = 1 := by simpa only [d179326, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23461 p hg
    simpa only [d179326, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179325 p = 1 := by simpa only [d179326, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23467 p hg
    simpa only [d179326, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23469 (p : Pattern) (guard : d179327 p = 1) : d48340 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d179317 p = 1 := by simpa only [d179327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23446 p hg
    simpa only [d179327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179326 p = 1 := by simpa only [d179327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23468 p hg
    simpa only [d179327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23470 (p : Pattern) (guard : d179328 p = 1) : d48340 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d179327 p = 1 := by simpa only [d179328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23469 p hg
    simpa only [d179328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23284 p hg
    simpa only [d179328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23471 (p : Pattern) (guard : d180452 p = 1) : d48340 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d179328 p = 1 := by simpa only [d180452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23470 p hg
    simpa only [d180452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23284 p hg
    simpa only [d180452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23472 (p : Pattern) (guard : d180453 p = 1) : d48340 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23284 p hg
    simpa only [d180453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180452 p = 1 := by simpa only [d180453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23471 p hg
    simpa only [d180453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23473 (p : Pattern) (guard : d179211 p = 1) : d47737 p ≤ (0 : Int) + d47737 p := by
  omega
theorem compare23474 (p : Pattern) (guard : d179212 p = 1) : d48345 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179211 p = 1 := by simpa only [d179212, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23473 p hg
    simpa only [d179212, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179212, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23352 p hg
    simpa only [d179212, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23475 (p : Pattern) (guard : d179213 p = 1) : d48345 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23350 p hg
    simpa only [d179213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179212 p = 1 := by simpa only [d179213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23474 p hg
    simpa only [d179213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23476 (p : Pattern) (guard : d179214 p = 1) : d48345 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179213 p = 1 := by simpa only [d179214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23475 p hg
    simpa only [d179214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23350 p hg
    simpa only [d179214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23477 (p : Pattern) (guard : d179300 p = 1) : d48345 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179214 p = 1 := by simpa only [d179300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23476 p hg
    simpa only [d179300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23350 p hg
    simpa only [d179300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23478 (p : Pattern) (guard : d179301 p = 1) : d48346 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179301, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23349 p hg
    simpa only [d179301, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179300 p = 1 := by simpa only [d179301, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23477 p hg
    simpa only [d179301, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23479 (p : Pattern) (guard : d179302 p = 1) : d48354 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179302, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23348 p hg
    simpa only [d179302, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179301 p = 1 := by simpa only [d179302, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23478 p hg
    simpa only [d179302, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23480 (p : Pattern) (guard : d179303 p = 1) : d48354 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179302 p = 1 := by simpa only [d179303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23479 p hg
    simpa only [d179303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23359 p hg
    simpa only [d179303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23481 (p : Pattern) (guard : d179304 p = 1) : d48354 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179303 p = 1 := by simpa only [d179304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23480 p hg
    simpa only [d179304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23359 p hg
    simpa only [d179304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23482 (p : Pattern) (guard : d179305 p = 1) : d48354 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179304 p = 1 := by simpa only [d179305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23481 p hg
    simpa only [d179305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23359 p hg
    simpa only [d179305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23483 (p : Pattern) (guard : d179306 p = 1) : d48356 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179305 p = 1 := by simpa only [d179306, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23482 p hg
    simpa only [d179306, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179306, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23363 p hg
    simpa only [d179306, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23484 (p : Pattern) (guard : d179307 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179307, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23347 p hg
    simpa only [d179307, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179306 p = 1 := by simpa only [d179307, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23483 p hg
    simpa only [d179307, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23485 (p : Pattern) (guard : d179308 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179307 p = 1 := by simpa only [d179308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23484 p hg
    simpa only [d179308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d179308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23486 (p : Pattern) (guard : d179309 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179308 p = 1 := by simpa only [d179309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23485 p hg
    simpa only [d179309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d179309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23487 (p : Pattern) (guard : d179310 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179309 p = 1 := by simpa only [d179310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23486 p hg
    simpa only [d179310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d179310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23488 (p : Pattern) (guard : d179320 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179310 p = 1 := by simpa only [d179320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23487 p hg
    simpa only [d179320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d179320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23489 (p : Pattern) (guard : d179321 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179320 p = 1 := by simpa only [d179321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23488 p hg
    simpa only [d179321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d179321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23490 (p : Pattern) (guard : d179322 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d179322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179321 p = 1 := by simpa only [d179322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23489 p hg
    simpa only [d179322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23491 (p : Pattern) (guard : d179323 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179322 p = 1 := by simpa only [d179323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23490 p hg
    simpa only [d179323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d179323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23492 (p : Pattern) (guard : d179324 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d179324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179323 p = 1 := by simpa only [d179324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23491 p hg
    simpa only [d179324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23493 (p : Pattern) (guard : d179325 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d179325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179324 p = 1 := by simpa only [d179325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23492 p hg
    simpa only [d179325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23494 (p : Pattern) (guard : d180454 p = 1) : d48358 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180454, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d180454, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179325 p = 1 := by simpa only [d180454, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23493 p hg
    simpa only [d180454, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23495 (p : Pattern) (guard : d180455 p = 1) : d48358 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23345 p hg
    simpa only [d180455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180454 p = 1 := by simpa only [d180455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23494 p hg
    simpa only [d180455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23496 (p : Pattern) (guard : d180456 p = 1) : d48358 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d180455 p = 1 := by simpa only [d180456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23495 p hg
    simpa only [d180456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23345 p hg
    simpa only [d180456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23497 (p : Pattern) (guard : d180457 p = 1) : d48358 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d180456 p = 1 := by simpa only [d180457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23496 p hg
    simpa only [d180457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23345 p hg
    simpa only [d180457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23498 (p : Pattern) (guard : d180458 p = 1) : d48358 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d180457 p = 1 := by simpa only [d180458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23497 p hg
    simpa only [d180458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23345 p hg
    simpa only [d180458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23499 (p : Pattern) (guard : d180459 p = 1) : d48359 p ≤ (0 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d180453 p = 1 := by simpa only [d180459, d48359, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23472 p hg
    simpa only [d180459, d48359, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180458 p = 1 := by simpa only [d180459, d48359, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23498 p hg
    simpa only [d180459, d48359, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
