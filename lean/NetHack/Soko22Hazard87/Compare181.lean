import NetHack.Soko22Hazard87.Compare180
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare45250 (p : Pattern) (guard : d367429 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 67 with
  | false =>
    have hg : d367428 p = 1 := by simpa only [d367429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45249 p hg
    simpa only [d367429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45251 (p : Pattern) (guard : d367430 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 52 with
  | false =>
    have hg : d367429 p = 1 := by simpa only [d367430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45250 p hg
    simpa only [d367430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45252 (p : Pattern) (guard : d367431 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 47 with
  | false =>
    have hg : d367430 p = 1 := by simpa only [d367431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45251 p hg
    simpa only [d367431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45253 (p : Pattern) (guard : d367432 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 46 with
  | false =>
    have hg : d367431 p = 1 := by simpa only [d367432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45252 p hg
    simpa only [d367432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45254 (p : Pattern) (guard : d367433 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 45 with
  | false =>
    have hg : d367432 p = 1 := by simpa only [d367433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45253 p hg
    simpa only [d367433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45255 (p : Pattern) (guard : d367434 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 30 with
  | false =>
    have hg : d367433 p = 1 := by simpa only [d367434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45254 p hg
    simpa only [d367434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45256 (p : Pattern) (guard : d367435 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 29 with
  | false =>
    have hg : d367434 p = 1 := by simpa only [d367435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45255 p hg
    simpa only [d367435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45257 (p : Pattern) (guard : d367436 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 28 with
  | false =>
    have hg : d367435 p = 1 := by simpa only [d367436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45256 p hg
    simpa only [d367436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45258 (p : Pattern) (guard : d367437 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 27 with
  | false =>
    have hg : d367436 p = 1 := by simpa only [d367437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45257 p hg
    simpa only [d367437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45259 (p : Pattern) (guard : d367438 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 25 with
  | false =>
    have hg : d367437 p = 1 := by simpa only [d367438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45258 p hg
    simpa only [d367438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d367438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45260 (p : Pattern) (guard : d0 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45261 (p : Pattern) (guard : d0 p = 1) : d51331 p ≤ (7 : Int) + d338727 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45262 (p : Pattern) (guard : d0 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45263 (p : Pattern) (guard : d0 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45264 (p : Pattern) (guard : d0 p = 1) : d51329 p ≤ (7 : Int) + d338724 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45265 (p : Pattern) (guard : d0 p = 1) : d51313 p ≤ (7 : Int) + d338703 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45266 (p : Pattern) (guard : d0 p = 1) : d51283 p ≤ (7 : Int) + d338708 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45267 (p : Pattern) (guard : d0 p = 1) : d51286 p ≤ (7 : Int) + d338684 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45268 (p : Pattern) (guard : d0 p = 1) : d47616 p ≤ (7 : Int) + d4 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45269 (p : Pattern) (guard : d13 p = 1) : d4 p ≤ (7 : Int) + d4 p := by
  omega
theorem compare45270 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (7 : Int) + d4 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45271 (p : Pattern) (guard : d14 p = 1) : d47616 p ≤ (7 : Int) + d4 p := by
  cases selected : p 247 with
  | false =>
    have hg : d13 p = 1 := by simpa only [d14, d47616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45269 p hg
    simpa only [d14, d47616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14, d47616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45270 p hg
    simpa only [d14, d47616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45272 (p : Pattern) (guard : d1084 p = 1) : d47616 p ≤ (7 : Int) + d4 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45268 p hg
    simpa only [d1084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14 p = 1 := by simpa only [d1084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45271 p hg
    simpa only [d1084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45273 (p : Pattern) (guard : d1085 p = 1) : d47616 p ≤ (7 : Int) + d4 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1084 p = 1 := by simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45272 p hg
    simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45268 p hg
    simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45274 (p : Pattern) (guard : d1086 p = 1) : d47616 p ≤ (7 : Int) + d4 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1085 p = 1 := by simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45273 p hg
    simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45268 p hg
    simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45275 (p : Pattern) (guard : d9771 p = 1) : d47616 p ≤ (7 : Int) + d4 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1086 p = 1 := by simpa only [d9771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45274 p hg
    simpa only [d9771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45268 p hg
    simpa only [d9771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45276 (p : Pattern) (guard : d342708 p = 1) : d47616 p ≤ (7 : Int) + d4 p := by
  cases selected : p 223 with
  | false =>
    have hg : d9771 p = 1 := by simpa only [d342708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45275 p hg
    simpa only [d342708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45268 p hg
    simpa only [d342708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45277 (p : Pattern) (guard : d0 p = 1) : d51203 p ≤ (7 : Int) + d4 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45278 (p : Pattern) (guard : d342709 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 204 with
  | false =>
    have hg : d342708 p = 1 := by simpa only [d342709, d51204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45276 p hg
    simpa only [d342709, d51204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342709, d51204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45277 p hg
    simpa only [d342709, d51204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45279 (p : Pattern) (guard : d0 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45280 (p : Pattern) (guard : d342710 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 202 with
  | false =>
    have hg : d342709 p = 1 := by simpa only [d342710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45278 p hg
    simpa only [d342710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45279 p hg
    simpa only [d342710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45281 (p : Pattern) (guard : d342711 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 201 with
  | false =>
    have hg : d342710 p = 1 := by simpa only [d342711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45280 p hg
    simpa only [d342711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45279 p hg
    simpa only [d342711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45282 (p : Pattern) (guard : d0 p = 1) : d51268 p ≤ (7 : Int) + d338655 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45283 (p : Pattern) (guard : d342712 p = 1) : d51269 p ≤ (7 : Int) + d338656 p := by
  cases selected : p 182 with
  | false =>
    have hg : d342711 p = 1 := by simpa only [d342712, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45281 p hg
    simpa only [d342712, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342712, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45282 p hg
    simpa only [d342712, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45284 (p : Pattern) (guard : d0 p = 1) : d51269 p ≤ (7 : Int) + d338656 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45285 (p : Pattern) (guard : d342713 p = 1) : d51269 p ≤ (7 : Int) + d338656 p := by
  cases selected : p 180 with
  | false =>
    have hg : d342712 p = 1 := by simpa only [d342713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45283 p hg
    simpa only [d342713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45284 p hg
    simpa only [d342713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45286 (p : Pattern) (guard : d0 p = 1) : d51235 p ≤ (7 : Int) + d338686 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45287 (p : Pattern) (guard : d342714 p = 1) : d51287 p ≤ (7 : Int) + d338687 p := by
  cases selected : p 163 with
  | false =>
    have hg : d342713 p = 1 := by simpa only [d342714, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45285 p hg
    simpa only [d342714, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342714, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45286 p hg
    simpa only [d342714, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45288 (p : Pattern) (guard : d0 p = 1) : d51239 p ≤ (7 : Int) + d338689 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45289 (p : Pattern) (guard : d342715 p = 1) : d51288 p ≤ (7 : Int) + d338690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d342714 p = 1 := by simpa only [d342715, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45287 p hg
    simpa only [d342715, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342715, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45288 p hg
    simpa only [d342715, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45290 (p : Pattern) (guard : d342716 p = 1) : d51289 p ≤ (7 : Int) + d338691 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342716, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45267 p hg
    simpa only [d342716, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342715 p = 1 := by simpa only [d342716, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45289 p hg
    simpa only [d342716, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45291 (p : Pattern) (guard : d0 p = 1) : d51292 p ≤ (7 : Int) + d338711 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45292 (p : Pattern) (guard : d342717 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 160 with
  | false =>
    have hg : d342716 p = 1 := by simpa only [d342717, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45290 p hg
    simpa only [d342717, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342717, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45291 p hg
    simpa only [d342717, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45293 (p : Pattern) (guard : d0 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45294 (p : Pattern) (guard : d342718 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 159 with
  | false =>
    have hg : d342717 p = 1 := by simpa only [d342718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45292 p hg
    simpa only [d342718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45293 p hg
    simpa only [d342718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45295 (p : Pattern) (guard : d342719 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 158 with
  | false =>
    have hg : d342718 p = 1 := by simpa only [d342719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45294 p hg
    simpa only [d342719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45293 p hg
    simpa only [d342719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45296 (p : Pattern) (guard : d342720 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 157 with
  | false =>
    have hg : d342719 p = 1 := by simpa only [d342720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45295 p hg
    simpa only [d342720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45293 p hg
    simpa only [d342720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45297 (p : Pattern) (guard : d342721 p = 1) : d51294 p ≤ (7 : Int) + d338713 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342721, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45266 p hg
    simpa only [d342721, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342720 p = 1 := by simpa only [d342721, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45296 p hg
    simpa only [d342721, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45298 (p : Pattern) (guard : d342722 p = 1) : d51314 p ≤ (7 : Int) + d338714 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342722, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45265 p hg
    simpa only [d342722, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342721 p = 1 := by simpa only [d342722, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45297 p hg
    simpa only [d342722, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45299 (p : Pattern) (guard : d0 p = 1) : d51314 p ≤ (7 : Int) + d338714 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45300 (p : Pattern) (guard : d342723 p = 1) : d51314 p ≤ (7 : Int) + d338714 p := by
  cases selected : p 136 with
  | false =>
    have hg : d342722 p = 1 := by simpa only [d342723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45298 p hg
    simpa only [d342723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45299 p hg
    simpa only [d342723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45301 (p : Pattern) (guard : d342724 p = 1) : d51314 p ≤ (7 : Int) + d338714 p := by
  cases selected : p 135 with
  | false =>
    have hg : d342723 p = 1 := by simpa only [d342724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45300 p hg
    simpa only [d342724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45299 p hg
    simpa only [d342724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45302 (p : Pattern) (guard : d342725 p = 1) : d51314 p ≤ (7 : Int) + d338714 p := by
  cases selected : p 119 with
  | false =>
    have hg : d342724 p = 1 := by simpa only [d342725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45301 p hg
    simpa only [d342725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45299 p hg
    simpa only [d342725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45303 (p : Pattern) (guard : d0 p = 1) : d51315 p ≤ (7 : Int) + d338725 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45304 (p : Pattern) (guard : d342726 p = 1) : d51316 p ≤ (7 : Int) + d338726 p := by
  cases selected : p 116 with
  | false =>
    have hg : d342725 p = 1 := by simpa only [d342726, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45302 p hg
    simpa only [d342726, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342726, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45303 p hg
    simpa only [d342726, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45305 (p : Pattern) (guard : d342727 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342727, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45264 p hg
    simpa only [d342727, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342726 p = 1 := by simpa only [d342727, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45304 p hg
    simpa only [d342727, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45306 (p : Pattern) (guard : d342728 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d342727 p = 1 := by simpa only [d342728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45305 p hg
    simpa only [d342728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d342728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45307 (p : Pattern) (guard : d342729 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d342728 p = 1 := by simpa only [d342729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45306 p hg
    simpa only [d342729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d342729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45308 (p : Pattern) (guard : d342730 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d342729 p = 1 := by simpa only [d342730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45307 p hg
    simpa only [d342730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d342730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45309 (p : Pattern) (guard : d342731 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d342731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342730 p = 1 := by simpa only [d342731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45308 p hg
    simpa only [d342731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45310 (p : Pattern) (guard : d342732 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d342731 p = 1 := by simpa only [d342732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45309 p hg
    simpa only [d342732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d342732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45311 (p : Pattern) (guard : d342790 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d342790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342732 p = 1 := by simpa only [d342790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45310 p hg
    simpa only [d342790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45312 (p : Pattern) (guard : d342791 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d342790 p = 1 := by simpa only [d342791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45311 p hg
    simpa only [d342791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d342791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45313 (p : Pattern) (guard : d342792 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d342792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342791 p = 1 := by simpa only [d342792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45312 p hg
    simpa only [d342792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45314 (p : Pattern) (guard : d342793 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d342793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342792 p = 1 := by simpa only [d342793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45313 p hg
    simpa only [d342793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45315 (p : Pattern) (guard : d342794 p = 1) : d51331 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342794, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d342794, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342793 p = 1 := by simpa only [d342794, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45314 p hg
    simpa only [d342794, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45316 (p : Pattern) (guard : d0 p = 1) : d51305 p ≤ (7 : Int) + d338724 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45317 (p : Pattern) (guard : d342727 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342727, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45316 p hg
    simpa only [d342727, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342726 p = 1 := by simpa only [d342727, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45304 p hg
    simpa only [d342727, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45318 (p : Pattern) (guard : d342728 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d342727 p = 1 := by simpa only [d342728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45317 p hg
    simpa only [d342728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d342728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45319 (p : Pattern) (guard : d342729 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d342728 p = 1 := by simpa only [d342729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45318 p hg
    simpa only [d342729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d342729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45320 (p : Pattern) (guard : d342730 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d342729 p = 1 := by simpa only [d342730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45319 p hg
    simpa only [d342730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d342730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45321 (p : Pattern) (guard : d342731 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d342731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342730 p = 1 := by simpa only [d342731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45320 p hg
    simpa only [d342731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45322 (p : Pattern) (guard : d342732 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d342731 p = 1 := by simpa only [d342732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45321 p hg
    simpa only [d342732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d342732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45323 (p : Pattern) (guard : d342790 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d342790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342732 p = 1 := by simpa only [d342790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45322 p hg
    simpa only [d342790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45324 (p : Pattern) (guard : d342791 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d342790 p = 1 := by simpa only [d342791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45323 p hg
    simpa only [d342791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d342791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45325 (p : Pattern) (guard : d342792 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d342792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342791 p = 1 := by simpa only [d342792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45324 p hg
    simpa only [d342792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45326 (p : Pattern) (guard : d342793 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d342793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342792 p = 1 := by simpa only [d342793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45325 p hg
    simpa only [d342793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45327 (p : Pattern) (guard : d342738 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d342730 p = 1 := by simpa only [d342738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45308 p hg
    simpa only [d342738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d342738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45328 (p : Pattern) (guard : d342739 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d342738 p = 1 := by simpa only [d342739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45327 p hg
    simpa only [d342739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d342739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45329 (p : Pattern) (guard : d342797 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d342797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342739 p = 1 := by simpa only [d342797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45328 p hg
    simpa only [d342797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45330 (p : Pattern) (guard : d342798 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d342797 p = 1 := by simpa only [d342798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45329 p hg
    simpa only [d342798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d342798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45331 (p : Pattern) (guard : d342799 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d342799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342798 p = 1 := by simpa only [d342799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45330 p hg
    simpa only [d342799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45332 (p : Pattern) (guard : d342800 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d342800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342799 p = 1 := by simpa only [d342800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45331 p hg
    simpa only [d342800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45333 (p : Pattern) (guard : d342801 p = 1) : d51331 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d342793 p = 1 := by simpa only [d342801, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45326 p hg
    simpa only [d342801, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342800 p = 1 := by simpa only [d342801, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45332 p hg
    simpa only [d342801, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45334 (p : Pattern) (guard : d342802 p = 1) : d51331 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 70 with
  | false =>
    have hg : d342794 p = 1 := by simpa only [d342802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45315 p hg
    simpa only [d342802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342801 p = 1 := by simpa only [d342802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45333 p hg
    simpa only [d342802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45335 (p : Pattern) (guard : d342803 p = 1) : d51331 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 69 with
  | false =>
    have hg : d342802 p = 1 := by simpa only [d342803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45334 p hg
    simpa only [d342803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45261 p hg
    simpa only [d342803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45336 (p : Pattern) (guard : d343966 p = 1) : d51331 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 51 with
  | false =>
    have hg : d342803 p = 1 := by simpa only [d343966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45335 p hg
    simpa only [d343966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45261 p hg
    simpa only [d343966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45337 (p : Pattern) (guard : d343967 p = 1) : d51331 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45261 p hg
    simpa only [d343967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343966 p = 1 := by simpa only [d343967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45336 p hg
    simpa only [d343967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45338 (p : Pattern) (guard : d0 p = 1) : d51469 p ≤ (7 : Int) + d338786 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45339 (p : Pattern) (guard : d0 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45340 (p : Pattern) (guard : d0 p = 1) : d51460 p ≤ (7 : Int) + d338782 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45341 (p : Pattern) (guard : d0 p = 1) : d51464 p ≤ (7 : Int) + d338765 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45342 (p : Pattern) (guard : d0 p = 1) : d51442 p ≤ (7 : Int) + d338770 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45343 (p : Pattern) (guard : d0 p = 1) : d51445 p ≤ (7 : Int) + d338753 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45344 (p : Pattern) (guard : d342715 p = 1) : d51447 p ≤ (7 : Int) + d338755 p := by
  have ha := bounds51447 p
  have hb := bounds338755 p
  omega
theorem compare45345 (p : Pattern) (guard : d342716 p = 1) : d51448 p ≤ (7 : Int) + d338756 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342716, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45343 p hg
    simpa only [d342716, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342715 p = 1 := by simpa only [d342716, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45344 p hg
    simpa only [d342716, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45346 (p : Pattern) (guard : d0 p = 1) : d51451 p ≤ (7 : Int) + d338773 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45347 (p : Pattern) (guard : d342717 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d342716 p = 1 := by simpa only [d342717, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45345 p hg
    simpa only [d342717, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342717, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45346 p hg
    simpa only [d342717, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45348 (p : Pattern) (guard : d0 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45349 (p : Pattern) (guard : d342718 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 159 with
  | false =>
    have hg : d342717 p = 1 := by simpa only [d342718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45347 p hg
    simpa only [d342718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45348 p hg
    simpa only [d342718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45350 (p : Pattern) (guard : d342719 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 158 with
  | false =>
    have hg : d342718 p = 1 := by simpa only [d342719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45349 p hg
    simpa only [d342719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45348 p hg
    simpa only [d342719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45351 (p : Pattern) (guard : d342720 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 157 with
  | false =>
    have hg : d342719 p = 1 := by simpa only [d342720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45350 p hg
    simpa only [d342720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45348 p hg
    simpa only [d342720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45352 (p : Pattern) (guard : d342721 p = 1) : d51453 p ≤ (7 : Int) + d338775 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342721, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45342 p hg
    simpa only [d342721, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342720 p = 1 := by simpa only [d342721, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45351 p hg
    simpa only [d342721, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45353 (p : Pattern) (guard : d342722 p = 1) : d51465 p ≤ (7 : Int) + d338776 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342722, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45341 p hg
    simpa only [d342722, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342721 p = 1 := by simpa only [d342722, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45352 p hg
    simpa only [d342722, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45354 (p : Pattern) (guard : d0 p = 1) : d51465 p ≤ (7 : Int) + d338776 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45355 (p : Pattern) (guard : d342723 p = 1) : d51465 p ≤ (7 : Int) + d338776 p := by
  cases selected : p 136 with
  | false =>
    have hg : d342722 p = 1 := by simpa only [d342723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45353 p hg
    simpa only [d342723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45354 p hg
    simpa only [d342723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45356 (p : Pattern) (guard : d342724 p = 1) : d51465 p ≤ (7 : Int) + d338776 p := by
  cases selected : p 135 with
  | false =>
    have hg : d342723 p = 1 := by simpa only [d342724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45355 p hg
    simpa only [d342724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45354 p hg
    simpa only [d342724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45357 (p : Pattern) (guard : d342725 p = 1) : d51465 p ≤ (7 : Int) + d338776 p := by
  cases selected : p 119 with
  | false =>
    have hg : d342724 p = 1 := by simpa only [d342725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45356 p hg
    simpa only [d342725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45354 p hg
    simpa only [d342725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45358 (p : Pattern) (guard : d0 p = 1) : d51466 p ≤ (7 : Int) + d338783 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45359 (p : Pattern) (guard : d342726 p = 1) : d51467 p ≤ (7 : Int) + d338784 p := by
  cases selected : p 116 with
  | false =>
    have hg : d342725 p = 1 := by simpa only [d342726, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45357 p hg
    simpa only [d342726, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342726, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45358 p hg
    simpa only [d342726, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45360 (p : Pattern) (guard : d342727 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342727, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45340 p hg
    simpa only [d342727, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342726 p = 1 := by simpa only [d342727, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45359 p hg
    simpa only [d342727, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45361 (p : Pattern) (guard : d342728 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 113 with
  | false =>
    have hg : d342727 p = 1 := by simpa only [d342728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45360 p hg
    simpa only [d342728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d342728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45362 (p : Pattern) (guard : d342729 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 96 with
  | false =>
    have hg : d342728 p = 1 := by simpa only [d342729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45361 p hg
    simpa only [d342729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d342729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45363 (p : Pattern) (guard : d342730 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 95 with
  | false =>
    have hg : d342729 p = 1 := by simpa only [d342730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45362 p hg
    simpa only [d342730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d342730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45364 (p : Pattern) (guard : d342738 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 93 with
  | false =>
    have hg : d342730 p = 1 := by simpa only [d342738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45363 p hg
    simpa only [d342738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d342738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45365 (p : Pattern) (guard : d342739 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 91 with
  | false =>
    have hg : d342738 p = 1 := by simpa only [d342739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45364 p hg
    simpa only [d342739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d342739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45366 (p : Pattern) (guard : d342797 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d342797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342739 p = 1 := by simpa only [d342797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45365 p hg
    simpa only [d342797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45367 (p : Pattern) (guard : d342798 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 89 with
  | false =>
    have hg : d342797 p = 1 := by simpa only [d342798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45366 p hg
    simpa only [d342798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d342798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45368 (p : Pattern) (guard : d342799 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d342799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342798 p = 1 := by simpa only [d342799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45367 p hg
    simpa only [d342799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45369 (p : Pattern) (guard : d342800 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d342800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342799 p = 1 := by simpa only [d342800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45368 p hg
    simpa only [d342800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45370 (p : Pattern) (guard : d343021 p = 1) : d51469 p ≤ (7 : Int) + d338786 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343021, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d343021, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342800 p = 1 := by simpa only [d343021, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45369 p hg
    simpa only [d343021, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45371 (p : Pattern) (guard : d343022 p = 1) : d51469 p ≤ (7 : Int) + d338786 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45338 p hg
    simpa only [d343022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343021 p = 1 := by simpa only [d343022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45370 p hg
    simpa only [d343022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45372 (p : Pattern) (guard : d343968 p = 1) : d51469 p ≤ (7 : Int) + d338786 p := by
  cases selected : p 69 with
  | false =>
    have hg : d343022 p = 1 := by simpa only [d343968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45371 p hg
    simpa only [d343968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45338 p hg
    simpa only [d343968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45373 (p : Pattern) (guard : d343969 p = 1) : d51469 p ≤ (7 : Int) + d338786 p := by
  cases selected : p 51 with
  | false =>
    have hg : d343968 p = 1 := by simpa only [d343969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45372 p hg
    simpa only [d343969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45338 p hg
    simpa only [d343969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45374 (p : Pattern) (guard : d343970 p = 1) : d51469 p ≤ (7 : Int) + d338786 p := by
  cases selected : p 50 with
  | false =>
    have hg : d343969 p = 1 := by simpa only [d343970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45373 p hg
    simpa only [d343970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45338 p hg
    simpa only [d343970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45375 (p : Pattern) (guard : d343971 p = 1) : d51470 p ≤ (7 : Int) + d338787 p := by
  cases selected : p 49 with
  | false =>
    have hg : d343967 p = 1 := by simpa only [d343971, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45337 p hg
    simpa only [d343971, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343970 p = 1 := by simpa only [d343971, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45374 p hg
    simpa only [d343971, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45376 (p : Pattern) (guard : d0 p = 1) : d51542 p ≤ (7 : Int) + d338826 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45377 (p : Pattern) (guard : d0 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45378 (p : Pattern) (guard : d0 p = 1) : d51508 p ≤ (7 : Int) + d338805 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45379 (p : Pattern) (guard : d0 p = 1) : d51523 p ≤ (7 : Int) + d338813 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45380 (p : Pattern) (guard : d0 p = 1) : d51528 p ≤ (7 : Int) + d338681 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45381 (p : Pattern) (guard : d0 p = 1) : d47629 p ≤ (7 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45382 (p : Pattern) (guard : d13 p = 1) : d2 p ≤ (7 : Int) + d2 p := by
  omega
theorem compare45383 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (7 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45384 (p : Pattern) (guard : d14 p = 1) : d47629 p ≤ (7 : Int) + d2 p := by
  cases selected : p 247 with
  | false =>
    have hg : d13 p = 1 := by simpa only [d14, d47629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45382 p hg
    simpa only [d14, d47629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14, d47629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45383 p hg
    simpa only [d14, d47629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45385 (p : Pattern) (guard : d1084 p = 1) : d47629 p ≤ (7 : Int) + d2 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45381 p hg
    simpa only [d1084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14 p = 1 := by simpa only [d1084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45384 p hg
    simpa only [d1084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45386 (p : Pattern) (guard : d1085 p = 1) : d47629 p ≤ (7 : Int) + d2 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1084 p = 1 := by simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45385 p hg
    simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45381 p hg
    simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45387 (p : Pattern) (guard : d1086 p = 1) : d47629 p ≤ (7 : Int) + d2 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1085 p = 1 := by simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45386 p hg
    simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45381 p hg
    simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45388 (p : Pattern) (guard : d9771 p = 1) : d47629 p ≤ (7 : Int) + d2 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1086 p = 1 := by simpa only [d9771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45387 p hg
    simpa only [d9771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45381 p hg
    simpa only [d9771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45389 (p : Pattern) (guard : d342708 p = 1) : d47629 p ≤ (7 : Int) + d2 p := by
  cases selected : p 223 with
  | false =>
    have hg : d9771 p = 1 := by simpa only [d342708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45388 p hg
    simpa only [d342708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45381 p hg
    simpa only [d342708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45390 (p : Pattern) (guard : d0 p = 1) : d51186 p ≤ (7 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45391 (p : Pattern) (guard : d342709 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 204 with
  | false =>
    have hg : d342708 p = 1 := by simpa only [d342709, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45389 p hg
    simpa only [d342709, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342709, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45390 p hg
    simpa only [d342709, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45392 (p : Pattern) (guard : d0 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45393 (p : Pattern) (guard : d342710 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d342709 p = 1 := by simpa only [d342710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45391 p hg
    simpa only [d342710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45392 p hg
    simpa only [d342710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45394 (p : Pattern) (guard : d342711 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 201 with
  | false =>
    have hg : d342710 p = 1 := by simpa only [d342711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45393 p hg
    simpa only [d342711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45392 p hg
    simpa only [d342711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45395 (p : Pattern) (guard : d0 p = 1) : d51187 p ≤ (7 : Int) + d338664 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45396 (p : Pattern) (guard : d342712 p = 1) : d51277 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 182 with
  | false =>
    have hg : d342711 p = 1 := by simpa only [d342712, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45394 p hg
    simpa only [d342712, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342712, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45395 p hg
    simpa only [d342712, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45397 (p : Pattern) (guard : d0 p = 1) : d51277 p ≤ (7 : Int) + d338681 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45398 (p : Pattern) (guard : d342713 p = 1) : d51277 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 180 with
  | false =>
    have hg : d342712 p = 1 := by simpa only [d342713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45396 p hg
    simpa only [d342713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45397 p hg
    simpa only [d342713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45399 (p : Pattern) (guard : d342755 p = 1) : d51529 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342755, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45380 p hg
    simpa only [d342755, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342713 p = 1 := by simpa only [d342755, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45398 p hg
    simpa only [d342755, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45400 (p : Pattern) (guard : d0 p = 1) : d51238 p ≤ (7 : Int) + d338688 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45401 (p : Pattern) (guard : d342714 p = 1) : d51530 p ≤ (7 : Int) + d338814 p := by
  cases selected : p 163 with
  | false =>
    have hg : d342713 p = 1 := by simpa only [d342714, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45285 p hg
    simpa only [d342714, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342714, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45400 p hg
    simpa only [d342714, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45402 (p : Pattern) (guard : d342756 p = 1) : d51531 p ≤ (7 : Int) + d338815 p := by
  cases selected : p 162 with
  | false =>
    have hg : d342755 p = 1 := by simpa only [d342756, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45399 p hg
    simpa only [d342756, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342714 p = 1 := by simpa only [d342756, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45401 p hg
    simpa only [d342756, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45403 (p : Pattern) (guard : d342715 p = 1) : d51291 p ≤ (7 : Int) + d338710 p := by
  have ha := bounds51291 p
  have hb := bounds338710 p
  omega
theorem compare45404 (p : Pattern) (guard : d342757 p = 1) : d51532 p ≤ (7 : Int) + d338816 p := by
  cases selected : p 161 with
  | false =>
    have hg : d342756 p = 1 := by simpa only [d342757, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45402 p hg
    simpa only [d342757, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342715 p = 1 := by simpa only [d342757, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45403 p hg
    simpa only [d342757, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45405 (p : Pattern) (guard : d0 p = 1) : d51535 p ≤ (7 : Int) + d338819 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45406 (p : Pattern) (guard : d342758 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d342757 p = 1 := by simpa only [d342758, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45404 p hg
    simpa only [d342758, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342758, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45405 p hg
    simpa only [d342758, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45407 (p : Pattern) (guard : d0 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45408 (p : Pattern) (guard : d342759 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 159 with
  | false =>
    have hg : d342758 p = 1 := by simpa only [d342759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45406 p hg
    simpa only [d342759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45407 p hg
    simpa only [d342759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45409 (p : Pattern) (guard : d342760 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 158 with
  | false =>
    have hg : d342759 p = 1 := by simpa only [d342760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45408 p hg
    simpa only [d342760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45407 p hg
    simpa only [d342760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45410 (p : Pattern) (guard : d342761 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 157 with
  | false =>
    have hg : d342760 p = 1 := by simpa only [d342761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45409 p hg
    simpa only [d342761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45407 p hg
    simpa only [d342761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45411 (p : Pattern) (guard : d342762 p = 1) : d51537 p ≤ (7 : Int) + d338821 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342762, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45379 p hg
    simpa only [d342762, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342761 p = 1 := by simpa only [d342762, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45410 p hg
    simpa only [d342762, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45412 (p : Pattern) (guard : d342763 p = 1) : d51538 p ≤ (7 : Int) + d338822 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342763, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45378 p hg
    simpa only [d342763, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342762 p = 1 := by simpa only [d342763, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45411 p hg
    simpa only [d342763, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45413 (p : Pattern) (guard : d0 p = 1) : d51538 p ≤ (7 : Int) + d338822 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45414 (p : Pattern) (guard : d342764 p = 1) : d51538 p ≤ (7 : Int) + d338822 p := by
  cases selected : p 136 with
  | false =>
    have hg : d342763 p = 1 := by simpa only [d342764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45412 p hg
    simpa only [d342764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45413 p hg
    simpa only [d342764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45415 (p : Pattern) (guard : d342765 p = 1) : d51538 p ≤ (7 : Int) + d338822 p := by
  cases selected : p 135 with
  | false =>
    have hg : d342764 p = 1 := by simpa only [d342765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45414 p hg
    simpa only [d342765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45413 p hg
    simpa only [d342765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45416 (p : Pattern) (guard : d342766 p = 1) : d51538 p ≤ (7 : Int) + d338822 p := by
  cases selected : p 119 with
  | false =>
    have hg : d342765 p = 1 := by simpa only [d342766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45415 p hg
    simpa only [d342766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45413 p hg
    simpa only [d342766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45417 (p : Pattern) (guard : d0 p = 1) : d51539 p ≤ (7 : Int) + d338823 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45418 (p : Pattern) (guard : d342767 p = 1) : d51540 p ≤ (7 : Int) + d338824 p := by
  cases selected : p 116 with
  | false =>
    have hg : d342766 p = 1 := by simpa only [d342767, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45416 p hg
    simpa only [d342767, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342767, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45417 p hg
    simpa only [d342767, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45419 (p : Pattern) (guard : d342768 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342768, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45264 p hg
    simpa only [d342768, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342767 p = 1 := by simpa only [d342768, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45418 p hg
    simpa only [d342768, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45420 (p : Pattern) (guard : d342769 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 113 with
  | false =>
    have hg : d342768 p = 1 := by simpa only [d342769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45419 p hg
    simpa only [d342769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d342769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45421 (p : Pattern) (guard : d342770 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 96 with
  | false =>
    have hg : d342769 p = 1 := by simpa only [d342770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45420 p hg
    simpa only [d342770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d342770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45422 (p : Pattern) (guard : d342771 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 95 with
  | false =>
    have hg : d342770 p = 1 := by simpa only [d342771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45421 p hg
    simpa only [d342771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d342771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45423 (p : Pattern) (guard : d342772 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 93 with
  | false =>
    have hg : d342771 p = 1 := by simpa only [d342772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45422 p hg
    simpa only [d342772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d342772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45424 (p : Pattern) (guard : d342773 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 91 with
  | false =>
    have hg : d342772 p = 1 := by simpa only [d342773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45423 p hg
    simpa only [d342773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d342773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45425 (p : Pattern) (guard : d343063 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d343063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342773 p = 1 := by simpa only [d343063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45424 p hg
    simpa only [d343063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45426 (p : Pattern) (guard : d343064 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 89 with
  | false =>
    have hg : d343063 p = 1 := by simpa only [d343064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45425 p hg
    simpa only [d343064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d343064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45427 (p : Pattern) (guard : d343065 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d343065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343064 p = 1 := by simpa only [d343065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45426 p hg
    simpa only [d343065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45428 (p : Pattern) (guard : d343066 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d343066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343065 p = 1 := by simpa only [d343066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45427 p hg
    simpa only [d343066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45429 (p : Pattern) (guard : d343067 p = 1) : d51542 p ≤ (7 : Int) + d338826 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343067, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d343067, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343066 p = 1 := by simpa only [d343067, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45428 p hg
    simpa only [d343067, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45430 (p : Pattern) (guard : d343068 p = 1) : d51542 p ≤ (7 : Int) + d338826 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45376 p hg
    simpa only [d343068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343067 p = 1 := by simpa only [d343068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45429 p hg
    simpa only [d343068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45431 (p : Pattern) (guard : d343972 p = 1) : d51542 p ≤ (7 : Int) + d338826 p := by
  cases selected : p 69 with
  | false =>
    have hg : d343068 p = 1 := by simpa only [d343972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45430 p hg
    simpa only [d343972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45376 p hg
    simpa only [d343972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45432 (p : Pattern) (guard : d343973 p = 1) : d51542 p ≤ (7 : Int) + d338826 p := by
  cases selected : p 51 with
  | false =>
    have hg : d343972 p = 1 := by simpa only [d343973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45431 p hg
    simpa only [d343973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45376 p hg
    simpa only [d343973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45433 (p : Pattern) (guard : d343974 p = 1) : d51542 p ≤ (7 : Int) + d338826 p := by
  cases selected : p 50 with
  | false =>
    have hg : d343973 p = 1 := by simpa only [d343974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45432 p hg
    simpa only [d343974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45376 p hg
    simpa only [d343974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45434 (p : Pattern) (guard : d0 p = 1) : d51633 p ≤ (7 : Int) + d338881 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare45435 (p : Pattern) (guard : d343975 p = 1) : d51634 p ≤ (7 : Int) + d338882 p := by
  cases selected : p 49 with
  | false =>
    have hg : d343974 p = 1 := by simpa only [d343975, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45433 p hg
    simpa only [d343975, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343975, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45434 p hg
    simpa only [d343975, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45436 (p : Pattern) (guard : d343976 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 48 with
  | false =>
    have hg : d343971 p = 1 := by simpa only [d343976, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45375 p hg
    simpa only [d343976, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343975 p = 1 := by simpa only [d343976, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45435 p hg
    simpa only [d343976, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45437 (p : Pattern) (guard : d343977 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d343977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343976 p = 1 := by simpa only [d343977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45436 p hg
    simpa only [d343977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45438 (p : Pattern) (guard : d343978 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d343978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343977 p = 1 := by simpa only [d343978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45437 p hg
    simpa only [d343978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45439 (p : Pattern) (guard : d343979 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d343979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343978 p = 1 := by simpa only [d343979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45438 p hg
    simpa only [d343979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45440 (p : Pattern) (guard : d343980 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d343980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343979 p = 1 := by simpa only [d343980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45439 p hg
    simpa only [d343980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45441 (p : Pattern) (guard : d343981 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d343981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343980 p = 1 := by simpa only [d343981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45440 p hg
    simpa only [d343981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45442 (p : Pattern) (guard : d343982 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d343982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343981 p = 1 := by simpa only [d343982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45441 p hg
    simpa only [d343982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45443 (p : Pattern) (guard : d127 p = 1) : d4 p ≤ (7 : Int) + d4 p := by
  omega
theorem compare45444 (p : Pattern) (guard : d308 p = 1) : d47616 p ≤ (7 : Int) + d4 p := by
  cases selected : p 247 with
  | false =>
    have hg : d127 p = 1 := by simpa only [d308, d47616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45443 p hg
    simpa only [d308, d47616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d308, d47616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45270 p hg
    simpa only [d308, d47616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45445 (p : Pattern) (guard : d1523 p = 1) : d47616 p ≤ (7 : Int) + d4 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45268 p hg
    simpa only [d1523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d308 p = 1 := by simpa only [d1523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45444 p hg
    simpa only [d1523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45446 (p : Pattern) (guard : d1524 p = 1) : d47616 p ≤ (7 : Int) + d4 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1523 p = 1 := by simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45445 p hg
    simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1084 p = 1 := by simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45272 p hg
    simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45447 (p : Pattern) (guard : d342817 p = 1) : d47616 p ≤ (7 : Int) + d4 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1524 p = 1 := by simpa only [d342817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45446 p hg
    simpa only [d342817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1085 p = 1 := by simpa only [d342817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45273 p hg
    simpa only [d342817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45448 (p : Pattern) (guard : d342818 p = 1) : d47616 p ≤ (7 : Int) + d4 p := by
  cases selected : p 224 with
  | false =>
    have hg : d342817 p = 1 := by simpa only [d342818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45447 p hg
    simpa only [d342818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1086 p = 1 := by simpa only [d342818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45274 p hg
    simpa only [d342818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45449 (p : Pattern) (guard : d342819 p = 1) : d47616 p ≤ (7 : Int) + d4 p := by
  cases selected : p 223 with
  | false =>
    have hg : d342818 p = 1 := by simpa only [d342819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45448 p hg
    simpa only [d342819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45268 p hg
    simpa only [d342819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45450 (p : Pattern) (guard : d342820 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 204 with
  | false =>
    have hg : d342819 p = 1 := by simpa only [d342820, d51204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45449 p hg
    simpa only [d342820, d51204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342820, d51204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45277 p hg
    simpa only [d342820, d51204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45451 (p : Pattern) (guard : d342821 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 202 with
  | false =>
    have hg : d342820 p = 1 := by simpa only [d342821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45450 p hg
    simpa only [d342821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342709 p = 1 := by simpa only [d342821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45278 p hg
    simpa only [d342821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45452 (p : Pattern) (guard : d342822 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 201 with
  | false =>
    have hg : d342821 p = 1 := by simpa only [d342822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45451 p hg
    simpa only [d342822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342710 p = 1 := by simpa only [d342822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45280 p hg
    simpa only [d342822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45453 (p : Pattern) (guard : d342823 p = 1) : d51269 p ≤ (7 : Int) + d338656 p := by
  cases selected : p 182 with
  | false =>
    have hg : d342822 p = 1 := by simpa only [d342823, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45452 p hg
    simpa only [d342823, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342823, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45282 p hg
    simpa only [d342823, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45454 (p : Pattern) (guard : d342824 p = 1) : d51269 p ≤ (7 : Int) + d338656 p := by
  cases selected : p 180 with
  | false =>
    have hg : d342823 p = 1 := by simpa only [d342824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45453 p hg
    simpa only [d342824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342712 p = 1 := by simpa only [d342824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45283 p hg
    simpa only [d342824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45455 (p : Pattern) (guard : d342825 p = 1) : d51287 p ≤ (7 : Int) + d338687 p := by
  cases selected : p 163 with
  | false =>
    have hg : d342824 p = 1 := by simpa only [d342825, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45454 p hg
    simpa only [d342825, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342825, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45286 p hg
    simpa only [d342825, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45456 (p : Pattern) (guard : d342826 p = 1) : d51288 p ≤ (7 : Int) + d338690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d342825 p = 1 := by simpa only [d342826, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45455 p hg
    simpa only [d342826, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342826, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45288 p hg
    simpa only [d342826, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45457 (p : Pattern) (guard : d342827 p = 1) : d51289 p ≤ (7 : Int) + d338691 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342827, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45267 p hg
    simpa only [d342827, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342826 p = 1 := by simpa only [d342827, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45456 p hg
    simpa only [d342827, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45458 (p : Pattern) (guard : d342828 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 160 with
  | false =>
    have hg : d342827 p = 1 := by simpa only [d342828, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45457 p hg
    simpa only [d342828, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342828, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45291 p hg
    simpa only [d342828, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45459 (p : Pattern) (guard : d342829 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 159 with
  | false =>
    have hg : d342828 p = 1 := by simpa only [d342829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45458 p hg
    simpa only [d342829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342717 p = 1 := by simpa only [d342829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45292 p hg
    simpa only [d342829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45460 (p : Pattern) (guard : d342830 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 158 with
  | false =>
    have hg : d342829 p = 1 := by simpa only [d342830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45459 p hg
    simpa only [d342830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342718 p = 1 := by simpa only [d342830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45294 p hg
    simpa only [d342830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45461 (p : Pattern) (guard : d342831 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 157 with
  | false =>
    have hg : d342830 p = 1 := by simpa only [d342831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45460 p hg
    simpa only [d342831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342719 p = 1 := by simpa only [d342831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45295 p hg
    simpa only [d342831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45462 (p : Pattern) (guard : d342832 p = 1) : d51294 p ≤ (7 : Int) + d338713 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342832, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45266 p hg
    simpa only [d342832, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342831 p = 1 := by simpa only [d342832, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45461 p hg
    simpa only [d342832, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45463 (p : Pattern) (guard : d342833 p = 1) : d51314 p ≤ (7 : Int) + d338714 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342833, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45265 p hg
    simpa only [d342833, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342832 p = 1 := by simpa only [d342833, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45462 p hg
    simpa only [d342833, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45464 (p : Pattern) (guard : d342834 p = 1) : d51314 p ≤ (7 : Int) + d338714 p := by
  cases selected : p 136 with
  | false =>
    have hg : d342833 p = 1 := by simpa only [d342834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45463 p hg
    simpa only [d342834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342722 p = 1 := by simpa only [d342834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45298 p hg
    simpa only [d342834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45465 (p : Pattern) (guard : d342835 p = 1) : d51314 p ≤ (7 : Int) + d338714 p := by
  cases selected : p 135 with
  | false =>
    have hg : d342834 p = 1 := by simpa only [d342835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45464 p hg
    simpa only [d342835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342723 p = 1 := by simpa only [d342835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45300 p hg
    simpa only [d342835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45466 (p : Pattern) (guard : d342836 p = 1) : d51314 p ≤ (7 : Int) + d338714 p := by
  cases selected : p 119 with
  | false =>
    have hg : d342835 p = 1 := by simpa only [d342836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45465 p hg
    simpa only [d342836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45299 p hg
    simpa only [d342836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45467 (p : Pattern) (guard : d342837 p = 1) : d51316 p ≤ (7 : Int) + d338726 p := by
  cases selected : p 116 with
  | false =>
    have hg : d342836 p = 1 := by simpa only [d342837, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45466 p hg
    simpa only [d342837, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342837, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45303 p hg
    simpa only [d342837, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45468 (p : Pattern) (guard : d342838 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342838, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45264 p hg
    simpa only [d342838, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342837 p = 1 := by simpa only [d342838, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45467 p hg
    simpa only [d342838, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45469 (p : Pattern) (guard : d342839 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d342838 p = 1 := by simpa only [d342839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45468 p hg
    simpa only [d342839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342727 p = 1 := by simpa only [d342839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45305 p hg
    simpa only [d342839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45470 (p : Pattern) (guard : d342840 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d342839 p = 1 := by simpa only [d342840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45469 p hg
    simpa only [d342840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d342840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45471 (p : Pattern) (guard : d342841 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d342840 p = 1 := by simpa only [d342841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45470 p hg
    simpa only [d342841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d342841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45472 (p : Pattern) (guard : d342842 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d342842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342841 p = 1 := by simpa only [d342842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45471 p hg
    simpa only [d342842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45473 (p : Pattern) (guard : d342843 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d342842 p = 1 := by simpa only [d342843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45472 p hg
    simpa only [d342843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342731 p = 1 := by simpa only [d342843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45309 p hg
    simpa only [d342843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45474 (p : Pattern) (guard : d342915 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d342915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342843 p = 1 := by simpa only [d342915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45473 p hg
    simpa only [d342915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45475 (p : Pattern) (guard : d342916 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d342915 p = 1 := by simpa only [d342916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45474 p hg
    simpa only [d342916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d342916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45476 (p : Pattern) (guard : d342917 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d342917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342916 p = 1 := by simpa only [d342917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45475 p hg
    simpa only [d342917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45477 (p : Pattern) (guard : d342918 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d342918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342917 p = 1 := by simpa only [d342918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45476 p hg
    simpa only [d342918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45478 (p : Pattern) (guard : d342919 p = 1) : d51331 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342919, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d342919, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342918 p = 1 := by simpa only [d342919, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45477 p hg
    simpa only [d342919, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45479 (p : Pattern) (guard : d342838 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342838, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45316 p hg
    simpa only [d342838, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342837 p = 1 := by simpa only [d342838, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45467 p hg
    simpa only [d342838, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45480 (p : Pattern) (guard : d342839 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d342838 p = 1 := by simpa only [d342839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45479 p hg
    simpa only [d342839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342727 p = 1 := by simpa only [d342839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45317 p hg
    simpa only [d342839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45481 (p : Pattern) (guard : d342840 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d342839 p = 1 := by simpa only [d342840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45480 p hg
    simpa only [d342840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d342840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45482 (p : Pattern) (guard : d342841 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d342840 p = 1 := by simpa only [d342841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45481 p hg
    simpa only [d342841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d342841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45483 (p : Pattern) (guard : d342842 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d342842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342841 p = 1 := by simpa only [d342842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45482 p hg
    simpa only [d342842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45484 (p : Pattern) (guard : d342843 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d342842 p = 1 := by simpa only [d342843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45483 p hg
    simpa only [d342843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342731 p = 1 := by simpa only [d342843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45321 p hg
    simpa only [d342843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45485 (p : Pattern) (guard : d342915 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d342915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342843 p = 1 := by simpa only [d342915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45484 p hg
    simpa only [d342915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45486 (p : Pattern) (guard : d342916 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d342915 p = 1 := by simpa only [d342916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45485 p hg
    simpa only [d342916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d342916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45487 (p : Pattern) (guard : d342917 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d342917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342916 p = 1 := by simpa only [d342917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45486 p hg
    simpa only [d342917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45488 (p : Pattern) (guard : d342918 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d342918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342917 p = 1 := by simpa only [d342918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45487 p hg
    simpa only [d342918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45489 (p : Pattern) (guard : d342858 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d342841 p = 1 := by simpa only [d342858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45471 p hg
    simpa only [d342858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d342858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45490 (p : Pattern) (guard : d342859 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d342858 p = 1 := by simpa only [d342859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45489 p hg
    simpa only [d342859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342738 p = 1 := by simpa only [d342859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45327 p hg
    simpa only [d342859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45491 (p : Pattern) (guard : d342922 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d342922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342859 p = 1 := by simpa only [d342922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45490 p hg
    simpa only [d342922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45492 (p : Pattern) (guard : d342923 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d342922 p = 1 := by simpa only [d342923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45491 p hg
    simpa only [d342923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d342923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45493 (p : Pattern) (guard : d342924 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d342924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342923 p = 1 := by simpa only [d342924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45492 p hg
    simpa only [d342924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45494 (p : Pattern) (guard : d342925 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d342925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342924 p = 1 := by simpa only [d342925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45493 p hg
    simpa only [d342925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45495 (p : Pattern) (guard : d342926 p = 1) : d51331 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d342918 p = 1 := by simpa only [d342926, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45488 p hg
    simpa only [d342926, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342925 p = 1 := by simpa only [d342926, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45494 p hg
    simpa only [d342926, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45496 (p : Pattern) (guard : d342927 p = 1) : d51331 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 70 with
  | false =>
    have hg : d342919 p = 1 := by simpa only [d342927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45478 p hg
    simpa only [d342927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342926 p = 1 := by simpa only [d342927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45495 p hg
    simpa only [d342927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45497 (p : Pattern) (guard : d342928 p = 1) : d51331 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 69 with
  | false =>
    have hg : d342927 p = 1 := by simpa only [d342928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45496 p hg
    simpa only [d342928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45261 p hg
    simpa only [d342928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45498 (p : Pattern) (guard : d343983 p = 1) : d51331 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 51 with
  | false =>
    have hg : d342928 p = 1 := by simpa only [d343983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45497 p hg
    simpa only [d343983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45261 p hg
    simpa only [d343983, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45499 (p : Pattern) (guard : d343984 p = 1) : d51331 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45261 p hg
    simpa only [d343984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343983 p = 1 := by simpa only [d343984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45498 p hg
    simpa only [d343984, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
