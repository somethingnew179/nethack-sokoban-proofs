import NetHack.Soko22Hazard87.Compare040
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare10250 (p : Pattern) (guard : d101917 p = 1) : d48307 p ≤ (1 : Int) + d47910 p := by
  cases selected : p 49 with
  | false =>
    have hg : d101916 p = 1 := by simpa only [d101917, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10249 p hg
    simpa only [d101917, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d101917, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10117 p hg
    simpa only [d101917, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10251 (p : Pattern) (guard : d101918 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101918, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10086 p hg
    simpa only [d101918, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101917 p = 1 := by simpa only [d101918, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10250 p hg
    simpa only [d101918, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10252 (p : Pattern) (guard : d101919 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d101919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101918 p = 1 := by simpa only [d101919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10251 p hg
    simpa only [d101919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10253 (p : Pattern) (guard : d101920 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d101920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101919 p = 1 := by simpa only [d101920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10252 p hg
    simpa only [d101920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10254 (p : Pattern) (guard : d101921 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d101921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101920 p = 1 := by simpa only [d101921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10253 p hg
    simpa only [d101921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10255 (p : Pattern) (guard : d101922 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d101922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101921 p = 1 := by simpa only [d101922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10254 p hg
    simpa only [d101922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10256 (p : Pattern) (guard : d101923 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d101923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101922 p = 1 := by simpa only [d101923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10255 p hg
    simpa only [d101923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10257 (p : Pattern) (guard : d101924 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d101924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101923 p = 1 := by simpa only [d101924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10256 p hg
    simpa only [d101924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10258 (p : Pattern) (guard : d101925 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d101907 p = 1 := by simpa only [d101925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10194 p hg
    simpa only [d101925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101924 p = 1 := by simpa only [d101925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10257 p hg
    simpa only [d101925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10259 (p : Pattern) (guard : d9609 p = 1) : d47681 p ≤ (1 : Int) + d47681 p := by
  omega
theorem compare10260 (p : Pattern) (guard : d9610 p = 1) : d48273 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d9609 p = 1 := by simpa only [d9610, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10259 p hg
    simpa only [d9610, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9610, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10094 p hg
    simpa only [d9610, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10261 (p : Pattern) (guard : d9611 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9611, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10092 p hg
    simpa only [d9611, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9610 p = 1 := by simpa only [d9611, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10260 p hg
    simpa only [d9611, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10262 (p : Pattern) (guard : d9614 p = 1) : d47681 p ≤ (1 : Int) + d47681 p := by
  omega
theorem compare10263 (p : Pattern) (guard : d9615 p = 1) : d48273 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d9614 p = 1 := by simpa only [d9615, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10262 p hg
    simpa only [d9615, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9615, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10094 p hg
    simpa only [d9615, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10264 (p : Pattern) (guard : d9616 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9616, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10092 p hg
    simpa only [d9616, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9615 p = 1 := by simpa only [d9616, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10263 p hg
    simpa only [d9616, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10265 (p : Pattern) (guard : d9617 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d9611 p = 1 := by simpa only [d9617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10261 p hg
    simpa only [d9617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9616 p = 1 := by simpa only [d9617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10264 p hg
    simpa only [d9617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10266 (p : Pattern) (guard : d9620 p = 1) : d47681 p ≤ (1 : Int) + d47681 p := by
  omega
theorem compare10267 (p : Pattern) (guard : d9621 p = 1) : d48273 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d9620 p = 1 := by simpa only [d9621, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10266 p hg
    simpa only [d9621, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9621, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10094 p hg
    simpa only [d9621, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10268 (p : Pattern) (guard : d9622 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9622, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10092 p hg
    simpa only [d9622, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9621 p = 1 := by simpa only [d9622, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10267 p hg
    simpa only [d9622, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10269 (p : Pattern) (guard : d9624 p = 1) : d47681 p ≤ (1 : Int) + d47681 p := by
  omega
theorem compare10270 (p : Pattern) (guard : d9625 p = 1) : d48273 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d9624 p = 1 := by simpa only [d9625, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10269 p hg
    simpa only [d9625, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9625, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10094 p hg
    simpa only [d9625, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10271 (p : Pattern) (guard : d9626 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9626, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10092 p hg
    simpa only [d9626, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9625 p = 1 := by simpa only [d9626, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10270 p hg
    simpa only [d9626, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10272 (p : Pattern) (guard : d9627 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d9622 p = 1 := by simpa only [d9627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10268 p hg
    simpa only [d9627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9626 p = 1 := by simpa only [d9627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10271 p hg
    simpa only [d9627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10273 (p : Pattern) (guard : d9628 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d9617 p = 1 := by simpa only [d9628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10265 p hg
    simpa only [d9628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9627 p = 1 := by simpa only [d9628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10272 p hg
    simpa only [d9628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10274 (p : Pattern) (guard : d9629 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d9629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9628 p = 1 := by simpa only [d9629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10273 p hg
    simpa only [d9629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10275 (p : Pattern) (guard : d9630 p = 1) : d48276 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d9629 p = 1 := by simpa only [d9630, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10274 p hg
    simpa only [d9630, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9630, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10100 p hg
    simpa only [d9630, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10276 (p : Pattern) (guard : d9631 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9631, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10090 p hg
    simpa only [d9631, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9630 p = 1 := by simpa only [d9631, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10275 p hg
    simpa only [d9631, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10277 (p : Pattern) (guard : d9632 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d9626 p = 1 := by simpa only [d9632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10271 p hg
    simpa only [d9632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d9632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10278 (p : Pattern) (guard : d9633 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d9627 p = 1 := by simpa only [d9633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10272 p hg
    simpa only [d9633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9632 p = 1 := by simpa only [d9633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10277 p hg
    simpa only [d9633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10279 (p : Pattern) (guard : d9634 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d9634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9633 p = 1 := by simpa only [d9634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10278 p hg
    simpa only [d9634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10280 (p : Pattern) (guard : d9635 p = 1) : d48276 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d9634 p = 1 := by simpa only [d9635, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10279 p hg
    simpa only [d9635, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9635, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10100 p hg
    simpa only [d9635, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10281 (p : Pattern) (guard : d9636 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9636, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10090 p hg
    simpa only [d9636, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9635 p = 1 := by simpa only [d9636, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10280 p hg
    simpa only [d9636, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10282 (p : Pattern) (guard : d9637 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d9631 p = 1 := by simpa only [d9637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10276 p hg
    simpa only [d9637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9636 p = 1 := by simpa only [d9637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10281 p hg
    simpa only [d9637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10283 (p : Pattern) (guard : d9638 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d9637 p = 1 := by simpa only [d9638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10282 p hg
    simpa only [d9638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10284 (p : Pattern) (guard : d9639 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d9638 p = 1 := by simpa only [d9639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10283 p hg
    simpa only [d9639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10285 (p : Pattern) (guard : d9640 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d9639 p = 1 := by simpa only [d9640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10284 p hg
    simpa only [d9640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10286 (p : Pattern) (guard : d9641 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d9632 p = 1 := by simpa only [d9641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10277 p hg
    simpa only [d9641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d9641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10287 (p : Pattern) (guard : d9642 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d9642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9641 p = 1 := by simpa only [d9642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10286 p hg
    simpa only [d9642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10288 (p : Pattern) (guard : d9643 p = 1) : d48276 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d9642 p = 1 := by simpa only [d9643, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10287 p hg
    simpa only [d9643, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9643, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10100 p hg
    simpa only [d9643, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10289 (p : Pattern) (guard : d9644 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9644, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10090 p hg
    simpa only [d9644, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9643 p = 1 := by simpa only [d9644, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10288 p hg
    simpa only [d9644, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10290 (p : Pattern) (guard : d9645 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d9636 p = 1 := by simpa only [d9645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10281 p hg
    simpa only [d9645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9644 p = 1 := by simpa only [d9645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10289 p hg
    simpa only [d9645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10291 (p : Pattern) (guard : d9646 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d9645 p = 1 := by simpa only [d9646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10290 p hg
    simpa only [d9646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10292 (p : Pattern) (guard : d9647 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d9646 p = 1 := by simpa only [d9647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10291 p hg
    simpa only [d9647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10293 (p : Pattern) (guard : d9648 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d9647 p = 1 := by simpa only [d9648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10292 p hg
    simpa only [d9648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10294 (p : Pattern) (guard : d9649 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d9640 p = 1 := by simpa only [d9649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10285 p hg
    simpa only [d9649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9648 p = 1 := by simpa only [d9649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10293 p hg
    simpa only [d9649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10295 (p : Pattern) (guard : d101926 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d9649 p = 1 := by simpa only [d101926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10294 p hg
    simpa only [d101926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d101926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d101926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10296 (p : Pattern) (guard : d9711 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d9636 p = 1 := by simpa only [d9711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10281 p hg
    simpa only [d9711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10297 (p : Pattern) (guard : d9712 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d9711 p = 1 := by simpa only [d9712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10296 p hg
    simpa only [d9712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10298 (p : Pattern) (guard : d9713 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d9712 p = 1 := by simpa only [d9713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10297 p hg
    simpa only [d9713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10299 (p : Pattern) (guard : d9714 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d9713 p = 1 := by simpa only [d9714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10298 p hg
    simpa only [d9714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10300 (p : Pattern) (guard : d9715 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d9714 p = 1 := by simpa only [d9715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10299 p hg
    simpa only [d9715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10301 (p : Pattern) (guard : d9716 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d9715 p = 1 := by simpa only [d9716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10300 p hg
    simpa only [d9716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10302 (p : Pattern) (guard : d101927 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d101926 p = 1 := by simpa only [d101927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10295 p hg
    simpa only [d101927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9716 p = 1 := by simpa only [d101927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10301 p hg
    simpa only [d101927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10303 (p : Pattern) (guard : d101928 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d101928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101927 p = 1 := by simpa only [d101928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10302 p hg
    simpa only [d101928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10304 (p : Pattern) (guard : d101929 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d101929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101928 p = 1 := by simpa only [d101929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10303 p hg
    simpa only [d101929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10305 (p : Pattern) (guard : d101930 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101930, d48278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10088 p hg
    simpa only [d101930, d48278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101929 p = 1 := by simpa only [d101930, d48278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10304 p hg
    simpa only [d101930, d48278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10306 (p : Pattern) (guard : d101931 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10087 p hg
    simpa only [d101931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101930 p = 1 := by simpa only [d101931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10305 p hg
    simpa only [d101931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10307 (p : Pattern) (guard : d9722 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d9644 p = 1 := by simpa only [d9722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10289 p hg
    simpa only [d9722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10308 (p : Pattern) (guard : d9723 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d9722 p = 1 := by simpa only [d9723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10307 p hg
    simpa only [d9723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10309 (p : Pattern) (guard : d9724 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d9723 p = 1 := by simpa only [d9724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10308 p hg
    simpa only [d9724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10310 (p : Pattern) (guard : d9725 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d9724 p = 1 := by simpa only [d9725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10309 p hg
    simpa only [d9725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10311 (p : Pattern) (guard : d9726 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d9725 p = 1 := by simpa only [d9726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10310 p hg
    simpa only [d9726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10312 (p : Pattern) (guard : d9727 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9726 p = 1 := by simpa only [d9727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10311 p hg
    simpa only [d9727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10313 (p : Pattern) (guard : d9728 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d9727 p = 1 := by simpa only [d9728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10312 p hg
    simpa only [d9728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10314 (p : Pattern) (guard : d9729 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9728 p = 1 := by simpa only [d9729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10313 p hg
    simpa only [d9729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10315 (p : Pattern) (guard : d9730 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9729 p = 1 := by simpa only [d9730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10314 p hg
    simpa only [d9730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10316 (p : Pattern) (guard : d9731 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9731, d48278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10088 p hg
    simpa only [d9731, d48278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9730 p = 1 := by simpa only [d9731, d48278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10315 p hg
    simpa only [d9731, d48278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10317 (p : Pattern) (guard : d9732 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10087 p hg
    simpa only [d9732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9731 p = 1 := by simpa only [d9732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10316 p hg
    simpa only [d9732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10318 (p : Pattern) (guard : d101932 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d101931 p = 1 := by simpa only [d101932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10306 p hg
    simpa only [d101932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9732 p = 1 := by simpa only [d101932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10317 p hg
    simpa only [d101932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10319 (p : Pattern) (guard : d101933 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d101932 p = 1 := by simpa only [d101933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10318 p hg
    simpa only [d101933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d101933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10087 p hg
    simpa only [d101933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10320 (p : Pattern) (guard : d101934 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d101933 p = 1 := by simpa only [d101934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10319 p hg
    simpa only [d101934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d101934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10087 p hg
    simpa only [d101934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10321 (p : Pattern) (guard : d101935 p = 1) : d48307 p ≤ (1 : Int) + d47910 p := by
  cases selected : p 49 with
  | false =>
    have hg : d101934 p = 1 := by simpa only [d101935, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10320 p hg
    simpa only [d101935, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d101935, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10117 p hg
    simpa only [d101935, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10322 (p : Pattern) (guard : d101936 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101936, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10086 p hg
    simpa only [d101936, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101935 p = 1 := by simpa only [d101936, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10321 p hg
    simpa only [d101936, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10323 (p : Pattern) (guard : d101937 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d101937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101936 p = 1 := by simpa only [d101937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10322 p hg
    simpa only [d101937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10324 (p : Pattern) (guard : d101938 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d101938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101937 p = 1 := by simpa only [d101938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10323 p hg
    simpa only [d101938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10325 (p : Pattern) (guard : d101939 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d101939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101938 p = 1 := by simpa only [d101939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10324 p hg
    simpa only [d101939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10326 (p : Pattern) (guard : d101940 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d101940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101939 p = 1 := by simpa only [d101940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10325 p hg
    simpa only [d101940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10327 (p : Pattern) (guard : d101941 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d101941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101940 p = 1 := by simpa only [d101941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10326 p hg
    simpa only [d101941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10328 (p : Pattern) (guard : d101942 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d101942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101941 p = 1 := by simpa only [d101942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10327 p hg
    simpa only [d101942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10329 (p : Pattern) (guard : d101943 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d101943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101942 p = 1 := by simpa only [d101943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10328 p hg
    simpa only [d101943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10330 (p : Pattern) (guard : d101944 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d101925 p = 1 := by simpa only [d101944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10258 p hg
    simpa only [d101944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101943 p = 1 := by simpa only [d101944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10329 p hg
    simpa only [d101944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10331 (p : Pattern) (guard : d9807 p = 1) : d47681 p ≤ (1 : Int) + d47681 p := by
  omega
theorem compare10332 (p : Pattern) (guard : d9808 p = 1) : d48273 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d9807 p = 1 := by simpa only [d9808, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10331 p hg
    simpa only [d9808, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9808, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10094 p hg
    simpa only [d9808, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10333 (p : Pattern) (guard : d9809 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9809, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10092 p hg
    simpa only [d9809, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9808 p = 1 := by simpa only [d9809, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10332 p hg
    simpa only [d9809, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10334 (p : Pattern) (guard : d9822 p = 1) : d47681 p ≤ (1 : Int) + d47681 p := by
  omega
theorem compare10335 (p : Pattern) (guard : d9823 p = 1) : d48273 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d9822 p = 1 := by simpa only [d9823, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10334 p hg
    simpa only [d9823, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9823, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10094 p hg
    simpa only [d9823, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10336 (p : Pattern) (guard : d9824 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9824, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10092 p hg
    simpa only [d9824, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9823 p = 1 := by simpa only [d9824, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10335 p hg
    simpa only [d9824, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10337 (p : Pattern) (guard : d9825 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d9809 p = 1 := by simpa only [d9825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10333 p hg
    simpa only [d9825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9824 p = 1 := by simpa only [d9825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10336 p hg
    simpa only [d9825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10338 (p : Pattern) (guard : d9834 p = 1) : d47681 p ≤ (1 : Int) + d47681 p := by
  omega
theorem compare10339 (p : Pattern) (guard : d9835 p = 1) : d48273 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d9834 p = 1 := by simpa only [d9835, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10338 p hg
    simpa only [d9835, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9835, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10094 p hg
    simpa only [d9835, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10340 (p : Pattern) (guard : d9836 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9836, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10092 p hg
    simpa only [d9836, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9835 p = 1 := by simpa only [d9836, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10339 p hg
    simpa only [d9836, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10341 (p : Pattern) (guard : d9851 p = 1) : d47681 p ≤ (1 : Int) + d47681 p := by
  omega
theorem compare10342 (p : Pattern) (guard : d9852 p = 1) : d48273 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d9851 p = 1 := by simpa only [d9852, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10341 p hg
    simpa only [d9852, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9852, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10094 p hg
    simpa only [d9852, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10343 (p : Pattern) (guard : d9853 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9853, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10092 p hg
    simpa only [d9853, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9852 p = 1 := by simpa only [d9853, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10342 p hg
    simpa only [d9853, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10344 (p : Pattern) (guard : d9854 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d9836 p = 1 := by simpa only [d9854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10340 p hg
    simpa only [d9854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9853 p = 1 := by simpa only [d9854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10343 p hg
    simpa only [d9854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10345 (p : Pattern) (guard : d9855 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d9825 p = 1 := by simpa only [d9855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10337 p hg
    simpa only [d9855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9854 p = 1 := by simpa only [d9855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10344 p hg
    simpa only [d9855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10346 (p : Pattern) (guard : d9856 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d9856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9855 p = 1 := by simpa only [d9856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10345 p hg
    simpa only [d9856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10347 (p : Pattern) (guard : d9857 p = 1) : d48276 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d9856 p = 1 := by simpa only [d9857, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10346 p hg
    simpa only [d9857, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9857, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10100 p hg
    simpa only [d9857, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10348 (p : Pattern) (guard : d9858 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9858, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10090 p hg
    simpa only [d9858, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9857 p = 1 := by simpa only [d9858, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10347 p hg
    simpa only [d9858, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10349 (p : Pattern) (guard : d9859 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d9853 p = 1 := by simpa only [d9859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10343 p hg
    simpa only [d9859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d9859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10350 (p : Pattern) (guard : d9860 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d9854 p = 1 := by simpa only [d9860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10344 p hg
    simpa only [d9860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9859 p = 1 := by simpa only [d9860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10349 p hg
    simpa only [d9860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10351 (p : Pattern) (guard : d9861 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d9861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9860 p = 1 := by simpa only [d9861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10350 p hg
    simpa only [d9861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10352 (p : Pattern) (guard : d9862 p = 1) : d48276 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d9861 p = 1 := by simpa only [d9862, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10351 p hg
    simpa only [d9862, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9862, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10100 p hg
    simpa only [d9862, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10353 (p : Pattern) (guard : d9863 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9863, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10090 p hg
    simpa only [d9863, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9862 p = 1 := by simpa only [d9863, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10352 p hg
    simpa only [d9863, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10354 (p : Pattern) (guard : d9864 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d9858 p = 1 := by simpa only [d9864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10348 p hg
    simpa only [d9864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9863 p = 1 := by simpa only [d9864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10353 p hg
    simpa only [d9864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10355 (p : Pattern) (guard : d9865 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d9864 p = 1 := by simpa only [d9865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10354 p hg
    simpa only [d9865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10356 (p : Pattern) (guard : d9866 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d9865 p = 1 := by simpa only [d9866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10355 p hg
    simpa only [d9866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10357 (p : Pattern) (guard : d9867 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d9866 p = 1 := by simpa only [d9867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10356 p hg
    simpa only [d9867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10358 (p : Pattern) (guard : d9870 p = 1) : d47681 p ≤ (1 : Int) + d47681 p := by
  omega
theorem compare10359 (p : Pattern) (guard : d9871 p = 1) : d48273 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d9870 p = 1 := by simpa only [d9871, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10358 p hg
    simpa only [d9871, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9871, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10094 p hg
    simpa only [d9871, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10360 (p : Pattern) (guard : d9872 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9872, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10092 p hg
    simpa only [d9872, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9871 p = 1 := by simpa only [d9872, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10359 p hg
    simpa only [d9872, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10361 (p : Pattern) (guard : d9873 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d9872 p = 1 := by simpa only [d9873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10360 p hg
    simpa only [d9873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d9873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10362 (p : Pattern) (guard : d9874 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d9873 p = 1 := by simpa only [d9874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10361 p hg
    simpa only [d9874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d9874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10363 (p : Pattern) (guard : d9875 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d9875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9874 p = 1 := by simpa only [d9875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10362 p hg
    simpa only [d9875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10364 (p : Pattern) (guard : d9876 p = 1) : d48276 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d9875 p = 1 := by simpa only [d9876, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10363 p hg
    simpa only [d9876, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9876, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10100 p hg
    simpa only [d9876, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10365 (p : Pattern) (guard : d9877 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9877, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10090 p hg
    simpa only [d9877, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9876 p = 1 := by simpa only [d9877, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10364 p hg
    simpa only [d9877, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10366 (p : Pattern) (guard : d9878 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d9863 p = 1 := by simpa only [d9878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10353 p hg
    simpa only [d9878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9877 p = 1 := by simpa only [d9878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10365 p hg
    simpa only [d9878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10367 (p : Pattern) (guard : d9879 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d9878 p = 1 := by simpa only [d9879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10366 p hg
    simpa only [d9879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10368 (p : Pattern) (guard : d9880 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d9879 p = 1 := by simpa only [d9880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10367 p hg
    simpa only [d9880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10369 (p : Pattern) (guard : d9881 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d9880 p = 1 := by simpa only [d9881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10368 p hg
    simpa only [d9881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10370 (p : Pattern) (guard : d9882 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d9867 p = 1 := by simpa only [d9882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10357 p hg
    simpa only [d9882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9881 p = 1 := by simpa only [d9882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10369 p hg
    simpa only [d9882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10371 (p : Pattern) (guard : d101945 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d9882 p = 1 := by simpa only [d101945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10370 p hg
    simpa only [d101945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d101945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d101945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10372 (p : Pattern) (guard : d9988 p = 1) : d47681 p ≤ (1 : Int) + d47681 p := by
  omega
theorem compare10373 (p : Pattern) (guard : d9989 p = 1) : d48273 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d9988 p = 1 := by simpa only [d9989, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10372 p hg
    simpa only [d9989, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9989, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10094 p hg
    simpa only [d9989, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10374 (p : Pattern) (guard : d9990 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9990, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10092 p hg
    simpa only [d9990, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9989 p = 1 := by simpa only [d9990, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10373 p hg
    simpa only [d9990, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10375 (p : Pattern) (guard : d9991 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d9990 p = 1 := by simpa only [d9991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10374 p hg
    simpa only [d9991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d9991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10376 (p : Pattern) (guard : d9992 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d9854 p = 1 := by simpa only [d9992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10344 p hg
    simpa only [d9992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9991 p = 1 := by simpa only [d9992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10375 p hg
    simpa only [d9992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10377 (p : Pattern) (guard : d9993 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d9993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9992 p = 1 := by simpa only [d9993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10376 p hg
    simpa only [d9993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10378 (p : Pattern) (guard : d9994 p = 1) : d48276 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d9993 p = 1 := by simpa only [d9994, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10377 p hg
    simpa only [d9994, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9994, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10100 p hg
    simpa only [d9994, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10379 (p : Pattern) (guard : d9995 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9995, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10090 p hg
    simpa only [d9995, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9994 p = 1 := by simpa only [d9995, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10378 p hg
    simpa only [d9995, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10380 (p : Pattern) (guard : d9996 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d9995 p = 1 := by simpa only [d9996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10379 p hg
    simpa only [d9996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10381 (p : Pattern) (guard : d9997 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d9996 p = 1 := by simpa only [d9997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10380 p hg
    simpa only [d9997, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9997, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10382 (p : Pattern) (guard : d9998 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d9997 p = 1 := by simpa only [d9998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10381 p hg
    simpa only [d9998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10383 (p : Pattern) (guard : d9999 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d9998 p = 1 := by simpa only [d9999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10382 p hg
    simpa only [d9999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10384 (p : Pattern) (guard : d10000 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d9999 p = 1 := by simpa only [d10000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10383 p hg
    simpa only [d10000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10385 (p : Pattern) (guard : d10001 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d10000 p = 1 := by simpa only [d10001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10384 p hg
    simpa only [d10001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10386 (p : Pattern) (guard : d101946 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d101945 p = 1 := by simpa only [d101946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10371 p hg
    simpa only [d101946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10001 p = 1 := by simpa only [d101946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10385 p hg
    simpa only [d101946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10387 (p : Pattern) (guard : d101947 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d101947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101946 p = 1 := by simpa only [d101947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10386 p hg
    simpa only [d101947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10388 (p : Pattern) (guard : d101948 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d101948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101947 p = 1 := by simpa only [d101948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10387 p hg
    simpa only [d101948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10389 (p : Pattern) (guard : d101949 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101949, d48278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10088 p hg
    simpa only [d101949, d48278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101948 p = 1 := by simpa only [d101949, d48278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10388 p hg
    simpa only [d101949, d48278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10390 (p : Pattern) (guard : d101950 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10087 p hg
    simpa only [d101950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101949 p = 1 := by simpa only [d101950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10389 p hg
    simpa only [d101950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10391 (p : Pattern) (guard : d10007 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d9877 p = 1 := by simpa only [d10007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10365 p hg
    simpa only [d10007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10392 (p : Pattern) (guard : d10008 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d10007 p = 1 := by simpa only [d10008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10391 p hg
    simpa only [d10008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10393 (p : Pattern) (guard : d10009 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d10008 p = 1 := by simpa only [d10009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10392 p hg
    simpa only [d10009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10394 (p : Pattern) (guard : d10010 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d10009 p = 1 := by simpa only [d10010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10393 p hg
    simpa only [d10010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10395 (p : Pattern) (guard : d10011 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d10010 p = 1 := by simpa only [d10011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10394 p hg
    simpa only [d10011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10396 (p : Pattern) (guard : d10012 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10011 p = 1 := by simpa only [d10012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10395 p hg
    simpa only [d10012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10397 (p : Pattern) (guard : d10013 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d10012 p = 1 := by simpa only [d10013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10396 p hg
    simpa only [d10013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10398 (p : Pattern) (guard : d10014 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10013 p = 1 := by simpa only [d10014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10397 p hg
    simpa only [d10014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10399 (p : Pattern) (guard : d10015 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10014 p = 1 := by simpa only [d10015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10398 p hg
    simpa only [d10015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10400 (p : Pattern) (guard : d10016 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10016, d48278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10088 p hg
    simpa only [d10016, d48278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10015 p = 1 := by simpa only [d10016, d48278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10399 p hg
    simpa only [d10016, d48278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10401 (p : Pattern) (guard : d10017 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10087 p hg
    simpa only [d10017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10016 p = 1 := by simpa only [d10017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10400 p hg
    simpa only [d10017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10402 (p : Pattern) (guard : d101951 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d101950 p = 1 := by simpa only [d101951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10390 p hg
    simpa only [d101951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10017 p = 1 := by simpa only [d101951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10401 p hg
    simpa only [d101951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10403 (p : Pattern) (guard : d101952 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d101951 p = 1 := by simpa only [d101952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10402 p hg
    simpa only [d101952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d101952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10087 p hg
    simpa only [d101952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10404 (p : Pattern) (guard : d101953 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d101952 p = 1 := by simpa only [d101953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10403 p hg
    simpa only [d101953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d101953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10087 p hg
    simpa only [d101953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10405 (p : Pattern) (guard : d101954 p = 1) : d48307 p ≤ (1 : Int) + d47910 p := by
  cases selected : p 49 with
  | false =>
    have hg : d101953 p = 1 := by simpa only [d101954, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10404 p hg
    simpa only [d101954, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d101954, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10117 p hg
    simpa only [d101954, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10406 (p : Pattern) (guard : d101955 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101955, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10086 p hg
    simpa only [d101955, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101954 p = 1 := by simpa only [d101955, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10405 p hg
    simpa only [d101955, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10407 (p : Pattern) (guard : d101956 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d101956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101955 p = 1 := by simpa only [d101956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10406 p hg
    simpa only [d101956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10408 (p : Pattern) (guard : d101957 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d101957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101956 p = 1 := by simpa only [d101957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10407 p hg
    simpa only [d101957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10409 (p : Pattern) (guard : d101958 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d101958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101957 p = 1 := by simpa only [d101958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10408 p hg
    simpa only [d101958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10410 (p : Pattern) (guard : d101959 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d101959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101958 p = 1 := by simpa only [d101959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10409 p hg
    simpa only [d101959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10411 (p : Pattern) (guard : d101960 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d101960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101959 p = 1 := by simpa only [d101960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10410 p hg
    simpa only [d101960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10412 (p : Pattern) (guard : d101961 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d101961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101960 p = 1 := by simpa only [d101961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10411 p hg
    simpa only [d101961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10413 (p : Pattern) (guard : d101962 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d101962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101961 p = 1 := by simpa only [d101962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10412 p hg
    simpa only [d101962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10414 (p : Pattern) (guard : d101963 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d101963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101962 p = 1 := by simpa only [d101963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10413 p hg
    simpa only [d101963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10415 (p : Pattern) (guard : d101964 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d101944 p = 1 := by simpa only [d101964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10330 p hg
    simpa only [d101964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101963 p = 1 := by simpa only [d101964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10414 p hg
    simpa only [d101964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10416 (p : Pattern) (guard : d10092 p = 1) : d47681 p ≤ (1 : Int) + d47681 p := by
  omega
theorem compare10417 (p : Pattern) (guard : d10093 p = 1) : d48273 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d10092 p = 1 := by simpa only [d10093, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10416 p hg
    simpa only [d10093, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10093, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10094 p hg
    simpa only [d10093, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10418 (p : Pattern) (guard : d10094 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10094, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10092 p hg
    simpa only [d10094, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10093 p = 1 := by simpa only [d10094, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10417 p hg
    simpa only [d10094, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10419 (p : Pattern) (guard : d10107 p = 1) : d47681 p ≤ (1 : Int) + d47681 p := by
  omega
theorem compare10420 (p : Pattern) (guard : d10108 p = 1) : d48273 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d10107 p = 1 := by simpa only [d10108, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10419 p hg
    simpa only [d10108, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10108, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10094 p hg
    simpa only [d10108, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10421 (p : Pattern) (guard : d10109 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10109, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10092 p hg
    simpa only [d10109, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10108 p = 1 := by simpa only [d10109, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10420 p hg
    simpa only [d10109, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10422 (p : Pattern) (guard : d10110 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d10094 p = 1 := by simpa only [d10110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10418 p hg
    simpa only [d10110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10109 p = 1 := by simpa only [d10110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10421 p hg
    simpa only [d10110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10423 (p : Pattern) (guard : d10122 p = 1) : d47681 p ≤ (1 : Int) + d47681 p := by
  omega
theorem compare10424 (p : Pattern) (guard : d10123 p = 1) : d48273 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d10122 p = 1 := by simpa only [d10123, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10423 p hg
    simpa only [d10123, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10123, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10094 p hg
    simpa only [d10123, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10425 (p : Pattern) (guard : d10124 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10124, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10092 p hg
    simpa only [d10124, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10123 p = 1 := by simpa only [d10124, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10424 p hg
    simpa only [d10124, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10426 (p : Pattern) (guard : d10142 p = 1) : d47681 p ≤ (1 : Int) + d47681 p := by
  omega
theorem compare10427 (p : Pattern) (guard : d10143 p = 1) : d48273 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d10142 p = 1 := by simpa only [d10143, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10426 p hg
    simpa only [d10143, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10143, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10094 p hg
    simpa only [d10143, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10428 (p : Pattern) (guard : d10144 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10144, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10092 p hg
    simpa only [d10144, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10143 p = 1 := by simpa only [d10144, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10427 p hg
    simpa only [d10144, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10429 (p : Pattern) (guard : d10145 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d10124 p = 1 := by simpa only [d10145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10425 p hg
    simpa only [d10145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10144 p = 1 := by simpa only [d10145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10428 p hg
    simpa only [d10145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10430 (p : Pattern) (guard : d10146 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d10110 p = 1 := by simpa only [d10146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10422 p hg
    simpa only [d10146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10145 p = 1 := by simpa only [d10146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10429 p hg
    simpa only [d10146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10431 (p : Pattern) (guard : d10147 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d10147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10146 p = 1 := by simpa only [d10147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10430 p hg
    simpa only [d10147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10432 (p : Pattern) (guard : d10148 p = 1) : d48276 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d10147 p = 1 := by simpa only [d10148, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10431 p hg
    simpa only [d10148, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10148, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10100 p hg
    simpa only [d10148, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10433 (p : Pattern) (guard : d10149 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10149, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10090 p hg
    simpa only [d10149, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10148 p = 1 := by simpa only [d10149, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10432 p hg
    simpa only [d10149, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10434 (p : Pattern) (guard : d10150 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d10144 p = 1 := by simpa only [d10150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10428 p hg
    simpa only [d10150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d10150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10435 (p : Pattern) (guard : d10151 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d10145 p = 1 := by simpa only [d10151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10429 p hg
    simpa only [d10151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10150 p = 1 := by simpa only [d10151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10434 p hg
    simpa only [d10151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10436 (p : Pattern) (guard : d10152 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d10152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10151 p = 1 := by simpa only [d10152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10435 p hg
    simpa only [d10152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10437 (p : Pattern) (guard : d10153 p = 1) : d48276 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d10152 p = 1 := by simpa only [d10153, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10436 p hg
    simpa only [d10153, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10153, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10100 p hg
    simpa only [d10153, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10438 (p : Pattern) (guard : d10154 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10154, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10090 p hg
    simpa only [d10154, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10153 p = 1 := by simpa only [d10154, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10437 p hg
    simpa only [d10154, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10439 (p : Pattern) (guard : d10155 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d10149 p = 1 := by simpa only [d10155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10433 p hg
    simpa only [d10155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10154 p = 1 := by simpa only [d10155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10438 p hg
    simpa only [d10155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10440 (p : Pattern) (guard : d10156 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d10155 p = 1 := by simpa only [d10156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10439 p hg
    simpa only [d10156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10441 (p : Pattern) (guard : d10157 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d10156 p = 1 := by simpa only [d10157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10440 p hg
    simpa only [d10157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10442 (p : Pattern) (guard : d10158 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d10157 p = 1 := by simpa only [d10158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10441 p hg
    simpa only [d10158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10443 (p : Pattern) (guard : d10164 p = 1) : d47681 p ≤ (1 : Int) + d47681 p := by
  omega
theorem compare10444 (p : Pattern) (guard : d10165 p = 1) : d48273 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d10164 p = 1 := by simpa only [d10165, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10443 p hg
    simpa only [d10165, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10165, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10094 p hg
    simpa only [d10165, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10445 (p : Pattern) (guard : d10166 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10166, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10092 p hg
    simpa only [d10166, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10165 p = 1 := by simpa only [d10166, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10444 p hg
    simpa only [d10166, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10446 (p : Pattern) (guard : d10167 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d10166 p = 1 := by simpa only [d10167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10445 p hg
    simpa only [d10167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d10167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10447 (p : Pattern) (guard : d10168 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d10167 p = 1 := by simpa only [d10168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10446 p hg
    simpa only [d10168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d10168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10448 (p : Pattern) (guard : d10169 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d10169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10168 p = 1 := by simpa only [d10169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10447 p hg
    simpa only [d10169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10449 (p : Pattern) (guard : d10170 p = 1) : d48276 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d10169 p = 1 := by simpa only [d10170, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10448 p hg
    simpa only [d10170, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10170, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10100 p hg
    simpa only [d10170, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10450 (p : Pattern) (guard : d10171 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10171, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10090 p hg
    simpa only [d10171, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10170 p = 1 := by simpa only [d10171, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10449 p hg
    simpa only [d10171, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10451 (p : Pattern) (guard : d10172 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d10154 p = 1 := by simpa only [d10172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10438 p hg
    simpa only [d10172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10171 p = 1 := by simpa only [d10172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10450 p hg
    simpa only [d10172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10452 (p : Pattern) (guard : d10173 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d10172 p = 1 := by simpa only [d10173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10451 p hg
    simpa only [d10173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10453 (p : Pattern) (guard : d10174 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d10173 p = 1 := by simpa only [d10174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10452 p hg
    simpa only [d10174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10454 (p : Pattern) (guard : d10175 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d10174 p = 1 := by simpa only [d10175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10453 p hg
    simpa only [d10175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10455 (p : Pattern) (guard : d10176 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d10158 p = 1 := by simpa only [d10176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10442 p hg
    simpa only [d10176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10175 p = 1 := by simpa only [d10176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10454 p hg
    simpa only [d10176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10456 (p : Pattern) (guard : d101965 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d10176 p = 1 := by simpa only [d101965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10455 p hg
    simpa only [d101965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d101965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d101965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10457 (p : Pattern) (guard : d10294 p = 1) : d47681 p ≤ (1 : Int) + d47681 p := by
  omega
theorem compare10458 (p : Pattern) (guard : d10295 p = 1) : d48273 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d10294 p = 1 := by simpa only [d10295, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10457 p hg
    simpa only [d10295, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10295, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10094 p hg
    simpa only [d10295, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10459 (p : Pattern) (guard : d10296 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10296, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10092 p hg
    simpa only [d10296, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10295 p = 1 := by simpa only [d10296, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10458 p hg
    simpa only [d10296, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10460 (p : Pattern) (guard : d10297 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d10296 p = 1 := by simpa only [d10297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10459 p hg
    simpa only [d10297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d10297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10461 (p : Pattern) (guard : d10298 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d10145 p = 1 := by simpa only [d10298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10429 p hg
    simpa only [d10298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10297 p = 1 := by simpa only [d10298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10460 p hg
    simpa only [d10298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10462 (p : Pattern) (guard : d10299 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d10299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10298 p = 1 := by simpa only [d10299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10461 p hg
    simpa only [d10299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10463 (p : Pattern) (guard : d10300 p = 1) : d48276 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d10299 p = 1 := by simpa only [d10300, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10462 p hg
    simpa only [d10300, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10300, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10100 p hg
    simpa only [d10300, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10464 (p : Pattern) (guard : d10301 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10301, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10090 p hg
    simpa only [d10301, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10300 p = 1 := by simpa only [d10301, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10463 p hg
    simpa only [d10301, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10465 (p : Pattern) (guard : d10302 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d10301 p = 1 := by simpa only [d10302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10464 p hg
    simpa only [d10302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10466 (p : Pattern) (guard : d10303 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d10302 p = 1 := by simpa only [d10303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10465 p hg
    simpa only [d10303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10467 (p : Pattern) (guard : d10304 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d10303 p = 1 := by simpa only [d10304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10466 p hg
    simpa only [d10304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10468 (p : Pattern) (guard : d10305 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d10304 p = 1 := by simpa only [d10305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10467 p hg
    simpa only [d10305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10469 (p : Pattern) (guard : d10306 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d10305 p = 1 := by simpa only [d10306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10468 p hg
    simpa only [d10306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10470 (p : Pattern) (guard : d10307 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d10306 p = 1 := by simpa only [d10307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10469 p hg
    simpa only [d10307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10471 (p : Pattern) (guard : d101966 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d101965 p = 1 := by simpa only [d101966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10456 p hg
    simpa only [d101966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10307 p = 1 := by simpa only [d101966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10470 p hg
    simpa only [d101966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10472 (p : Pattern) (guard : d101967 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d101967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101966 p = 1 := by simpa only [d101967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10471 p hg
    simpa only [d101967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10473 (p : Pattern) (guard : d101968 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d101968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101967 p = 1 := by simpa only [d101968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10472 p hg
    simpa only [d101968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10474 (p : Pattern) (guard : d101969 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101969, d48278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10088 p hg
    simpa only [d101969, d48278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101968 p = 1 := by simpa only [d101969, d48278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10473 p hg
    simpa only [d101969, d48278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10475 (p : Pattern) (guard : d101970 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10087 p hg
    simpa only [d101970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101969 p = 1 := by simpa only [d101970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10474 p hg
    simpa only [d101970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10476 (p : Pattern) (guard : d10313 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d10171 p = 1 := by simpa only [d10313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10450 p hg
    simpa only [d10313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10477 (p : Pattern) (guard : d10314 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d10313 p = 1 := by simpa only [d10314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10476 p hg
    simpa only [d10314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10478 (p : Pattern) (guard : d10315 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d10314 p = 1 := by simpa only [d10315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10477 p hg
    simpa only [d10315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10479 (p : Pattern) (guard : d10316 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d10315 p = 1 := by simpa only [d10316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10478 p hg
    simpa only [d10316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10480 (p : Pattern) (guard : d10317 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d10316 p = 1 := by simpa only [d10317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10479 p hg
    simpa only [d10317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10481 (p : Pattern) (guard : d10318 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10317 p = 1 := by simpa only [d10318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10480 p hg
    simpa only [d10318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10482 (p : Pattern) (guard : d10319 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d10318 p = 1 := by simpa only [d10319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10481 p hg
    simpa only [d10319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10483 (p : Pattern) (guard : d10320 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10319 p = 1 := by simpa only [d10320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10482 p hg
    simpa only [d10320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10484 (p : Pattern) (guard : d10321 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10320 p = 1 := by simpa only [d10321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10483 p hg
    simpa only [d10321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10485 (p : Pattern) (guard : d10322 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10322, d48278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10088 p hg
    simpa only [d10322, d48278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10321 p = 1 := by simpa only [d10322, d48278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10484 p hg
    simpa only [d10322, d48278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10486 (p : Pattern) (guard : d10323 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10087 p hg
    simpa only [d10323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10322 p = 1 := by simpa only [d10323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10485 p hg
    simpa only [d10323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10487 (p : Pattern) (guard : d101971 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d101970 p = 1 := by simpa only [d101971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10475 p hg
    simpa only [d101971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10323 p = 1 := by simpa only [d101971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10486 p hg
    simpa only [d101971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10488 (p : Pattern) (guard : d101972 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d101971 p = 1 := by simpa only [d101972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10487 p hg
    simpa only [d101972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d101972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10087 p hg
    simpa only [d101972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10489 (p : Pattern) (guard : d101973 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d101972 p = 1 := by simpa only [d101973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10488 p hg
    simpa only [d101973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d101973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10087 p hg
    simpa only [d101973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10490 (p : Pattern) (guard : d101974 p = 1) : d48307 p ≤ (1 : Int) + d47910 p := by
  cases selected : p 49 with
  | false =>
    have hg : d101973 p = 1 := by simpa only [d101974, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10489 p hg
    simpa only [d101974, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d101974, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10117 p hg
    simpa only [d101974, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10491 (p : Pattern) (guard : d101975 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101975, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10086 p hg
    simpa only [d101975, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101974 p = 1 := by simpa only [d101975, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10490 p hg
    simpa only [d101975, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10492 (p : Pattern) (guard : d101976 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d101976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101975 p = 1 := by simpa only [d101976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10491 p hg
    simpa only [d101976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10493 (p : Pattern) (guard : d101977 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d101977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101976 p = 1 := by simpa only [d101977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10492 p hg
    simpa only [d101977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10494 (p : Pattern) (guard : d101978 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d101978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101977 p = 1 := by simpa only [d101978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10493 p hg
    simpa only [d101978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10495 (p : Pattern) (guard : d101979 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d101979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101978 p = 1 := by simpa only [d101979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10494 p hg
    simpa only [d101979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10496 (p : Pattern) (guard : d101980 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d101980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101979 p = 1 := by simpa only [d101980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10495 p hg
    simpa only [d101980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10497 (p : Pattern) (guard : d101981 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d101981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101980 p = 1 := by simpa only [d101981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10496 p hg
    simpa only [d101981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10498 (p : Pattern) (guard : d101982 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d101982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101981 p = 1 := by simpa only [d101982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10497 p hg
    simpa only [d101982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10499 (p : Pattern) (guard : d101983 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d101983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101982 p = 1 := by simpa only [d101983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10498 p hg
    simpa only [d101983, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
