/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons104
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare14700 (p : Pattern) (guard : d5269 p = 1) : d141 p ≤ (0 : Int) + d5376 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d141, d5376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14684 p hg
    simpa only [d141, d5376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d141, d5376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14613 p hg
    simpa only [d141, d5376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14701 (p : Pattern) (guard : d5269 p = 1) : d142 p ≤ (0 : Int) + d5377 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d142, d5377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14699 p hg
    simpa only [d142, d5377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d142, d5377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14700 p hg
    simpa only [d142, d5377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14702 (p : Pattern) (guard : d5269 p = 1) : d143 p ≤ (0 : Int) + d5378 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d143, d5378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14684 p hg
    simpa only [d143, d5378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d143, d5378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14615 p hg
    simpa only [d143, d5378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14703 (p : Pattern) (guard : d5269 p = 1) : d144 p ≤ (0 : Int) + d5379 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d144, d5379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14702 p hg
    simpa only [d144, d5379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d144, d5379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d144, d5379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14704 (p : Pattern) (guard : d5269 p = 1) : d145 p ≤ (0 : Int) + d5380 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d145, d5380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14701 p hg
    simpa only [d145, d5380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d145, d5380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14703 p hg
    simpa only [d145, d5380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14705 (p : Pattern) (guard : d5269 p = 1) : d146 p ≤ (0 : Int) + d5381 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d146, d5381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14697 p hg
    simpa only [d146, d5381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d146, d5381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14704 p hg
    simpa only [d146, d5381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14706 (p : Pattern) (guard : d5269 p = 1) : d147 p ≤ (0 : Int) + d5382 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d147, d5382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14690 p hg
    simpa only [d147, d5382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d147, d5382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14705 p hg
    simpa only [d147, d5382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14707 (p : Pattern) (guard : d5269 p = 1) : d148 p ≤ (0 : Int) + d5383 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d148, d5383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14679 p hg
    simpa only [d148, d5383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d148, d5383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14680 p hg
    simpa only [d148, d5383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14708 (p : Pattern) (guard : d5269 p = 1) : d149 p ≤ (0 : Int) + d5384 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d149, d5384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14691 p hg
    simpa only [d149, d5384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d149, d5384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14707 p hg
    simpa only [d149, d5384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14709 (p : Pattern) (guard : d5269 p = 1) : d150 p ≤ (0 : Int) + d5385 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d150, d5385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14708 p hg
    simpa only [d150, d5385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d150, d5385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d150, d5385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14710 (p : Pattern) (guard : d5269 p = 1) : d151 p ≤ (0 : Int) + d5386 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d151, d5386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14709 p hg
    simpa only [d151, d5386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d151, d5386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d151, d5386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14711 (p : Pattern) (guard : d5269 p = 1) : d152 p ≤ (0 : Int) + d5387 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d152, d5387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14665 p hg
    simpa only [d152, d5387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d152, d5387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14710 p hg
    simpa only [d152, d5387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14712 (p : Pattern) (guard : d5269 p = 1) : d153 p ≤ (0 : Int) + d5388 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d153, d5388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14707 p hg
    simpa only [d153, d5388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d153, d5388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d153, d5388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14713 (p : Pattern) (guard : d5269 p = 1) : d154 p ≤ (0 : Int) + d5389 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d154, d5389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14712 p hg
    simpa only [d154, d5389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d154, d5389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d154, d5389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14714 (p : Pattern) (guard : d5269 p = 1) : d155 p ≤ (0 : Int) + d5390 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d155, d5390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14713 p hg
    simpa only [d155, d5390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d155, d5390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d155, d5390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14715 (p : Pattern) (guard : d5269 p = 1) : d156 p ≤ (0 : Int) + d5391 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d156, d5391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14697 p hg
    simpa only [d156, d5391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d156, d5391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14714 p hg
    simpa only [d156, d5391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14716 (p : Pattern) (guard : d5269 p = 1) : d157 p ≤ (0 : Int) + d5392 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d157, d5392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14711 p hg
    simpa only [d157, d5392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d157, d5392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14715 p hg
    simpa only [d157, d5392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14717 (p : Pattern) (guard : d5269 p = 1) : d158 p ≤ (0 : Int) + d5393 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d158, d5393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14706 p hg
    simpa only [d158, d5393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d158, d5393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14716 p hg
    simpa only [d158, d5393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14718 (p : Pattern) (guard : d5269 p = 1) : d159 p ≤ (0 : Int) + d5394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d159, d5394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14663 p hg
    simpa only [d159, d5394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d159, d5394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d159, d5394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14719 (p : Pattern) (guard : d5269 p = 1) : d160 p ≤ (0 : Int) + d5395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d160, d5395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14718 p hg
    simpa only [d160, d5395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d160, d5395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d160, d5395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14720 (p : Pattern) (guard : d5269 p = 1) : d161 p ≤ (0 : Int) + d5396 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d161, d5396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14719 p hg
    simpa only [d161, d5396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d161, d5396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d161, d5396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14721 (p : Pattern) (guard : d5269 p = 1) : d162 p ≤ (0 : Int) + d5397 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d162, d5397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14720 p hg
    simpa only [d162, d5397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d162, d5397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d162, d5397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14722 (p : Pattern) (guard : d5269 p = 1) : d163 p ≤ (0 : Int) + d5398 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d163, d5398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14716 p hg
    simpa only [d163, d5398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d163, d5398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14721 p hg
    simpa only [d163, d5398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14723 (p : Pattern) (guard : d5269 p = 1) : d164 p ≤ (0 : Int) + d5399 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d164, d5399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14717 p hg
    simpa only [d164, d5399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d164, d5399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14722 p hg
    simpa only [d164, d5399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14724 (p : Pattern) (guard : d5269 p = 1) : d165 p ≤ (0 : Int) + d5400 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d165, d5400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14716 p hg
    simpa only [d165, d5400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d165, d5400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d165, d5400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14725 (p : Pattern) (guard : d5269 p = 1) : d166 p ≤ (0 : Int) + d5401 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d166, d5401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14717 p hg
    simpa only [d166, d5401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d166, d5401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14724 p hg
    simpa only [d166, d5401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14726 (p : Pattern) (guard : d5269 p = 1) : d167 p ≤ (0 : Int) + d5402 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d167, d5402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14723 p hg
    simpa only [d167, d5402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d167, d5402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14725 p hg
    simpa only [d167, d5402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14727 (p : Pattern) (guard : d5269 p = 1) : d168 p ≤ (0 : Int) + d5403 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d168, d5403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14644 p hg
    simpa only [d168, d5403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d168, d5403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14726 p hg
    simpa only [d168, d5403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14728 (p : Pattern) (guard : d5269 p = 1) : d169 p ≤ (0 : Int) + d5404 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d169, d5404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14644 p hg
    simpa only [d169, d5404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d169, d5404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14727 p hg
    simpa only [d169, d5404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14729 (p : Pattern) (guard : d5269 p = 1) : d170 p ≤ (0 : Int) + d5405 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d170, d5405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14562 p hg
    simpa only [d170, d5405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d170, d5405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14571 p hg
    simpa only [d170, d5405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14730 (p : Pattern) (guard : d5269 p = 1) : d171 p ≤ (0 : Int) + d5406 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d171, d5406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14592 p hg
    simpa only [d171, d5406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d171, d5406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14729 p hg
    simpa only [d171, d5406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14731 (p : Pattern) (guard : d5269 p = 1) : d172 p ≤ (0 : Int) + d5407 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d172, d5407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14562 p hg
    simpa only [d172, d5407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d172, d5407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14580 p hg
    simpa only [d172, d5407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14732 (p : Pattern) (guard : d5269 p = 1) : d173 p ≤ (0 : Int) + d5408 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d173, d5408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14570 p hg
    simpa only [d173, d5408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d173, d5408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d173, d5408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14733 (p : Pattern) (guard : d5269 p = 1) : d174 p ≤ (0 : Int) + d5409 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d174, d5409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14731 p hg
    simpa only [d174, d5409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d174, d5409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14732 p hg
    simpa only [d174, d5409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14734 (p : Pattern) (guard : d5269 p = 1) : d175 p ≤ (0 : Int) + d5410 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d175, d5410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14730 p hg
    simpa only [d175, d5410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d175, d5410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14733 p hg
    simpa only [d175, d5410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14735 (p : Pattern) (guard : d5269 p = 1) : d176 p ≤ (0 : Int) + d5411 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d176, d5411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14609 p hg
    simpa only [d176, d5411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d176, d5411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14732 p hg
    simpa only [d176, d5411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14736 (p : Pattern) (guard : d5269 p = 1) : d177 p ≤ (0 : Int) + d5412 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d177, d5412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14735 p hg
    simpa only [d177, d5412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d177, d5412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14616 p hg
    simpa only [d177, d5412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14737 (p : Pattern) (guard : d5269 p = 1) : d178 p ≤ (0 : Int) + d5413 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d178, d5413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14734 p hg
    simpa only [d178, d5413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d178, d5413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14736 p hg
    simpa only [d178, d5413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14738 (p : Pattern) (guard : d5269 p = 1) : d179 p ≤ (0 : Int) + d5414 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d179, d5414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14556 p hg
    simpa only [d179, d5414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d179, d5414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14737 p hg
    simpa only [d179, d5414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14739 (p : Pattern) (guard : d5269 p = 1) : d180 p ≤ (0 : Int) + d5415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d180, d5415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14729 p hg
    simpa only [d180, d5415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d180, d5415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14582 p hg
    simpa only [d180, d5415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14740 (p : Pattern) (guard : d5269 p = 1) : d181 p ≤ (0 : Int) + d5416 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d181, d5416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14732 p hg
    simpa only [d181, d5416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d181, d5416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14615 p hg
    simpa only [d181, d5416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14741 (p : Pattern) (guard : d5269 p = 1) : d182 p ≤ (0 : Int) + d5417 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d182, d5417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14739 p hg
    simpa only [d182, d5417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d182, d5417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14740 p hg
    simpa only [d182, d5417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14742 (p : Pattern) (guard : d5269 p = 1) : d183 p ≤ (0 : Int) + d5418 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d183, d5418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14732 p hg
    simpa only [d183, d5418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d183, d5418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d183, d5418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14743 (p : Pattern) (guard : d5269 p = 1) : d184 p ≤ (0 : Int) + d5419 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d184, d5419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14742 p hg
    simpa only [d184, d5419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d184, d5419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d184, d5419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14744 (p : Pattern) (guard : d5269 p = 1) : d185 p ≤ (0 : Int) + d5420 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d185, d5420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14741 p hg
    simpa only [d185, d5420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d185, d5420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14743 p hg
    simpa only [d185, d5420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14745 (p : Pattern) (guard : d5269 p = 1) : d186 p ≤ (0 : Int) + d5421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d186, d5421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14608 p hg
    simpa only [d186, d5421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d186, d5421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14744 p hg
    simpa only [d186, d5421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14746 (p : Pattern) (guard : d5269 p = 1) : d187 p ≤ (0 : Int) + d5422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d187, d5422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14738 p hg
    simpa only [d187, d5422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d187, d5422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14745 p hg
    simpa only [d187, d5422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14747 (p : Pattern) (guard : d5269 p = 1) : d188 p ≤ (0 : Int) + d5423 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d188, d5423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14535 p hg
    simpa only [d188, d5423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d188, d5423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14622 p hg
    simpa only [d188, d5423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14748 (p : Pattern) (guard : d5269 p = 1) : d189 p ≤ (0 : Int) + d5424 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d189, d5424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14747 p hg
    simpa only [d189, d5424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d189, d5424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14623 p hg
    simpa only [d189, d5424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14749 (p : Pattern) (guard : d0 p = 1) : d191 p ≤ (0 : Int) + d190 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14750 (p : Pattern) (guard : d1 p = 1) : d8 p ≤ (0 : Int) + d8 p := by
  omega
theorem compare14751 (p : Pattern) (guard : d1 p = 1) : d8 p ≤ (0 : Int) + d190 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14750 p hg
    simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1638 p hg
    simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14752 (p : Pattern) (guard : d0 p = 1) : d190 p ≤ (0 : Int) + d190 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14753 (p : Pattern) (guard : d5268 p = 1) : d191 p ≤ (0 : Int) + d190 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5268, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14751 p hg
    simpa only [d5268, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5268, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14752 p hg
    simpa only [d5268, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14754 (p : Pattern) (guard : d5269 p = 1) : d191 p ≤ (0 : Int) + d190 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14749 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5268 p = 1 := by simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14753 p hg
    simpa only [d5269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14755 (p : Pattern) (guard : d5269 p = 1) : d192 p ≤ (0 : Int) + d5425 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d192, d5425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14754 p hg
    simpa only [d192, d5425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d192, d5425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d192, d5425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14756 (p : Pattern) (guard : d5269 p = 1) : d193 p ≤ (0 : Int) + d5426 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d193, d5426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14754 p hg
    simpa only [d193, d5426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d193, d5426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14755 p hg
    simpa only [d193, d5426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14757 (p : Pattern) (guard : d5269 p = 1) : d194 p ≤ (0 : Int) + d5427 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d194, d5427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14543 p hg
    simpa only [d194, d5427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d194, d5427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14756 p hg
    simpa only [d194, d5427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14758 (p : Pattern) (guard : d5269 p = 1) : d195 p ≤ (0 : Int) + d5428 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d195, d5428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14757 p hg
    simpa only [d195, d5428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d195, d5428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d195, d5428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14759 (p : Pattern) (guard : d5269 p = 1) : d196 p ≤ (0 : Int) + d5429 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d196, d5429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14758 p hg
    simpa only [d196, d5429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d196, d5429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d196, d5429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14760 (p : Pattern) (guard : d5269 p = 1) : d197 p ≤ (0 : Int) + d5430 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d197, d5430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14748 p hg
    simpa only [d197, d5430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d197, d5430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14759 p hg
    simpa only [d197, d5430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14761 (p : Pattern) (guard : d5269 p = 1) : d198 p ≤ (0 : Int) + d5431 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d198, d5431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14543 p hg
    simpa only [d198, d5431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d198, d5431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14605 p hg
    simpa only [d198, d5431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14762 (p : Pattern) (guard : d5269 p = 1) : d199 p ≤ (0 : Int) + d5432 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d199, d5432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14592 p hg
    simpa only [d199, d5432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d199, d5432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14761 p hg
    simpa only [d199, d5432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14763 (p : Pattern) (guard : d5269 p = 1) : d200 p ≤ (0 : Int) + d5433 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d200, d5433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14762 p hg
    simpa only [d200, d5433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d200, d5433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14627 p hg
    simpa only [d200, d5433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14764 (p : Pattern) (guard : d5269 p = 1) : d201 p ≤ (0 : Int) + d5434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d201, d5434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14756 p hg
    simpa only [d201, d5434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d201, d5434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d201, d5434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14765 (p : Pattern) (guard : d5269 p = 1) : d202 p ≤ (0 : Int) + d5435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d202, d5435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14764 p hg
    simpa only [d202, d5435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d202, d5435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d202, d5435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14766 (p : Pattern) (guard : d5269 p = 1) : d203 p ≤ (0 : Int) + d5436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d203, d5436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14765 p hg
    simpa only [d203, d5436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d203, d5436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d203, d5436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14767 (p : Pattern) (guard : d5269 p = 1) : d204 p ≤ (0 : Int) + d5437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d204, d5437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14763 p hg
    simpa only [d204, d5437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d204, d5437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14766 p hg
    simpa only [d204, d5437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14768 (p : Pattern) (guard : d5269 p = 1) : d205 p ≤ (0 : Int) + d5438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d205, d5438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14760 p hg
    simpa only [d205, d5438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d205, d5438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14767 p hg
    simpa only [d205, d5438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14769 (p : Pattern) (guard : d5269 p = 1) : d206 p ≤ (0 : Int) + d5439 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d206, d5439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14746 p hg
    simpa only [d206, d5439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d206, d5439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14768 p hg
    simpa only [d206, d5439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14770 (p : Pattern) (guard : d5269 p = 1) : d207 p ≤ (0 : Int) + d5440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d207, d5440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14768 p hg
    simpa only [d207, d5440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d207, d5440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d207, d5440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14771 (p : Pattern) (guard : d5269 p = 1) : d208 p ≤ (0 : Int) + d5441 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d208, d5441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14769 p hg
    simpa only [d208, d5441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d208, d5441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14770 p hg
    simpa only [d208, d5441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14772 (p : Pattern) (guard : d5269 p = 1) : d209 p ≤ (0 : Int) + d5442 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d209, d5442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14641 p hg
    simpa only [d209, d5442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d209, d5442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14771 p hg
    simpa only [d209, d5442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14773 (p : Pattern) (guard : d5269 p = 1) : d210 p ≤ (0 : Int) + d5443 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d210, d5443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14644 p hg
    simpa only [d210, d5443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d210, d5443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14772 p hg
    simpa only [d210, d5443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14774 (p : Pattern) (guard : d5269 p = 1) : d211 p ≤ (0 : Int) + d5444 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d211, d5444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14660 p hg
    simpa only [d211, d5444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d211, d5444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d211, d5444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14775 (p : Pattern) (guard : d5269 p = 1) : d212 p ≤ (0 : Int) + d5445 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d212, d5445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14692 p hg
    simpa only [d212, d5445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d212, d5445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14774 p hg
    simpa only [d212, d5445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14776 (p : Pattern) (guard : d5269 p = 1) : d213 p ≤ (0 : Int) + d5446 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d213, d5446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14774 p hg
    simpa only [d213, d5446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d213, d5446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d213, d5446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14777 (p : Pattern) (guard : d5269 p = 1) : d214 p ≤ (0 : Int) + d5447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d214, d5447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14775 p hg
    simpa only [d214, d5447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d214, d5447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14776 p hg
    simpa only [d214, d5447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14778 (p : Pattern) (guard : d5269 p = 1) : d215 p ≤ (0 : Int) + d5448 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d215, d5448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14684 p hg
    simpa only [d215, d5448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d215, d5448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d215, d5448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14779 (p : Pattern) (guard : d5269 p = 1) : d216 p ≤ (0 : Int) + d5449 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d216, d5449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14699 p hg
    simpa only [d216, d5449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d216, d5449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14778 p hg
    simpa only [d216, d5449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14780 (p : Pattern) (guard : d5269 p = 1) : d217 p ≤ (0 : Int) + d5450 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d217, d5450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14778 p hg
    simpa only [d217, d5450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d217, d5450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d217, d5450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14781 (p : Pattern) (guard : d5269 p = 1) : d218 p ≤ (0 : Int) + d5451 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d218, d5451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14779 p hg
    simpa only [d218, d5451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d218, d5451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14780 p hg
    simpa only [d218, d5451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14782 (p : Pattern) (guard : d5269 p = 1) : d219 p ≤ (0 : Int) + d5452 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d219, d5452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14777 p hg
    simpa only [d219, d5452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d219, d5452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14781 p hg
    simpa only [d219, d5452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14783 (p : Pattern) (guard : d5269 p = 1) : d220 p ≤ (0 : Int) + d5453 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d220, d5453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14690 p hg
    simpa only [d220, d5453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d220, d5453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14782 p hg
    simpa only [d220, d5453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14784 (p : Pattern) (guard : d5269 p = 1) : d221 p ≤ (0 : Int) + d5454 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d221, d5454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14777 p hg
    simpa only [d221, d5454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d221, d5454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14714 p hg
    simpa only [d221, d5454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14785 (p : Pattern) (guard : d5269 p = 1) : d222 p ≤ (0 : Int) + d5455 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d222, d5455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14711 p hg
    simpa only [d222, d5455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d222, d5455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14784 p hg
    simpa only [d222, d5455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14786 (p : Pattern) (guard : d5269 p = 1) : d223 p ≤ (0 : Int) + d5456 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d223, d5456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14783 p hg
    simpa only [d223, d5456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d223, d5456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14785 p hg
    simpa only [d223, d5456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14787 (p : Pattern) (guard : d5269 p = 1) : d224 p ≤ (0 : Int) + d5457 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d224, d5457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14785 p hg
    simpa only [d224, d5457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d224, d5457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14721 p hg
    simpa only [d224, d5457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14788 (p : Pattern) (guard : d5269 p = 1) : d225 p ≤ (0 : Int) + d5458 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d225, d5458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14786 p hg
    simpa only [d225, d5458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d225, d5458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14787 p hg
    simpa only [d225, d5458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14789 (p : Pattern) (guard : d5269 p = 1) : d226 p ≤ (0 : Int) + d5459 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d226, d5459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14671 p hg
    simpa only [d226, d5459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d226, d5459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14680 p hg
    simpa only [d226, d5459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14790 (p : Pattern) (guard : d5269 p = 1) : d227 p ≤ (0 : Int) + d5460 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d227, d5460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14691 p hg
    simpa only [d227, d5460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d227, d5460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14789 p hg
    simpa only [d227, d5460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14791 (p : Pattern) (guard : d5269 p = 1) : d228 p ≤ (0 : Int) + d5461 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d228, d5461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14790 p hg
    simpa only [d228, d5461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d228, d5461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14778 p hg
    simpa only [d228, d5461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14792 (p : Pattern) (guard : d5269 p = 1) : d229 p ≤ (0 : Int) + d5462 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d229, d5462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14679 p hg
    simpa only [d229, d5462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d229, d5462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d229, d5462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14793 (p : Pattern) (guard : d5269 p = 1) : d230 p ≤ (0 : Int) + d5463 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d230, d5463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14792 p hg
    simpa only [d230, d5463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d230, d5463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d230, d5463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14794 (p : Pattern) (guard : d5269 p = 1) : d231 p ≤ (0 : Int) + d5464 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d231, d5464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14793 p hg
    simpa only [d231, d5464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d231, d5464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d231, d5464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14795 (p : Pattern) (guard : d5269 p = 1) : d232 p ≤ (0 : Int) + d5465 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d232, d5465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14791 p hg
    simpa only [d232, d5465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d232, d5465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14794 p hg
    simpa only [d232, d5465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14796 (p : Pattern) (guard : d5269 p = 1) : d233 p ≤ (0 : Int) + d5466 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d233, d5466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14665 p hg
    simpa only [d233, d5466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d233, d5466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14795 p hg
    simpa only [d233, d5466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14797 (p : Pattern) (guard : d5269 p = 1) : d234 p ≤ (0 : Int) + d5467 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d234, d5467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14658 p hg
    simpa only [d234, d5467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d234, d5467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14680 p hg
    simpa only [d234, d5467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14798 (p : Pattern) (guard : d5269 p = 1) : d235 p ≤ (0 : Int) + d5468 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d235, d5468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14797 p hg
    simpa only [d235, d5468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d235, d5468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14684 p hg
    simpa only [d235, d5468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14799 (p : Pattern) (guard : d5269 p = 1) : d236 p ≤ (0 : Int) + d5469 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d236, d5469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14798 p hg
    simpa only [d236, d5469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d236, d5469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14793 p hg
    simpa only [d236, d5469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14800 (p : Pattern) (guard : d5269 p = 1) : d237 p ≤ (0 : Int) + d5470 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d237, d5470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14588 p hg
    simpa only [d237, d5470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d237, d5470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d237, d5470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14801 (p : Pattern) (guard : d5269 p = 1) : d238 p ≤ (0 : Int) + d5471 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d238, d5471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14799 p hg
    simpa only [d238, d5471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d238, d5471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14800 p hg
    simpa only [d238, d5471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14802 (p : Pattern) (guard : d5269 p = 1) : d239 p ≤ (0 : Int) + d5472 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d239, d5472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14777 p hg
    simpa only [d239, d5472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d239, d5472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14801 p hg
    simpa only [d239, d5472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14803 (p : Pattern) (guard : d5269 p = 1) : d240 p ≤ (0 : Int) + d5473 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d240, d5473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14796 p hg
    simpa only [d240, d5473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d240, d5473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14802 p hg
    simpa only [d240, d5473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14804 (p : Pattern) (guard : d5269 p = 1) : d241 p ≤ (0 : Int) + d5474 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d241, d5474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14691 p hg
    simpa only [d241, d5474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d241, d5474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14605 p hg
    simpa only [d241, d5474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14805 (p : Pattern) (guard : d5269 p = 1) : d242 p ≤ (0 : Int) + d5475 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d242, d5475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14652 p hg
    simpa only [d242, d5475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d242, d5475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14804 p hg
    simpa only [d242, d5475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14806 (p : Pattern) (guard : d5269 p = 1) : d243 p ≤ (0 : Int) + d5476 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d243, d5476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14805 p hg
    simpa only [d243, d5476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d243, d5476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14696 p hg
    simpa only [d243, d5476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14807 (p : Pattern) (guard : d5269 p = 1) : d244 p ≤ (0 : Int) + d5477 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d244, d5477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14806 p hg
    simpa only [d244, d5477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d244, d5477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14714 p hg
    simpa only [d244, d5477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14808 (p : Pattern) (guard : d5269 p = 1) : d245 p ≤ (0 : Int) + d5478 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d245, d5478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14691 p hg
    simpa only [d245, d5478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d245, d5478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14774 p hg
    simpa only [d245, d5478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14809 (p : Pattern) (guard : d5269 p = 1) : d246 p ≤ (0 : Int) + d5479 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d246, d5479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14808 p hg
    simpa only [d246, d5479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d246, d5479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14713 p hg
    simpa only [d246, d5479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14810 (p : Pattern) (guard : d5269 p = 1) : d247 p ≤ (0 : Int) + d5480 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d247, d5480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14554 p hg
    simpa only [d247, d5480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d247, d5480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d247, d5480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14811 (p : Pattern) (guard : d5269 p = 1) : d248 p ≤ (0 : Int) + d5481 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d248, d5481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14810 p hg
    simpa only [d248, d5481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d248, d5481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d248, d5481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14812 (p : Pattern) (guard : d5269 p = 1) : d249 p ≤ (0 : Int) + d5482 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d249, d5482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14809 p hg
    simpa only [d249, d5482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d249, d5482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14811 p hg
    simpa only [d249, d5482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14813 (p : Pattern) (guard : d5269 p = 1) : d250 p ≤ (0 : Int) + d5483 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d250, d5483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14807 p hg
    simpa only [d250, d5483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d250, d5483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14812 p hg
    simpa only [d250, d5483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14814 (p : Pattern) (guard : d5269 p = 1) : d251 p ≤ (0 : Int) + d5484 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d251, d5484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14803 p hg
    simpa only [d251, d5484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d251, d5484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14813 p hg
    simpa only [d251, d5484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14815 (p : Pattern) (guard : d5269 p = 1) : d252 p ≤ (0 : Int) + d5485 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d252, d5485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14691 p hg
    simpa only [d252, d5485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d252, d5485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14553 p hg
    simpa only [d252, d5485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14816 (p : Pattern) (guard : d5269 p = 1) : d253 p ≤ (0 : Int) + d5486 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d253, d5486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14652 p hg
    simpa only [d253, d5486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d253, d5486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14815 p hg
    simpa only [d253, d5486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14817 (p : Pattern) (guard : d5269 p = 1) : d254 p ≤ (0 : Int) + d5487 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d254, d5487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14660 p hg
    simpa only [d254, d5487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d254, d5487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14553 p hg
    simpa only [d254, d5487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14818 (p : Pattern) (guard : d5269 p = 1) : d255 p ≤ (0 : Int) + d5488 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d255, d5488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14817 p hg
    simpa only [d255, d5488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d255, d5488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d255, d5488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14819 (p : Pattern) (guard : d5269 p = 1) : d256 p ≤ (0 : Int) + d5489 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d256, d5489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14816 p hg
    simpa only [d256, d5489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d256, d5489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14818 p hg
    simpa only [d256, d5489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14820 (p : Pattern) (guard : d5269 p = 1) : d257 p ≤ (0 : Int) + d5490 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d257, d5490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14707 p hg
    simpa only [d257, d5490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d257, d5490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14605 p hg
    simpa only [d257, d5490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14821 (p : Pattern) (guard : d5269 p = 1) : d258 p ≤ (0 : Int) + d5491 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d258, d5491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14820 p hg
    simpa only [d258, d5491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d258, d5491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d258, d5491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14822 (p : Pattern) (guard : d5269 p = 1) : d259 p ≤ (0 : Int) + d5492 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d259, d5492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14821 p hg
    simpa only [d259, d5492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d259, d5492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d259, d5492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14823 (p : Pattern) (guard : d5269 p = 1) : d260 p ≤ (0 : Int) + d5493 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d260, d5493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14819 p hg
    simpa only [d260, d5493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d260, d5493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14822 p hg
    simpa only [d260, d5493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14824 (p : Pattern) (guard : d5269 p = 1) : d261 p ≤ (0 : Int) + d5494 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d261, d5494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14823 p hg
    simpa only [d261, d5494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d261, d5494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14812 p hg
    simpa only [d261, d5494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14825 (p : Pattern) (guard : d5269 p = 1) : d262 p ≤ (0 : Int) + d5495 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d262, d5495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14824 p hg
    simpa only [d262, d5495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d262, d5495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14533 p hg
    simpa only [d262, d5495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14826 (p : Pattern) (guard : d5269 p = 1) : d263 p ≤ (0 : Int) + d5496 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d263, d5496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14814 p hg
    simpa only [d263, d5496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d263, d5496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14825 p hg
    simpa only [d263, d5496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14827 (p : Pattern) (guard : d5269 p = 1) : d264 p ≤ (0 : Int) + d5497 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d264, d5497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14788 p hg
    simpa only [d264, d5497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d264, d5497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14826 p hg
    simpa only [d264, d5497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14828 (p : Pattern) (guard : d5269 p = 1) : d265 p ≤ (0 : Int) + d5498 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d265, d5498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14644 p hg
    simpa only [d265, d5498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d265, d5498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14827 p hg
    simpa only [d265, d5498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14829 (p : Pattern) (guard : d5269 p = 1) : d266 p ≤ (0 : Int) + d5499 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d266, d5499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14773 p hg
    simpa only [d266, d5499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d266, d5499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14828 p hg
    simpa only [d266, d5499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14830 (p : Pattern) (guard : d5269 p = 1) : d267 p ≤ (0 : Int) + d5500 p := by
  cases selected : p 48 with
  | false =>
    have hg : d5269 p = 1 := by simpa only [d267, d5500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14728 p hg
    simpa only [d267, d5500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5269 p = 1 := by simpa only [d267, d5500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14829 p hg
    simpa only [d267, d5500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14831 (p : Pattern) (guard : d0 p = 1) : d14 p ≤ (0 : Int) + d315 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14832 (p : Pattern) (guard : d5502 p = 1) : d14 p ≤ (0 : Int) + d2503 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d5502, d2503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14831 p hg
    simpa only [d5502, d2503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14833 (p : Pattern) (guard : d0 p = 1) : d14 p ≤ (0 : Int) + d2504 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14834 (p : Pattern) (guard : d5503 p = 1) : d14 p ≤ (0 : Int) + d2505 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14832 p hg
    simpa only [d5503, d2505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14833 p hg
    simpa only [d5503, d2505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14835 (p : Pattern) (guard : d5502 p = 1) : d14 p ≤ (0 : Int) + d2504 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d5502, d2504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11458 p hg
    simpa only [d5502, d2504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14836 (p : Pattern) (guard : d0 p = 1) : d14 p ≤ (0 : Int) + d2506 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare14837 (p : Pattern) (guard : d5503 p = 1) : d14 p ≤ (0 : Int) + d2507 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14835 p hg
    simpa only [d5503, d2507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14836 p hg
    simpa only [d5503, d2507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14838 (p : Pattern) (guard : d5503 p = 1) : d14 p ≤ (0 : Int) + d2508 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14834 p hg
    simpa only [d2508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14837 p hg
    simpa only [d2508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14839 (p : Pattern) (guard : d0 p = 1) : d14 p ≤ (0 : Int) + d2509 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban22Refined85
