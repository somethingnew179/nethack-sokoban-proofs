/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons266
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare37380 (p : Pattern) (guard : d8100 p = 1) : d3820 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3820, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37203 p hg
    simpa only [d8100, d3820, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3820, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37344 p hg
    simpa only [d8100, d3820, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37381 (p : Pattern) (guard : d8106 p = 1) : d3822 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3822, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37380 p hg
    simpa only [d8106, d3822, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3822, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37346 p hg
    simpa only [d8106, d3822, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37382 (p : Pattern) (guard : d8112 p = 1) : d3828 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3828, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37381 p hg
    simpa only [d8112, d3828, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3828, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37369 p hg
    simpa only [d8112, d3828, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37383 (p : Pattern) (guard : d8118 p = 1) : d3834 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3834, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37382 p hg
    simpa only [d8118, d3834, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3834, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37354 p hg
    simpa only [d8118, d3834, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37384 (p : Pattern) (guard : d8124 p = 1) : d3836 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3836, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37383 p hg
    simpa only [d8124, d3836, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3836, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37357 p hg
    simpa only [d8124, d3836, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37385 (p : Pattern) (guard : d8130 p = 1) : d3843 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3843, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37384 p hg
    simpa only [d8130, d3843, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3843, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37363 p hg
    simpa only [d8130, d3843, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37386 (p : Pattern) (guard : d5843 p = 1) : d102 p ≤ (0 : Int) + d57 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d102, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1583 p hg
    simpa only [d5843, d102, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d102, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5843, d102, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37387 (p : Pattern) (guard : d5847 p = 1) : d102 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37386 p hg
    simpa only [d5847, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17788 p hg
    simpa only [d5847, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37388 (p : Pattern) (guard : d5854 p = 1) : d102 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37387 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17788 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37389 (p : Pattern) (guard : d8099 p = 1) : d102 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37388 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17788 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37390 (p : Pattern) (guard : d8105 p = 1) : d3766 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3766, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37389 p hg
    simpa only [d8105, d3766, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3766, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37299 p hg
    simpa only [d8105, d3766, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37391 (p : Pattern) (guard : d8111 p = 1) : d3827 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3827, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37390 p hg
    simpa only [d8111, d3827, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3827, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37348 p hg
    simpa only [d8111, d3827, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37392 (p : Pattern) (guard : d8117 p = 1) : d3844 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3844, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37391 p hg
    simpa only [d8117, d3844, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3844, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37370 p hg
    simpa only [d8117, d3844, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37393 (p : Pattern) (guard : d8123 p = 1) : d3846 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3846, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37392 p hg
    simpa only [d8123, d3846, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3846, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37372 p hg
    simpa only [d8123, d3846, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37394 (p : Pattern) (guard : d8129 p = 1) : d3849 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3849, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37393 p hg
    simpa only [d8129, d3849, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3849, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37374 p hg
    simpa only [d8129, d3849, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37395 (p : Pattern) (guard : d8135 p = 1) : d3853 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d3853, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37394 p hg
    simpa only [d8135, d3853, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d3853, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37376 p hg
    simpa only [d8135, d3853, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37396 (p : Pattern) (guard : d8136 p = 1) : d3854 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d3854, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37385 p hg
    simpa only [d8136, d3854, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d3854, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37395 p hg
    simpa only [d8136, d3854, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37397 (p : Pattern) (guard : d8141 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare37398 (p : Pattern) (guard : d8142 p = 1) : d3867 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d3867, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37396 p hg
    simpa only [d8142, d3867, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d3867, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d3867, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37399 (p : Pattern) (guard : d8143 p = 1) : d3868 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d3868, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37379 p hg
    simpa only [d8143, d3868, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d3868, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37398 p hg
    simpa only [d8143, d3868, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37400 (p : Pattern) (guard : d8144 p = 1) : d3869 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d3869, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37273 p hg
    simpa only [d8144, d3869, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d3869, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37399 p hg
    simpa only [d8144, d3869, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37401 (p : Pattern) (guard : d8145 p = 1) : d3870 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8139 p = 1 := by simpa only [d8145, d3870, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36976 p hg
    simpa only [d8145, d3870, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8144 p = 1 := by simpa only [d8145, d3870, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37400 p hg
    simpa only [d8145, d3870, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37402 (p : Pattern) (guard : d8146 p = 1) : d3871 p ≤ (0 : Int) + d447 p := by
  cases selected : p 49 with
  | false =>
    have hg : d8140 p = 1 := by simpa only [d8146, d3871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36813 p hg
    simpa only [d8146, d3871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8145 p = 1 := by simpa only [d8146, d3871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37401 p hg
    simpa only [d8146, d3871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37403 (p : Pattern) (guard : d8086 p = 1) : d3721 p ≤ (0 : Int) + d431 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d3721, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36505 p hg
    simpa only [d8086, d3721, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d3721, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36592 p hg
    simpa only [d8086, d3721, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37404 (p : Pattern) (guard : d8085 p = 1) : d3544 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d3544, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35987 p hg
    simpa only [d8085, d3544, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d3544, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35890 p hg
    simpa only [d8085, d3544, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37405 (p : Pattern) (guard : d8090 p = 1) : d3545 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d3545, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37404 p hg
    simpa only [d8090, d3545, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d3545, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36305 p hg
    simpa only [d8090, d3545, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37406 (p : Pattern) (guard : d8091 p = 1) : d3722 p ≤ (0 : Int) + d432 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3722, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37403 p hg
    simpa only [d8091, d3722, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3722, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37405 p hg
    simpa only [d8091, d3722, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37407 (p : Pattern) (guard : d8085 p = 1) : d3548 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d3548, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35869 p hg
    simpa only [d8085, d3548, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d3548, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35895 p hg
    simpa only [d8085, d3548, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37408 (p : Pattern) (guard : d8090 p = 1) : d3549 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d3549, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37407 p hg
    simpa only [d8090, d3549, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d3549, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36310 p hg
    simpa only [d8090, d3549, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37409 (p : Pattern) (guard : d8095 p = 1) : d3550 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3550, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37408 p hg
    simpa only [d8095, d3550, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3550, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d3550, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37410 (p : Pattern) (guard : d8096 p = 1) : d3723 p ≤ (0 : Int) + d433 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3723, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37406 p hg
    simpa only [d8096, d3723, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3723, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37409 p hg
    simpa only [d8096, d3723, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37411 (p : Pattern) (guard : d8085 p = 1) : d13 p ≤ (0 : Int) + d340 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35901 p hg
    simpa only [d8085, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35989 p hg
    simpa only [d8085, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37412 (p : Pattern) (guard : d8090 p = 1) : d13 p ≤ (0 : Int) + d341 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37411 p hg
    simpa only [d8090, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36772 p hg
    simpa only [d8090, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37413 (p : Pattern) (guard : d8095 p = 1) : d3552 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3552, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37412 p hg
    simpa only [d8095, d3552, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3552, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36654 p hg
    simpa only [d8095, d3552, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37414 (p : Pattern) (guard : d8089 p = 1) : d3548 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d3548, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36771 p hg
    simpa only [d8089, d3548, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d3548, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36309 p hg
    simpa only [d8089, d3548, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37415 (p : Pattern) (guard : d8094 p = 1) : d3549 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d3549, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37414 p hg
    simpa only [d8094, d3549, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d3549, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36657 p hg
    simpa only [d8094, d3549, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37416 (p : Pattern) (guard : d8100 p = 1) : d3550 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3550, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37415 p hg
    simpa only [d8100, d3550, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3550, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d3550, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37417 (p : Pattern) (guard : d8101 p = 1) : d3553 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3553, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37413 p hg
    simpa only [d8101, d3553, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3553, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37416 p hg
    simpa only [d8101, d3553, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37418 (p : Pattern) (guard : d8102 p = 1) : d3724 p ≤ (0 : Int) + d434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3724, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37410 p hg
    simpa only [d8102, d3724, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3724, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37417 p hg
    simpa only [d8102, d3724, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37419 (p : Pattern) (guard : d8084 p = 1) : d17 p ≤ (0 : Int) + d315 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35941 p hg
    simpa only [d8084, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34358 p hg
    simpa only [d8084, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37420 (p : Pattern) (guard : d8089 p = 1) : d17 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37419 p hg
    simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36016 p hg
    simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37421 (p : Pattern) (guard : d8094 p = 1) : d17 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37420 p hg
    simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36349 p hg
    simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37422 (p : Pattern) (guard : d8100 p = 1) : d3558 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3558, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37421 p hg
    simpa only [d8100, d3558, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3558, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36665 p hg
    simpa only [d8100, d3558, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37423 (p : Pattern) (guard : d8106 p = 1) : d3563 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3563, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37422 p hg
    simpa only [d8106, d3563, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3563, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36669 p hg
    simpa only [d8106, d3563, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37424 (p : Pattern) (guard : d8107 p = 1) : d3564 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3564, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36932 p hg
    simpa only [d8107, d3564, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3564, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37423 p hg
    simpa only [d8107, d3564, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37425 (p : Pattern) (guard : d8108 p = 1) : d3725 p ≤ (0 : Int) + d435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3725, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37418 p hg
    simpa only [d8108, d3725, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3725, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37424 p hg
    simpa only [d8108, d3725, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37426 (p : Pattern) (guard : d8107 p = 1) : d3564 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3564, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36705 p hg
    simpa only [d8107, d3564, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3564, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36943 p hg
    simpa only [d8107, d3564, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37427 (p : Pattern) (guard : d8112 p = 1) : d3574 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3574, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36566 p hg
    simpa only [d8112, d3574, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3574, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d3574, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37428 (p : Pattern) (guard : d8113 p = 1) : d3575 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3575, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37426 p hg
    simpa only [d8113, d3575, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3575, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37427 p hg
    simpa only [d8113, d3575, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37429 (p : Pattern) (guard : d8114 p = 1) : d3726 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d3726, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37425 p hg
    simpa only [d8114, d3726, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d3726, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37428 p hg
    simpa only [d8114, d3726, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37430 (p : Pattern) (guard : d8101 p = 1) : d3589 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3589, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36622 p hg
    simpa only [d8101, d3589, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3589, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36224 p hg
    simpa only [d8101, d3589, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37431 (p : Pattern) (guard : d8106 p = 1) : d3595 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3595, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36802 p hg
    simpa only [d8106, d3595, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3595, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36451 p hg
    simpa only [d8106, d3595, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37432 (p : Pattern) (guard : d8107 p = 1) : d3596 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3596, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37430 p hg
    simpa only [d8107, d3596, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3596, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37431 p hg
    simpa only [d8107, d3596, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37433 (p : Pattern) (guard : d8106 p = 1) : d3600 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3600, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36774 p hg
    simpa only [d8106, d3600, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3600, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36239 p hg
    simpa only [d8106, d3600, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37434 (p : Pattern) (guard : d8112 p = 1) : d3607 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3607, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37433 p hg
    simpa only [d8112, d3607, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3607, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36693 p hg
    simpa only [d8112, d3607, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37435 (p : Pattern) (guard : d8113 p = 1) : d3608 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3608, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37432 p hg
    simpa only [d8113, d3608, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3608, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37434 p hg
    simpa only [d8113, d3608, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37436 (p : Pattern) (guard : d8119 p = 1) : d3614 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3614, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37435 p hg
    simpa only [d8119, d3614, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3614, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36699 p hg
    simpa only [d8119, d3614, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37437 (p : Pattern) (guard : d8120 p = 1) : d3727 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d3727, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37429 p hg
    simpa only [d8120, d3727, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d3727, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37436 p hg
    simpa only [d8120, d3727, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37438 (p : Pattern) (guard : d8085 p = 1) : d13 p ≤ (0 : Int) + d328 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35883 p hg
    simpa only [d8085, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36771 p hg
    simpa only [d8085, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37439 (p : Pattern) (guard : d8090 p = 1) : d13 p ≤ (0 : Int) + d331 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37438 p hg
    simpa only [d8090, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36800 p hg
    simpa only [d8090, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37440 (p : Pattern) (guard : d8089 p = 1) : d3544 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d3544, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36771 p hg
    simpa only [d8089, d3544, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d3544, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36304 p hg
    simpa only [d8089, d3544, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37441 (p : Pattern) (guard : d8094 p = 1) : d3545 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d3545, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37440 p hg
    simpa only [d8094, d3545, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d3545, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36653 p hg
    simpa only [d8094, d3545, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37442 (p : Pattern) (guard : d8095 p = 1) : d3552 p ≤ (0 : Int) + d334 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3552, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37439 p hg
    simpa only [d8095, d3552, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3552, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37441 p hg
    simpa only [d8095, d3552, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37443 (p : Pattern) (guard : d8089 p = 1) : d3548 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d3548, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36799 p hg
    simpa only [d8089, d3548, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d3548, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36309 p hg
    simpa only [d8089, d3548, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37444 (p : Pattern) (guard : d8094 p = 1) : d3549 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d3549, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37443 p hg
    simpa only [d8094, d3549, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d3549, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36657 p hg
    simpa only [d8094, d3549, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37445 (p : Pattern) (guard : d8100 p = 1) : d3550 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3550, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37444 p hg
    simpa only [d8100, d3550, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3550, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d3550, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37446 (p : Pattern) (guard : d8101 p = 1) : d3553 p ≤ (0 : Int) + d337 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3553, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37442 p hg
    simpa only [d8101, d3553, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3553, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37445 p hg
    simpa only [d8101, d3553, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37447 (p : Pattern) (guard : d8084 p = 1) : d30 p ≤ (0 : Int) + d364 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1209 p hg
    simpa only [d8084, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34407 p hg
    simpa only [d8084, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37448 (p : Pattern) (guard : d8089 p = 1) : d30 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37447 p hg
    simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36125 p hg
    simpa only [d8089, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37449 (p : Pattern) (guard : d8094 p = 1) : d30 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37448 p hg
    simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36397 p hg
    simpa only [d8094, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37450 (p : Pattern) (guard : d8100 p = 1) : d3623 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3623, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37449 p hg
    simpa only [d8100, d3623, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3623, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36710 p hg
    simpa only [d8100, d3623, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37451 (p : Pattern) (guard : d8106 p = 1) : d3628 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3628, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37450 p hg
    simpa only [d8106, d3628, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3628, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36714 p hg
    simpa only [d8106, d3628, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37452 (p : Pattern) (guard : d8107 p = 1) : d3710 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3710, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37446 p hg
    simpa only [d8107, d3710, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3710, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37451 p hg
    simpa only [d8107, d3710, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37453 (p : Pattern) (guard : d8084 p = 1) : d17 p ≤ (0 : Int) + d317 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare921 p hg
    simpa only [d8084, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34358 p hg
    simpa only [d8084, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37454 (p : Pattern) (guard : d8089 p = 1) : d17 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37453 p hg
    simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36016 p hg
    simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37455 (p : Pattern) (guard : d8094 p = 1) : d17 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37454 p hg
    simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36349 p hg
    simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37456 (p : Pattern) (guard : d8100 p = 1) : d3558 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3558, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37455 p hg
    simpa only [d8100, d3558, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3558, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36665 p hg
    simpa only [d8100, d3558, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37457 (p : Pattern) (guard : d8106 p = 1) : d3563 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3563, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37456 p hg
    simpa only [d8106, d3563, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3563, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36669 p hg
    simpa only [d8106, d3563, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37458 (p : Pattern) (guard : d5843 p = 1) : d23 p ≤ (0 : Int) + d57 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d23, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare690 p hg
    simpa only [d5843, d23, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d23, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5843, d23, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37459 (p : Pattern) (guard : d5847 p = 1) : d23 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37458 p hg
    simpa only [d5847, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17666 p hg
    simpa only [d5847, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37460 (p : Pattern) (guard : d5854 p = 1) : d23 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37459 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17666 p hg
    simpa only [d5854, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37461 (p : Pattern) (guard : d8099 p = 1) : d23 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37460 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17666 p hg
    simpa only [d8099, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37462 (p : Pattern) (guard : d8105 p = 1) : d3568 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3568, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37461 p hg
    simpa only [d8105, d3568, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3568, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36405 p hg
    simpa only [d8105, d3568, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37463 (p : Pattern) (guard : d8111 p = 1) : d3573 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3573, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37462 p hg
    simpa only [d8111, d3573, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3573, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36722 p hg
    simpa only [d8111, d3573, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37464 (p : Pattern) (guard : d8112 p = 1) : d3630 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3630, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37457 p hg
    simpa only [d8112, d3630, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3630, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37463 p hg
    simpa only [d8112, d3630, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37465 (p : Pattern) (guard : d8113 p = 1) : d3711 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3711, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37452 p hg
    simpa only [d8113, d3711, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3711, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37464 p hg
    simpa only [d8113, d3711, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37466 (p : Pattern) (guard : d5843 p = 1) : d57 p ≤ (0 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d57, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare728 p hg
    simpa only [d5843, d57, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d57, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5843, d57, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37467 (p : Pattern) (guard : d5847 p = 1) : d57 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37466 p hg
    simpa only [d5847, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17706 p hg
    simpa only [d5847, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37468 (p : Pattern) (guard : d5854 p = 1) : d57 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37467 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17706 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37469 (p : Pattern) (guard : d8099 p = 1) : d57 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37468 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17706 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37470 (p : Pattern) (guard : d8105 p = 1) : d3634 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3634, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37469 p hg
    simpa only [d8105, d3634, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3634, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36411 p hg
    simpa only [d8105, d3634, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37471 (p : Pattern) (guard : d8111 p = 1) : d3636 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3636, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37470 p hg
    simpa only [d8111, d3636, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3636, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36468 p hg
    simpa only [d8111, d3636, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37472 (p : Pattern) (guard : d8112 p = 1) : d3637 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3637, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37423 p hg
    simpa only [d8112, d3637, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3637, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37471 p hg
    simpa only [d8112, d3637, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37473 (p : Pattern) (guard : d8118 p = 1) : d3641 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3641, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37472 p hg
    simpa only [d8118, d3641, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3641, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36473 p hg
    simpa only [d8118, d3641, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37474 (p : Pattern) (guard : d8119 p = 1) : d3712 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3712, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37465 p hg
    simpa only [d8119, d3712, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3712, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37473 p hg
    simpa only [d8119, d3712, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37475 (p : Pattern) (guard : d8106 p = 1) : d3595 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3595, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36967 p hg
    simpa only [d8106, d3595, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3595, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36451 p hg
    simpa only [d8106, d3595, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37476 (p : Pattern) (guard : d8112 p = 1) : d3645 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3645, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37475 p hg
    simpa only [d8112, d3645, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3645, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36732 p hg
    simpa only [d8112, d3645, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37477 (p : Pattern) (guard : d8118 p = 1) : d3647 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3647, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37476 p hg
    simpa only [d8118, d3647, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3647, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36735 p hg
    simpa only [d8118, d3647, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37478 (p : Pattern) (guard : d8124 p = 1) : d3653 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3653, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37477 p hg
    simpa only [d8124, d3653, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3653, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36740 p hg
    simpa only [d8124, d3653, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37479 (p : Pattern) (guard : d8125 p = 1) : d3713 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3713, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37474 p hg
    simpa only [d8125, d3713, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3713, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37478 p hg
    simpa only [d8125, d3713, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37480 (p : Pattern) (guard : d8126 p = 1) : d3728 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d3728, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37437 p hg
    simpa only [d8126, d3728, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d3728, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37479 p hg
    simpa only [d8126, d3728, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37481 (p : Pattern) (guard : d8095 p = 1) : d3658 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3658, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36703 p hg
    simpa only [d8095, d3658, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3658, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36745 p hg
    simpa only [d8095, d3658, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37482 (p : Pattern) (guard : d8101 p = 1) : d3660 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3660, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37481 p hg
    simpa only [d8101, d3660, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3660, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36747 p hg
    simpa only [d8101, d3660, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37483 (p : Pattern) (guard : d8107 p = 1) : d3666 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3666, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37482 p hg
    simpa only [d8107, d3666, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3666, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36968 p hg
    simpa only [d8107, d3666, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37484 (p : Pattern) (guard : d8106 p = 1) : d3668 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3668, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36802 p hg
    simpa only [d8106, d3668, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3668, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36753 p hg
    simpa only [d8106, d3668, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37485 (p : Pattern) (guard : d8112 p = 1) : d3671 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3671, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37484 p hg
    simpa only [d8112, d3671, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3671, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36756 p hg
    simpa only [d8112, d3671, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37486 (p : Pattern) (guard : d8113 p = 1) : d3672 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3672, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37483 p hg
    simpa only [d8113, d3672, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3672, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37485 p hg
    simpa only [d8113, d3672, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37487 (p : Pattern) (guard : d8118 p = 1) : d3676 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3676, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36960 p hg
    simpa only [d8118, d3676, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3676, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36759 p hg
    simpa only [d8118, d3676, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37488 (p : Pattern) (guard : d8119 p = 1) : d3677 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3677, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37486 p hg
    simpa only [d8119, d3677, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3677, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37487 p hg
    simpa only [d8119, d3677, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37489 (p : Pattern) (guard : d8125 p = 1) : d3684 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3684, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37488 p hg
    simpa only [d8125, d3684, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3684, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36769 p hg
    simpa only [d8125, d3684, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37490 (p : Pattern) (guard : d8084 p = 1) : d13 p ≤ (0 : Int) + d315 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4500 p hg
    simpa only [d8084, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34338 p hg
    simpa only [d8084, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37491 (p : Pattern) (guard : d8089 p = 1) : d13 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37490 p hg
    simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36338 p hg
    simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37492 (p : Pattern) (guard : d8094 p = 1) : d13 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37491 p hg
    simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36682 p hg
    simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37493 (p : Pattern) (guard : d8100 p = 1) : d3582 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3582, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37492 p hg
    simpa only [d8100, d3582, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3582, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36685 p hg
    simpa only [d8100, d3582, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37494 (p : Pattern) (guard : d8106 p = 1) : d3665 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3665, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37493 p hg
    simpa only [d8106, d3665, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3665, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36750 p hg
    simpa only [d8106, d3665, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37495 (p : Pattern) (guard : d5843 p = 1) : d30 p ≤ (0 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d30, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1532 p hg
    simpa only [d5843, d30, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d30, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5843, d30, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37496 (p : Pattern) (guard : d5847 p = 1) : d30 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37495 p hg
    simpa only [d5847, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17673 p hg
    simpa only [d5847, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37497 (p : Pattern) (guard : d5854 p = 1) : d30 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37496 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17673 p hg
    simpa only [d5854, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37498 (p : Pattern) (guard : d8099 p = 1) : d30 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37497 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17673 p hg
    simpa only [d8099, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37499 (p : Pattern) (guard : d8105 p = 1) : d3643 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3643, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37498 p hg
    simpa only [d8105, d3643, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3643, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36730 p hg
    simpa only [d8105, d3643, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37500 (p : Pattern) (guard : d8111 p = 1) : d3678 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3678, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37499 p hg
    simpa only [d8111, d3678, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3678, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36776 p hg
    simpa only [d8111, d3678, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37501 (p : Pattern) (guard : d8112 p = 1) : d3685 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3685, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37494 p hg
    simpa only [d8112, d3685, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3685, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37500 p hg
    simpa only [d8112, d3685, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37502 (p : Pattern) (guard : d8118 p = 1) : d3687 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3687, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37501 p hg
    simpa only [d8118, d3687, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3687, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36780 p hg
    simpa only [d8118, d3687, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37503 (p : Pattern) (guard : d8124 p = 1) : d3690 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3690, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37502 p hg
    simpa only [d8124, d3690, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3690, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36785 p hg
    simpa only [d8124, d3690, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37504 (p : Pattern) (guard : d8130 p = 1) : d3694 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3694, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37503 p hg
    simpa only [d8130, d3694, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3694, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36789 p hg
    simpa only [d8130, d3694, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37505 (p : Pattern) (guard : d8131 p = 1) : d3695 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d3695, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37489 p hg
    simpa only [d8131, d3695, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d3695, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37504 p hg
    simpa only [d8131, d3695, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37506 (p : Pattern) (guard : d8132 p = 1) : d3729 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d3729, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37480 p hg
    simpa only [d8132, d3729, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d3729, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37505 p hg
    simpa only [d8132, d3729, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37507 (p : Pattern) (guard : d8095 p = 1) : d3658 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3658, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36930 p hg
    simpa only [d8095, d3658, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3658, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36745 p hg
    simpa only [d8095, d3658, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37508 (p : Pattern) (guard : d8101 p = 1) : d3660 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3660, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37507 p hg
    simpa only [d8101, d3660, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3660, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36747 p hg
    simpa only [d8101, d3660, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37509 (p : Pattern) (guard : d8107 p = 1) : d3666 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3666, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37508 p hg
    simpa only [d8107, d3666, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3666, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37494 p hg
    simpa only [d8107, d3666, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37510 (p : Pattern) (guard : d8106 p = 1) : d3668 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3668, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36967 p hg
    simpa only [d8106, d3668, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3668, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36753 p hg
    simpa only [d8106, d3668, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37511 (p : Pattern) (guard : d8112 p = 1) : d3671 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3671, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37510 p hg
    simpa only [d8112, d3671, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3671, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36756 p hg
    simpa only [d8112, d3671, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37512 (p : Pattern) (guard : d8113 p = 1) : d3672 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3672, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37509 p hg
    simpa only [d8113, d3672, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3672, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37511 p hg
    simpa only [d8113, d3672, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37513 (p : Pattern) (guard : d8118 p = 1) : d3676 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3676, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37485 p hg
    simpa only [d8118, d3676, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3676, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36759 p hg
    simpa only [d8118, d3676, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37514 (p : Pattern) (guard : d8119 p = 1) : d3677 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3677, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37512 p hg
    simpa only [d8119, d3677, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3677, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37513 p hg
    simpa only [d8119, d3677, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37515 (p : Pattern) (guard : d8112 p = 1) : d3681 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3681, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36600 p hg
    simpa only [d8112, d3681, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3681, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36766 p hg
    simpa only [d8112, d3681, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37516 (p : Pattern) (guard : d8118 p = 1) : d3682 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3682, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37515 p hg
    simpa only [d8118, d3682, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3682, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36473 p hg
    simpa only [d8118, d3682, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37517 (p : Pattern) (guard : d8124 p = 1) : d3683 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3683, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37516 p hg
    simpa only [d8124, d3683, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3683, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d3683, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37518 (p : Pattern) (guard : d8125 p = 1) : d3684 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3684, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37514 p hg
    simpa only [d8125, d3684, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3684, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37517 p hg
    simpa only [d8125, d3684, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare37519 (p : Pattern) (guard : d8084 p = 1) : d13 p ≤ (0 : Int) + d317 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare906 p hg
    simpa only [d8084, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34338 p hg
    simpa only [d8084, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
