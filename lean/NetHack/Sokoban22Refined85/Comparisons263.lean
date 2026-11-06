/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons262
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare36820 (p : Pattern) (guard : d8102 p = 1) : d3564 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3564, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36519 p hg
    simpa only [d8102, d3564, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3564, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36561 p hg
    simpa only [d8102, d3564, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36821 (p : Pattern) (guard : d8103 p = 1) : d3565 p ≤ (0 : Int) + d347 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d3565, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36819 p hg
    simpa only [d8103, d3565, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d3565, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36820 p hg
    simpa only [d8103, d3565, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36822 (p : Pattern) (guard : d8107 p = 1) : d3574 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3574, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36085 p hg
    simpa only [d8107, d3574, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3574, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d3574, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36823 (p : Pattern) (guard : d8108 p = 1) : d3575 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3575, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36525 p hg
    simpa only [d8108, d3575, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3575, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36822 p hg
    simpa only [d8108, d3575, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36824 (p : Pattern) (guard : d8109 p = 1) : d3576 p ≤ (0 : Int) + d363 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d3576, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36821 p hg
    simpa only [d8109, d3576, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d3576, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36823 p hg
    simpa only [d8109, d3576, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36825 (p : Pattern) (guard : d8096 p = 1) : d3589 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3589, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36268 p hg
    simpa only [d8096, d3589, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3589, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36193 p hg
    simpa only [d8096, d3589, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36826 (p : Pattern) (guard : d8102 p = 1) : d3596 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3596, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36825 p hg
    simpa only [d8102, d3596, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3596, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36577 p hg
    simpa only [d8102, d3596, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36827 (p : Pattern) (guard : d8101 p = 1) : d3600 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3600, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36459 p hg
    simpa only [d8101, d3600, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3600, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36114 p hg
    simpa only [d8101, d3600, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36828 (p : Pattern) (guard : d8107 p = 1) : d3607 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3607, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36827 p hg
    simpa only [d8107, d3607, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3607, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36354 p hg
    simpa only [d8107, d3607, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36829 (p : Pattern) (guard : d8108 p = 1) : d3608 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3608, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36826 p hg
    simpa only [d8108, d3608, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3608, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36828 p hg
    simpa only [d8108, d3608, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36830 (p : Pattern) (guard : d8101 p = 1) : d3609 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3609, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36395 p hg
    simpa only [d8101, d3609, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3609, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d3609, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36831 (p : Pattern) (guard : d8107 p = 1) : d3610 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3610, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36830 p hg
    simpa only [d8107, d3610, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3610, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36354 p hg
    simpa only [d8107, d3610, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36832 (p : Pattern) (guard : d8113 p = 1) : d3613 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3613, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36831 p hg
    simpa only [d8113, d3613, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3613, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36359 p hg
    simpa only [d8113, d3613, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36833 (p : Pattern) (guard : d8114 p = 1) : d3614 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d3614, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36829 p hg
    simpa only [d8114, d3614, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d3614, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36832 p hg
    simpa only [d8114, d3614, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36834 (p : Pattern) (guard : d8115 p = 1) : d3615 p ≤ (0 : Int) + d377 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d3615, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36824 p hg
    simpa only [d8115, d3615, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d3615, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36833 p hg
    simpa only [d8115, d3615, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36835 (p : Pattern) (guard : d8086 p = 1) : d3618 p ≤ (0 : Int) + d381 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d3618, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36045 p hg
    simpa only [d8086, d3618, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d3618, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36490 p hg
    simpa only [d8086, d3618, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36836 (p : Pattern) (guard : d8085 p = 1) : d3544 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d3544, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35886 p hg
    simpa only [d8085, d3544, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d3544, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35890 p hg
    simpa only [d8085, d3544, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36837 (p : Pattern) (guard : d8090 p = 1) : d3545 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d3545, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36836 p hg
    simpa only [d8090, d3545, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d3545, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36305 p hg
    simpa only [d8090, d3545, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36838 (p : Pattern) (guard : d8091 p = 1) : d3619 p ≤ (0 : Int) + d382 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3619, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36835 p hg
    simpa only [d8091, d3619, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3619, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36837 p hg
    simpa only [d8091, d3619, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36839 (p : Pattern) (guard : d8085 p = 1) : d3548 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d3548, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35987 p hg
    simpa only [d8085, d3548, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d3548, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35895 p hg
    simpa only [d8085, d3548, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36840 (p : Pattern) (guard : d8090 p = 1) : d3549 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d3549, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36839 p hg
    simpa only [d8090, d3549, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d3549, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36310 p hg
    simpa only [d8090, d3549, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36841 (p : Pattern) (guard : d8095 p = 1) : d3550 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3550, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36840 p hg
    simpa only [d8095, d3550, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3550, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d3550, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36842 (p : Pattern) (guard : d8096 p = 1) : d3620 p ≤ (0 : Int) + d383 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3620, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36838 p hg
    simpa only [d8096, d3620, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3620, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36841 p hg
    simpa only [d8096, d3620, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36843 (p : Pattern) (guard : d8085 p = 1) : d30 p ≤ (0 : Int) + d349 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36054 p hg
    simpa only [d8085, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36056 p hg
    simpa only [d8085, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36844 (p : Pattern) (guard : d8090 p = 1) : d30 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36843 p hg
    simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36126 p hg
    simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36845 (p : Pattern) (guard : d8095 p = 1) : d3623 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3623, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36844 p hg
    simpa only [d8095, d3623, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3623, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36371 p hg
    simpa only [d8095, d3623, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36846 (p : Pattern) (guard : d8101 p = 1) : d3628 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3628, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36845 p hg
    simpa only [d8101, d3628, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3628, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36376 p hg
    simpa only [d8101, d3628, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36847 (p : Pattern) (guard : d8102 p = 1) : d3629 p ≤ (0 : Int) + d384 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3629, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36842 p hg
    simpa only [d8102, d3629, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3629, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36846 p hg
    simpa only [d8102, d3629, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36848 (p : Pattern) (guard : d8085 p = 1) : d17 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36073 p hg
    simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35914 p hg
    simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36849 (p : Pattern) (guard : d8090 p = 1) : d17 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36848 p hg
    simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36017 p hg
    simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36850 (p : Pattern) (guard : d8095 p = 1) : d3558 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3558, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36849 p hg
    simpa only [d8095, d3558, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3558, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36319 p hg
    simpa only [d8095, d3558, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36851 (p : Pattern) (guard : d8101 p = 1) : d3563 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3563, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36850 p hg
    simpa only [d8101, d3563, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3563, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36324 p hg
    simpa only [d8101, d3563, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36852 (p : Pattern) (guard : d8084 p = 1) : d23 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35948 p hg
    simpa only [d8084, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34388 p hg
    simpa only [d8084, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36853 (p : Pattern) (guard : d8089 p = 1) : d23 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36852 p hg
    simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36031 p hg
    simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36854 (p : Pattern) (guard : d8094 p = 1) : d23 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36853 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36135 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36855 (p : Pattern) (guard : d8100 p = 1) : d3568 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3568, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36854 p hg
    simpa only [d8100, d3568, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3568, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36138 p hg
    simpa only [d8100, d3568, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36856 (p : Pattern) (guard : d8106 p = 1) : d3573 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3573, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36855 p hg
    simpa only [d8106, d3573, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3573, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36386 p hg
    simpa only [d8106, d3573, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36857 (p : Pattern) (guard : d8107 p = 1) : d3630 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3630, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36851 p hg
    simpa only [d8107, d3630, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3630, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36856 p hg
    simpa only [d8107, d3630, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36858 (p : Pattern) (guard : d8108 p = 1) : d3631 p ≤ (0 : Int) + d385 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3631, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36847 p hg
    simpa only [d8108, d3631, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3631, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36857 p hg
    simpa only [d8108, d3631, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36859 (p : Pattern) (guard : d8084 p = 1) : d57 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36088 p hg
    simpa only [d8084, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34494 p hg
    simpa only [d8084, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36860 (p : Pattern) (guard : d8089 p = 1) : d57 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36859 p hg
    simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36092 p hg
    simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36861 (p : Pattern) (guard : d8094 p = 1) : d57 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36860 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36143 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36862 (p : Pattern) (guard : d8100 p = 1) : d3634 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3634, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36861 p hg
    simpa only [d8100, d3634, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3634, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36146 p hg
    simpa only [d8100, d3634, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36863 (p : Pattern) (guard : d8106 p = 1) : d3636 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3636, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36862 p hg
    simpa only [d8106, d3636, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3636, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36236 p hg
    simpa only [d8106, d3636, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36864 (p : Pattern) (guard : d8107 p = 1) : d3637 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3637, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36561 p hg
    simpa only [d8107, d3637, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3637, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36863 p hg
    simpa only [d8107, d3637, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36865 (p : Pattern) (guard : d8084 p = 1) : d39 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36103 p hg
    simpa only [d8084, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34431 p hg
    simpa only [d8084, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36866 (p : Pattern) (guard : d8089 p = 1) : d39 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36865 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36107 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36867 (p : Pattern) (guard : d8094 p = 1) : d39 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36866 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36150 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36868 (p : Pattern) (guard : d8100 p = 1) : d3638 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3638, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36867 p hg
    simpa only [d8100, d3638, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3638, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36153 p hg
    simpa only [d8100, d3638, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36869 (p : Pattern) (guard : d8106 p = 1) : d3639 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3639, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36868 p hg
    simpa only [d8106, d3639, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3639, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36239 p hg
    simpa only [d8106, d3639, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36870 (p : Pattern) (guard : d8112 p = 1) : d3640 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3640, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36869 p hg
    simpa only [d8112, d3640, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3640, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d3640, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36871 (p : Pattern) (guard : d8113 p = 1) : d3641 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3641, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36864 p hg
    simpa only [d8113, d3641, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3641, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36870 p hg
    simpa only [d8113, d3641, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36872 (p : Pattern) (guard : d8114 p = 1) : d3642 p ≤ (0 : Int) + d388 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d3642, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36858 p hg
    simpa only [d8114, d3642, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d3642, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36871 p hg
    simpa only [d8114, d3642, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36873 (p : Pattern) (guard : d8101 p = 1) : d3595 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3595, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36594 p hg
    simpa only [d8101, d3595, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3595, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36205 p hg
    simpa only [d8101, d3595, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36874 (p : Pattern) (guard : d8106 p = 1) : d3644 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3644, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36599 p hg
    simpa only [d8106, d3644, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3644, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d3644, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36875 (p : Pattern) (guard : d8107 p = 1) : d3645 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3645, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36873 p hg
    simpa only [d8107, d3645, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3645, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36874 p hg
    simpa only [d8107, d3645, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36876 (p : Pattern) (guard : d8113 p = 1) : d3647 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3647, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36875 p hg
    simpa only [d8113, d3647, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3647, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36408 p hg
    simpa only [d8113, d3647, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36877 (p : Pattern) (guard : d8119 p = 1) : d3653 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3653, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36876 p hg
    simpa only [d8119, d3653, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3653, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36420 p hg
    simpa only [d8119, d3653, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36878 (p : Pattern) (guard : d8120 p = 1) : d3654 p ≤ (0 : Int) + d392 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d3654, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36872 p hg
    simpa only [d8120, d3654, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d3654, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36877 p hg
    simpa only [d8120, d3654, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36879 (p : Pattern) (guard : d8121 p = 1) : d3655 p ≤ (0 : Int) + d393 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d3655, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36834 p hg
    simpa only [d8121, d3655, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d3655, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36878 p hg
    simpa only [d8121, d3655, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36880 (p : Pattern) (guard : d8127 p = 1) : d3696 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d3696, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36879 p hg
    simpa only [d8127, d3696, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d3696, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36639 p hg
    simpa only [d8127, d3696, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36881 (p : Pattern) (guard : d8091 p = 1) : d3658 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3658, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36514 p hg
    simpa only [d8091, d3658, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3658, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36425 p hg
    simpa only [d8091, d3658, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36882 (p : Pattern) (guard : d8095 p = 1) : d3659 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3659, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36546 p hg
    simpa only [d8095, d3659, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3659, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d3659, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36883 (p : Pattern) (guard : d8096 p = 1) : d3660 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3660, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36881 p hg
    simpa only [d8096, d3660, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3660, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36882 p hg
    simpa only [d8096, d3660, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36884 (p : Pattern) (guard : d8102 p = 1) : d3666 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3666, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36883 p hg
    simpa only [d8102, d3666, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3666, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36623 p hg
    simpa only [d8102, d3666, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36885 (p : Pattern) (guard : d8101 p = 1) : d3668 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3668, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36594 p hg
    simpa only [d8101, d3668, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3668, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36434 p hg
    simpa only [d8101, d3668, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36886 (p : Pattern) (guard : d8107 p = 1) : d3671 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3671, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36885 p hg
    simpa only [d8107, d3671, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3671, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36634 p hg
    simpa only [d8107, d3671, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36887 (p : Pattern) (guard : d8108 p = 1) : d3672 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3672, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36884 p hg
    simpa only [d8108, d3672, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3672, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36886 p hg
    simpa only [d8108, d3672, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36888 (p : Pattern) (guard : d8113 p = 1) : d3676 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3676, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36611 p hg
    simpa only [d8113, d3676, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3676, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36440 p hg
    simpa only [d8113, d3676, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36889 (p : Pattern) (guard : d8114 p = 1) : d3677 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d3677, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36887 p hg
    simpa only [d8114, d3677, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d3677, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36888 p hg
    simpa only [d8114, d3677, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36890 (p : Pattern) (guard : d8107 p = 1) : d3681 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3681, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36225 p hg
    simpa only [d8107, d3681, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3681, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36452 p hg
    simpa only [d8107, d3681, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36891 (p : Pattern) (guard : d8113 p = 1) : d3682 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3682, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36890 p hg
    simpa only [d8113, d3682, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3682, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36241 p hg
    simpa only [d8113, d3682, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36892 (p : Pattern) (guard : d8119 p = 1) : d3683 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3683, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36891 p hg
    simpa only [d8119, d3683, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3683, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d3683, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36893 (p : Pattern) (guard : d8120 p = 1) : d3684 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d3684, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36889 p hg
    simpa only [d8120, d3684, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d3684, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36892 p hg
    simpa only [d8120, d3684, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36894 (p : Pattern) (guard : d8095 p = 1) : d3582 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3582, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36703 p hg
    simpa only [d8095, d3582, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3582, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36344 p hg
    simpa only [d8095, d3582, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36895 (p : Pattern) (guard : d8101 p = 1) : d3665 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3665, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36894 p hg
    simpa only [d8101, d3665, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3665, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36431 p hg
    simpa only [d8101, d3665, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36896 (p : Pattern) (guard : d8100 p = 1) : d3643 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3643, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36708 p hg
    simpa only [d8100, d3643, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3643, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36400 p hg
    simpa only [d8100, d3643, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36897 (p : Pattern) (guard : d8106 p = 1) : d3678 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3678, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36896 p hg
    simpa only [d8106, d3678, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3678, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36461 p hg
    simpa only [d8106, d3678, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36898 (p : Pattern) (guard : d8107 p = 1) : d3685 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3685, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36895 p hg
    simpa only [d8107, d3685, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3685, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36897 p hg
    simpa only [d8107, d3685, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36899 (p : Pattern) (guard : d8100 p = 1) : d3605 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3605, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36719 p hg
    simpa only [d8100, d3605, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3605, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36352 p hg
    simpa only [d8100, d3605, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36900 (p : Pattern) (guard : d8106 p = 1) : d3670 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3670, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36899 p hg
    simpa only [d8106, d3670, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3670, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36436 p hg
    simpa only [d8106, d3670, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36901 (p : Pattern) (guard : d8112 p = 1) : d3686 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3686, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36900 p hg
    simpa only [d8112, d3686, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3686, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36465 p hg
    simpa only [d8112, d3686, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36902 (p : Pattern) (guard : d8113 p = 1) : d3687 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3687, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36898 p hg
    simpa only [d8113, d3687, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3687, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36901 p hg
    simpa only [d8113, d3687, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36903 (p : Pattern) (guard : d8112 p = 1) : d3688 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3688, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36634 p hg
    simpa only [d8112, d3688, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3688, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36469 p hg
    simpa only [d8112, d3688, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36904 (p : Pattern) (guard : d8118 p = 1) : d3689 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3689, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36903 p hg
    simpa only [d8118, d3689, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3689, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36473 p hg
    simpa only [d8118, d3689, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36905 (p : Pattern) (guard : d8119 p = 1) : d3690 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3690, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36902 p hg
    simpa only [d8119, d3690, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3690, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36904 p hg
    simpa only [d8119, d3690, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36906 (p : Pattern) (guard : d8125 p = 1) : d3694 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3694, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36905 p hg
    simpa only [d8125, d3694, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3694, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36478 p hg
    simpa only [d8125, d3694, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36907 (p : Pattern) (guard : d8126 p = 1) : d3695 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d3695, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36893 p hg
    simpa only [d8126, d3695, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d3695, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36906 p hg
    simpa only [d8126, d3695, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36908 (p : Pattern) (guard : d8101 p = 1) : d3674 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3674, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36080 p hg
    simpa only [d8101, d3674, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3674, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36180 p hg
    simpa only [d8101, d3674, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36909 (p : Pattern) (guard : d8107 p = 1) : d3697 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3697, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36908 p hg
    simpa only [d8107, d3697, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3697, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36240 p hg
    simpa only [d8107, d3697, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36910 (p : Pattern) (guard : d8113 p = 1) : d3698 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3698, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36909 p hg
    simpa only [d8113, d3698, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3698, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36241 p hg
    simpa only [d8113, d3698, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36911 (p : Pattern) (guard : d8119 p = 1) : d3700 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3700, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36910 p hg
    simpa only [d8119, d3700, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3700, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36643 p hg
    simpa only [d8119, d3700, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36912 (p : Pattern) (guard : d8125 p = 1) : d3702 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3702, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36911 p hg
    simpa only [d8125, d3702, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3702, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36645 p hg
    simpa only [d8125, d3702, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36913 (p : Pattern) (guard : d8118 p = 1) : d3699 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3699, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36870 p hg
    simpa only [d8118, d3699, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3699, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d3699, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36914 (p : Pattern) (guard : d8124 p = 1) : d3701 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3701, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36913 p hg
    simpa only [d8124, d3701, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3701, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d3701, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36915 (p : Pattern) (guard : d8130 p = 1) : d3703 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3703, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36914 p hg
    simpa only [d8130, d3703, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3703, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36647 p hg
    simpa only [d8130, d3703, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36916 (p : Pattern) (guard : d8131 p = 1) : d3704 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d3704, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36912 p hg
    simpa only [d8131, d3704, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d3704, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36915 p hg
    simpa only [d8131, d3704, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36917 (p : Pattern) (guard : d8132 p = 1) : d3705 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d3705, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36907 p hg
    simpa only [d8132, d3705, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d3705, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36916 p hg
    simpa only [d8132, d3705, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36918 (p : Pattern) (guard : d8133 p = 1) : d3706 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d3706, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36880 p hg
    simpa only [d8133, d3706, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d3706, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36917 p hg
    simpa only [d8133, d3706, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36919 (p : Pattern) (guard : d8102 p = 1) : d3553 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36551 p hg
    simpa only [d8102, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36705 p hg
    simpa only [d8102, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36920 (p : Pattern) (guard : d8107 p = 1) : d3564 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3564, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36660 p hg
    simpa only [d8107, d3564, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3564, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36721 p hg
    simpa only [d8107, d3564, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36921 (p : Pattern) (guard : d8108 p = 1) : d3707 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3707, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36919 p hg
    simpa only [d8108, d3707, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3707, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36920 p hg
    simpa only [d8108, d3707, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36922 (p : Pattern) (guard : d8113 p = 1) : d3575 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3575, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36671 p hg
    simpa only [d8113, d3575, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3575, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36678 p hg
    simpa only [d8113, d3575, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36923 (p : Pattern) (guard : d8114 p = 1) : d3708 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d3708, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36921 p hg
    simpa only [d8114, d3708, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d3708, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36922 p hg
    simpa only [d8114, d3708, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36924 (p : Pattern) (guard : d8101 p = 1) : d3589 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3589, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36492 p hg
    simpa only [d8101, d3589, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3589, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36224 p hg
    simpa only [d8101, d3589, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36925 (p : Pattern) (guard : d8107 p = 1) : d3596 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3596, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36924 p hg
    simpa only [d8107, d3596, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3596, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36687 p hg
    simpa only [d8107, d3596, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36926 (p : Pattern) (guard : d8113 p = 1) : d3608 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3608, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36925 p hg
    simpa only [d8113, d3608, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3608, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36694 p hg
    simpa only [d8113, d3608, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36927 (p : Pattern) (guard : d8119 p = 1) : d3614 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3614, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36926 p hg
    simpa only [d8119, d3614, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3614, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36699 p hg
    simpa only [d8119, d3614, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36928 (p : Pattern) (guard : d8120 p = 1) : d3709 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d3709, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36923 p hg
    simpa only [d8120, d3709, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d3709, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36927 p hg
    simpa only [d8120, d3709, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36929 (p : Pattern) (guard : d8085 p = 1) : d13 p ≤ (0 : Int) + d349 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35933 p hg
    simpa only [d8085, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35989 p hg
    simpa only [d8085, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36930 (p : Pattern) (guard : d8090 p = 1) : d13 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36929 p hg
    simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36339 p hg
    simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36931 (p : Pattern) (guard : d8095 p = 1) : d3552 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3552, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36930 p hg
    simpa only [d8095, d3552, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3552, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36654 p hg
    simpa only [d8095, d3552, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36932 (p : Pattern) (guard : d8101 p = 1) : d3553 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3553, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36931 p hg
    simpa only [d8101, d3553, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3553, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36659 p hg
    simpa only [d8101, d3553, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36933 (p : Pattern) (guard : d8084 p = 1) : d30 p ≤ (0 : Int) + d315 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4512 p hg
    simpa only [d8084, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34407 p hg
    simpa only [d8084, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36934 (p : Pattern) (guard : d8089 p = 1) : d30 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36933 p hg
    simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36125 p hg
    simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36935 (p : Pattern) (guard : d8094 p = 1) : d30 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36934 p hg
    simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36397 p hg
    simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36936 (p : Pattern) (guard : d8100 p = 1) : d3623 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3623, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36935 p hg
    simpa only [d8100, d3623, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3623, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36710 p hg
    simpa only [d8100, d3623, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36937 (p : Pattern) (guard : d8106 p = 1) : d3628 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3628, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36936 p hg
    simpa only [d8106, d3628, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3628, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36714 p hg
    simpa only [d8106, d3628, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36938 (p : Pattern) (guard : d8107 p = 1) : d3710 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3710, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36932 p hg
    simpa only [d8107, d3710, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3710, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36937 p hg
    simpa only [d8107, d3710, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36939 (p : Pattern) (guard : d8084 p = 1) : d17 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare927 p hg
    simpa only [d8084, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34358 p hg
    simpa only [d8084, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36940 (p : Pattern) (guard : d8089 p = 1) : d17 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36939 p hg
    simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36016 p hg
    simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36941 (p : Pattern) (guard : d8094 p = 1) : d17 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36940 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36349 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36942 (p : Pattern) (guard : d8100 p = 1) : d3558 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3558, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36941 p hg
    simpa only [d8100, d3558, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3558, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36665 p hg
    simpa only [d8100, d3558, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36943 (p : Pattern) (guard : d8106 p = 1) : d3563 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3563, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36942 p hg
    simpa only [d8106, d3563, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3563, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36669 p hg
    simpa only [d8106, d3563, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36944 (p : Pattern) (guard : d8112 p = 1) : d3630 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3630, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36943 p hg
    simpa only [d8112, d3630, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3630, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36723 p hg
    simpa only [d8112, d3630, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36945 (p : Pattern) (guard : d8113 p = 1) : d3711 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3711, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36938 p hg
    simpa only [d8113, d3711, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3711, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36944 p hg
    simpa only [d8113, d3711, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36946 (p : Pattern) (guard : d8112 p = 1) : d3637 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3637, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36721 p hg
    simpa only [d8112, d3637, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3637, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36469 p hg
    simpa only [d8112, d3637, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36947 (p : Pattern) (guard : d8118 p = 1) : d3641 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3641, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36946 p hg
    simpa only [d8118, d3641, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3641, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36473 p hg
    simpa only [d8118, d3641, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36948 (p : Pattern) (guard : d8119 p = 1) : d3712 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3712, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36945 p hg
    simpa only [d8119, d3712, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3712, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36947 p hg
    simpa only [d8119, d3712, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36949 (p : Pattern) (guard : d8106 p = 1) : d3595 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3595, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36774 p hg
    simpa only [d8106, d3595, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3595, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36451 p hg
    simpa only [d8106, d3595, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36950 (p : Pattern) (guard : d8112 p = 1) : d3645 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3645, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36949 p hg
    simpa only [d8112, d3645, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3645, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36732 p hg
    simpa only [d8112, d3645, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36951 (p : Pattern) (guard : d8118 p = 1) : d3647 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3647, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36950 p hg
    simpa only [d8118, d3647, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3647, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36735 p hg
    simpa only [d8118, d3647, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36952 (p : Pattern) (guard : d8124 p = 1) : d3653 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3653, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36951 p hg
    simpa only [d8124, d3653, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3653, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36740 p hg
    simpa only [d8124, d3653, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36953 (p : Pattern) (guard : d8125 p = 1) : d3713 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3713, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36948 p hg
    simpa only [d8125, d3713, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3713, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36952 p hg
    simpa only [d8125, d3713, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36954 (p : Pattern) (guard : d8126 p = 1) : d3714 p ≤ (0 : Int) + d419 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d3714, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36928 p hg
    simpa only [d8126, d3714, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d3714, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36953 p hg
    simpa only [d8126, d3714, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36955 (p : Pattern) (guard : d8132 p = 1) : d3715 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d3715, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36954 p hg
    simpa only [d8132, d3715, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d3715, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36808 p hg
    simpa only [d8132, d3715, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36956 (p : Pattern) (guard : d8095 p = 1) : d3658 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3658, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36621 p hg
    simpa only [d8095, d3658, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3658, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36745 p hg
    simpa only [d8095, d3658, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36957 (p : Pattern) (guard : d8101 p = 1) : d3660 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3660, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36956 p hg
    simpa only [d8101, d3660, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3660, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36747 p hg
    simpa only [d8101, d3660, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36958 (p : Pattern) (guard : d8107 p = 1) : d3666 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3666, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36957 p hg
    simpa only [d8107, d3666, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3666, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36803 p hg
    simpa only [d8107, d3666, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36959 (p : Pattern) (guard : d8106 p = 1) : d3668 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3668, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36774 p hg
    simpa only [d8106, d3668, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3668, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36753 p hg
    simpa only [d8106, d3668, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
