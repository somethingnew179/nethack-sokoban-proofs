/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons260
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare36540 (p : Pattern) (guard : d8107 p = 1) : d3607 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3607, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36539 p hg
    simpa only [d8107, d3607, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3607, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36354 p hg
    simpa only [d8107, d3607, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36541 (p : Pattern) (guard : d8108 p = 1) : d3608 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3608, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36538 p hg
    simpa only [d8108, d3608, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3608, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36540 p hg
    simpa only [d8108, d3608, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36542 (p : Pattern) (guard : d8114 p = 1) : d3614 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d3614, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36541 p hg
    simpa only [d8114, d3614, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d3614, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36360 p hg
    simpa only [d8114, d3614, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36543 (p : Pattern) (guard : d8115 p = 1) : d3727 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d3727, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36535 p hg
    simpa only [d8115, d3727, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d3727, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36542 p hg
    simpa only [d8115, d3727, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36544 (p : Pattern) (guard : d8086 p = 1) : d13 p ≤ (0 : Int) + d331 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35885 p hg
    simpa only [d8086, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36457 p hg
    simpa only [d8086, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36545 (p : Pattern) (guard : d8085 p = 1) : d3544 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d3544, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35884 p hg
    simpa only [d8085, d3544, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d3544, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35890 p hg
    simpa only [d8085, d3544, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36546 (p : Pattern) (guard : d8090 p = 1) : d3545 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d3545, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36545 p hg
    simpa only [d8090, d3545, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d3545, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36305 p hg
    simpa only [d8090, d3545, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36547 (p : Pattern) (guard : d8091 p = 1) : d3552 p ≤ (0 : Int) + d334 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3552, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36544 p hg
    simpa only [d8091, d3552, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3552, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36546 p hg
    simpa only [d8091, d3552, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36548 (p : Pattern) (guard : d8085 p = 1) : d3548 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d3548, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35886 p hg
    simpa only [d8085, d3548, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d3548, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35895 p hg
    simpa only [d8085, d3548, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36549 (p : Pattern) (guard : d8090 p = 1) : d3549 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d3549, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36548 p hg
    simpa only [d8090, d3549, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d3549, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36310 p hg
    simpa only [d8090, d3549, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36550 (p : Pattern) (guard : d8095 p = 1) : d3550 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3550, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36549 p hg
    simpa only [d8095, d3550, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3550, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d3550, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36551 (p : Pattern) (guard : d8096 p = 1) : d3553 p ≤ (0 : Int) + d337 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3553, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36547 p hg
    simpa only [d8096, d3553, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3553, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36550 p hg
    simpa only [d8096, d3553, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36552 (p : Pattern) (guard : d1 p = 1) : d30 p ≤ (0 : Int) + d364 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1209 p hg
    simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1507 p hg
    simpa only [d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36553 (p : Pattern) (guard : d8085 p = 1) : d30 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36552 p hg
    simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36056 p hg
    simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36554 (p : Pattern) (guard : d8090 p = 1) : d30 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36553 p hg
    simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36126 p hg
    simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36555 (p : Pattern) (guard : d8095 p = 1) : d3623 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3623, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36554 p hg
    simpa only [d8095, d3623, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3623, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36371 p hg
    simpa only [d8095, d3623, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36556 (p : Pattern) (guard : d8101 p = 1) : d3628 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3628, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36555 p hg
    simpa only [d8101, d3628, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3628, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36376 p hg
    simpa only [d8101, d3628, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36557 (p : Pattern) (guard : d8102 p = 1) : d3710 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3710, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36551 p hg
    simpa only [d8102, d3710, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3710, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36556 p hg
    simpa only [d8102, d3710, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36558 (p : Pattern) (guard : d8085 p = 1) : d17 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35912 p hg
    simpa only [d8085, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35914 p hg
    simpa only [d8085, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36559 (p : Pattern) (guard : d8090 p = 1) : d17 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36558 p hg
    simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36017 p hg
    simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36560 (p : Pattern) (guard : d8095 p = 1) : d3558 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3558, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36559 p hg
    simpa only [d8095, d3558, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3558, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36319 p hg
    simpa only [d8095, d3558, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36561 (p : Pattern) (guard : d8101 p = 1) : d3563 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3563, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36560 p hg
    simpa only [d8101, d3563, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3563, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36324 p hg
    simpa only [d8101, d3563, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36562 (p : Pattern) (guard : d8084 p = 1) : d23 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare691 p hg
    simpa only [d8084, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34388 p hg
    simpa only [d8084, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36563 (p : Pattern) (guard : d8089 p = 1) : d23 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36562 p hg
    simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36031 p hg
    simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36564 (p : Pattern) (guard : d8094 p = 1) : d23 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36563 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36135 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36565 (p : Pattern) (guard : d8100 p = 1) : d3568 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3568, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36564 p hg
    simpa only [d8100, d3568, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3568, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36138 p hg
    simpa only [d8100, d3568, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36566 (p : Pattern) (guard : d8106 p = 1) : d3573 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3573, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36565 p hg
    simpa only [d8106, d3573, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3573, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36386 p hg
    simpa only [d8106, d3573, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36567 (p : Pattern) (guard : d8107 p = 1) : d3630 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3630, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36561 p hg
    simpa only [d8107, d3630, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3630, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36566 p hg
    simpa only [d8107, d3630, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36568 (p : Pattern) (guard : d8108 p = 1) : d3711 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3711, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36557 p hg
    simpa only [d8108, d3711, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3711, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36567 p hg
    simpa only [d8108, d3711, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36569 (p : Pattern) (guard : d8084 p = 1) : d57 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare729 p hg
    simpa only [d8084, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34494 p hg
    simpa only [d8084, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36570 (p : Pattern) (guard : d8089 p = 1) : d57 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36569 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36092 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36571 (p : Pattern) (guard : d8094 p = 1) : d57 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36570 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36143 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36572 (p : Pattern) (guard : d8100 p = 1) : d3634 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3634, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36571 p hg
    simpa only [d8100, d3634, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3634, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36146 p hg
    simpa only [d8100, d3634, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36573 (p : Pattern) (guard : d8106 p = 1) : d3636 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3636, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36572 p hg
    simpa only [d8106, d3636, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3636, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36236 p hg
    simpa only [d8106, d3636, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36574 (p : Pattern) (guard : d8107 p = 1) : d3637 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3637, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36524 p hg
    simpa only [d8107, d3637, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3637, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36573 p hg
    simpa only [d8107, d3637, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36575 (p : Pattern) (guard : d8113 p = 1) : d3641 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3641, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36574 p hg
    simpa only [d8113, d3641, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3641, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36241 p hg
    simpa only [d8113, d3641, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36576 (p : Pattern) (guard : d8114 p = 1) : d3712 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d3712, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36568 p hg
    simpa only [d8114, d3712, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d3712, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36575 p hg
    simpa only [d8114, d3712, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36577 (p : Pattern) (guard : d8101 p = 1) : d3595 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3595, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36492 p hg
    simpa only [d8101, d3595, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3595, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36205 p hg
    simpa only [d8101, d3595, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36578 (p : Pattern) (guard : d8107 p = 1) : d3645 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3645, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36577 p hg
    simpa only [d8107, d3645, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3645, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36402 p hg
    simpa only [d8107, d3645, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36579 (p : Pattern) (guard : d8113 p = 1) : d3647 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3647, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36578 p hg
    simpa only [d8113, d3647, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3647, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36408 p hg
    simpa only [d8113, d3647, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36580 (p : Pattern) (guard : d8119 p = 1) : d3653 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3653, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36579 p hg
    simpa only [d8119, d3653, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3653, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36420 p hg
    simpa only [d8119, d3653, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36581 (p : Pattern) (guard : d8120 p = 1) : d3713 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d3713, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36576 p hg
    simpa only [d8120, d3713, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d3713, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36580 p hg
    simpa only [d8120, d3713, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36582 (p : Pattern) (guard : d8121 p = 1) : d3728 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d3728, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36543 p hg
    simpa only [d8121, d3728, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d3728, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36581 p hg
    simpa only [d8121, d3728, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36583 (p : Pattern) (guard : d8091 p = 1) : d3658 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3658, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36267 p hg
    simpa only [d8091, d3658, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3658, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36425 p hg
    simpa only [d8091, d3658, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36584 (p : Pattern) (guard : d8096 p = 1) : d3660 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3660, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36583 p hg
    simpa only [d8096, d3660, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3660, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36427 p hg
    simpa only [d8096, d3660, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36585 (p : Pattern) (guard : d8102 p = 1) : d3666 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3666, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36584 p hg
    simpa only [d8102, d3666, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3666, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36493 p hg
    simpa only [d8102, d3666, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36586 (p : Pattern) (guard : d8101 p = 1) : d3668 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3668, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36459 p hg
    simpa only [d8101, d3668, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3668, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36434 p hg
    simpa only [d8101, d3668, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36587 (p : Pattern) (guard : d8107 p = 1) : d3671 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3671, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36586 p hg
    simpa only [d8107, d3671, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3671, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36437 p hg
    simpa only [d8107, d3671, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36588 (p : Pattern) (guard : d8108 p = 1) : d3672 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3672, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36585 p hg
    simpa only [d8108, d3672, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3672, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36587 p hg
    simpa only [d8108, d3672, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36589 (p : Pattern) (guard : d8113 p = 1) : d3676 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3676, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36486 p hg
    simpa only [d8113, d3676, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3676, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36440 p hg
    simpa only [d8113, d3676, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36590 (p : Pattern) (guard : d8114 p = 1) : d3677 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d3677, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36588 p hg
    simpa only [d8114, d3677, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d3677, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36589 p hg
    simpa only [d8114, d3677, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36591 (p : Pattern) (guard : d8120 p = 1) : d3684 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d3684, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36590 p hg
    simpa only [d8120, d3684, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d3684, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36455 p hg
    simpa only [d8120, d3684, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36592 (p : Pattern) (guard : d8085 p = 1) : d13 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35869 p hg
    simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35989 p hg
    simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36593 (p : Pattern) (guard : d8090 p = 1) : d13 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36592 p hg
    simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36339 p hg
    simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36594 (p : Pattern) (guard : d8095 p = 1) : d3582 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3582, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36593 p hg
    simpa only [d8095, d3582, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3582, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36344 p hg
    simpa only [d8095, d3582, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36595 (p : Pattern) (guard : d8101 p = 1) : d3665 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3665, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36594 p hg
    simpa only [d8101, d3665, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3665, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36431 p hg
    simpa only [d8101, d3665, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36596 (p : Pattern) (guard : d8084 p = 1) : d30 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1533 p hg
    simpa only [d8084, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34407 p hg
    simpa only [d8084, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36597 (p : Pattern) (guard : d8089 p = 1) : d30 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36596 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36125 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36598 (p : Pattern) (guard : d8094 p = 1) : d30 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36597 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36397 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36599 (p : Pattern) (guard : d8100 p = 1) : d3643 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3643, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36598 p hg
    simpa only [d8100, d3643, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3643, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36400 p hg
    simpa only [d8100, d3643, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36600 (p : Pattern) (guard : d8106 p = 1) : d3678 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3678, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36599 p hg
    simpa only [d8106, d3678, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3678, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36461 p hg
    simpa only [d8106, d3678, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36601 (p : Pattern) (guard : d8107 p = 1) : d3685 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3685, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36595 p hg
    simpa only [d8107, d3685, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3685, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36600 p hg
    simpa only [d8107, d3685, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36602 (p : Pattern) (guard : d8113 p = 1) : d3687 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3687, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36601 p hg
    simpa only [d8113, d3687, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3687, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36466 p hg
    simpa only [d8113, d3687, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36603 (p : Pattern) (guard : d8119 p = 1) : d3690 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3690, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36602 p hg
    simpa only [d8119, d3690, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3690, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36474 p hg
    simpa only [d8119, d3690, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36604 (p : Pattern) (guard : d8125 p = 1) : d3694 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3694, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36603 p hg
    simpa only [d8125, d3694, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3694, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36478 p hg
    simpa only [d8125, d3694, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36605 (p : Pattern) (guard : d8126 p = 1) : d3695 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d3695, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36591 p hg
    simpa only [d8126, d3695, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d3695, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36604 p hg
    simpa only [d8126, d3695, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36606 (p : Pattern) (guard : d8127 p = 1) : d3729 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d3729, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36582 p hg
    simpa only [d8127, d3729, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d3729, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36605 p hg
    simpa only [d8127, d3729, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36607 (p : Pattern) (guard : d8091 p = 1) : d3658 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3658, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36363 p hg
    simpa only [d8091, d3658, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3658, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36425 p hg
    simpa only [d8091, d3658, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36608 (p : Pattern) (guard : d8096 p = 1) : d3660 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3660, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36607 p hg
    simpa only [d8096, d3660, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3660, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36427 p hg
    simpa only [d8096, d3660, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36609 (p : Pattern) (guard : d8102 p = 1) : d3666 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3666, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36608 p hg
    simpa only [d8102, d3666, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3666, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36595 p hg
    simpa only [d8102, d3666, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36610 (p : Pattern) (guard : d8101 p = 1) : d3668 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3668, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36492 p hg
    simpa only [d8101, d3668, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3668, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36434 p hg
    simpa only [d8101, d3668, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36611 (p : Pattern) (guard : d8107 p = 1) : d3671 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3671, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36610 p hg
    simpa only [d8107, d3671, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3671, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36437 p hg
    simpa only [d8107, d3671, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36612 (p : Pattern) (guard : d8108 p = 1) : d3672 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3672, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36609 p hg
    simpa only [d8108, d3672, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3672, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36611 p hg
    simpa only [d8108, d3672, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36613 (p : Pattern) (guard : d8113 p = 1) : d3676 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3676, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36587 p hg
    simpa only [d8113, d3676, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3676, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36440 p hg
    simpa only [d8113, d3676, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36614 (p : Pattern) (guard : d8114 p = 1) : d3677 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d3677, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36612 p hg
    simpa only [d8114, d3677, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d3677, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36613 p hg
    simpa only [d8114, d3677, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36615 (p : Pattern) (guard : d8101 p = 1) : d3678 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3678, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36132 p hg
    simpa only [d8101, d3678, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3678, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36224 p hg
    simpa only [d8101, d3678, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36616 (p : Pattern) (guard : d8107 p = 1) : d3681 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3681, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36615 p hg
    simpa only [d8107, d3681, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3681, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36452 p hg
    simpa only [d8107, d3681, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36617 (p : Pattern) (guard : d8113 p = 1) : d3682 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3682, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36616 p hg
    simpa only [d8113, d3682, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3682, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36241 p hg
    simpa only [d8113, d3682, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36618 (p : Pattern) (guard : d8119 p = 1) : d3683 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3683, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36617 p hg
    simpa only [d8119, d3683, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3683, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d3683, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36619 (p : Pattern) (guard : d8120 p = 1) : d3684 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d3684, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36614 p hg
    simpa only [d8120, d3684, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d3684, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36618 p hg
    simpa only [d8120, d3684, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36620 (p : Pattern) (guard : d8085 p = 1) : d13 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35871 p hg
    simpa only [d8085, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35989 p hg
    simpa only [d8085, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36621 (p : Pattern) (guard : d8090 p = 1) : d13 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36620 p hg
    simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36339 p hg
    simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36622 (p : Pattern) (guard : d8095 p = 1) : d3582 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3582, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36621 p hg
    simpa only [d8095, d3582, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3582, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36344 p hg
    simpa only [d8095, d3582, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36623 (p : Pattern) (guard : d8101 p = 1) : d3665 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3665, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36622 p hg
    simpa only [d8101, d3665, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3665, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36431 p hg
    simpa only [d8101, d3665, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36624 (p : Pattern) (guard : d8084 p = 1) : d30 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36219 p hg
    simpa only [d8084, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34407 p hg
    simpa only [d8084, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36625 (p : Pattern) (guard : d8089 p = 1) : d30 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36624 p hg
    simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36125 p hg
    simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36626 (p : Pattern) (guard : d8094 p = 1) : d30 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36625 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36397 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36627 (p : Pattern) (guard : d8100 p = 1) : d3643 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3643, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36626 p hg
    simpa only [d8100, d3643, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3643, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36400 p hg
    simpa only [d8100, d3643, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36628 (p : Pattern) (guard : d8106 p = 1) : d3678 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3678, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36627 p hg
    simpa only [d8106, d3678, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3678, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36461 p hg
    simpa only [d8106, d3678, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36629 (p : Pattern) (guard : d8107 p = 1) : d3685 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3685, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36623 p hg
    simpa only [d8107, d3685, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3685, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36628 p hg
    simpa only [d8107, d3685, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36630 (p : Pattern) (guard : d8084 p = 1) : d17 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare938 p hg
    simpa only [d8084, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34358 p hg
    simpa only [d8084, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36631 (p : Pattern) (guard : d8089 p = 1) : d17 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36630 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36016 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36632 (p : Pattern) (guard : d8094 p = 1) : d17 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36631 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36349 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36633 (p : Pattern) (guard : d8100 p = 1) : d3605 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3605, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36632 p hg
    simpa only [d8100, d3605, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3605, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36352 p hg
    simpa only [d8100, d3605, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36634 (p : Pattern) (guard : d8106 p = 1) : d3670 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3670, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36633 p hg
    simpa only [d8106, d3670, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3670, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36436 p hg
    simpa only [d8106, d3670, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36635 (p : Pattern) (guard : d8112 p = 1) : d3686 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3686, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36634 p hg
    simpa only [d8112, d3686, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3686, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36465 p hg
    simpa only [d8112, d3686, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36636 (p : Pattern) (guard : d8113 p = 1) : d3687 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3687, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36629 p hg
    simpa only [d8113, d3687, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3687, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36635 p hg
    simpa only [d8113, d3687, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36637 (p : Pattern) (guard : d8119 p = 1) : d3690 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3690, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36636 p hg
    simpa only [d8119, d3690, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3690, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36474 p hg
    simpa only [d8119, d3690, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36638 (p : Pattern) (guard : d8125 p = 1) : d3694 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3694, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36637 p hg
    simpa only [d8125, d3694, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3694, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36478 p hg
    simpa only [d8125, d3694, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36639 (p : Pattern) (guard : d8126 p = 1) : d3695 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d3695, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36619 p hg
    simpa only [d8126, d3695, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d3695, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36638 p hg
    simpa only [d8126, d3695, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36640 (p : Pattern) (guard : d8101 p = 1) : d3674 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3674, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36531 p hg
    simpa only [d8101, d3674, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3674, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36180 p hg
    simpa only [d8101, d3674, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36641 (p : Pattern) (guard : d8107 p = 1) : d3697 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3697, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36640 p hg
    simpa only [d8107, d3697, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3697, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36240 p hg
    simpa only [d8107, d3697, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36642 (p : Pattern) (guard : d8113 p = 1) : d3698 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3698, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36641 p hg
    simpa only [d8113, d3698, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3698, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36241 p hg
    simpa only [d8113, d3698, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36643 (p : Pattern) (guard : d8118 p = 1) : d3699 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36241 p hg
    simpa only [d8118, d3699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d3699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36644 (p : Pattern) (guard : d8119 p = 1) : d3700 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3700, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36642 p hg
    simpa only [d8119, d3700, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3700, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36643 p hg
    simpa only [d8119, d3700, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36645 (p : Pattern) (guard : d8124 p = 1) : d3701 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36643 p hg
    simpa only [d8124, d3701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d3701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36646 (p : Pattern) (guard : d8125 p = 1) : d3702 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3702, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36644 p hg
    simpa only [d8125, d3702, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3702, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36645 p hg
    simpa only [d8125, d3702, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36647 (p : Pattern) (guard : d8129 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare36648 (p : Pattern) (guard : d8130 p = 1) : d3703 p ≤ (0 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36645 p hg
    simpa only [d8130, d3703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36647 p hg
    simpa only [d8130, d3703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36649 (p : Pattern) (guard : d8131 p = 1) : d3704 p ≤ (0 : Int) + d441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d3704, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36646 p hg
    simpa only [d8131, d3704, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d3704, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36648 p hg
    simpa only [d8131, d3704, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36650 (p : Pattern) (guard : d8132 p = 1) : d3705 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d3705, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36639 p hg
    simpa only [d8132, d3705, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d3705, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36649 p hg
    simpa only [d8132, d3705, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36651 (p : Pattern) (guard : d8133 p = 1) : d3730 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d3730, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36606 p hg
    simpa only [d8133, d3730, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d3730, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36650 p hg
    simpa only [d8133, d3730, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36652 (p : Pattern) (guard : d8089 p = 1) : d3544 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d3544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35989 p hg
    simpa only [d8089, d3544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d3544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36304 p hg
    simpa only [d8089, d3544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36653 (p : Pattern) (guard : d5854 p = 1) : d3543 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36304 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29212 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36654 (p : Pattern) (guard : d8094 p = 1) : d3545 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d3545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36652 p hg
    simpa only [d8094, d3545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d3545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36653 p hg
    simpa only [d8094, d3545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36655 (p : Pattern) (guard : d8095 p = 1) : d3552 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3552, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36621 p hg
    simpa only [d8095, d3552, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3552, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36654 p hg
    simpa only [d8095, d3552, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36656 (p : Pattern) (guard : d8089 p = 1) : d3548 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d3548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35989 p hg
    simpa only [d8089, d3548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d3548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36309 p hg
    simpa only [d8089, d3548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36657 (p : Pattern) (guard : d5854 p = 1) : d3547 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36309 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29219 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36658 (p : Pattern) (guard : d8094 p = 1) : d3549 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d3549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36656 p hg
    simpa only [d8094, d3549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d3549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36657 p hg
    simpa only [d8094, d3549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36659 (p : Pattern) (guard : d8100 p = 1) : d3550 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36658 p hg
    simpa only [d8100, d3550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d3550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36660 (p : Pattern) (guard : d8101 p = 1) : d3553 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3553, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36655 p hg
    simpa only [d8101, d3553, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3553, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36659 p hg
    simpa only [d8101, d3553, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36661 (p : Pattern) (guard : d8102 p = 1) : d3553 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36519 p hg
    simpa only [d8102, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36660 p hg
    simpa only [d8102, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36662 (p : Pattern) (guard : d8095 p = 1) : d3552 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3552, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36593 p hg
    simpa only [d8095, d3552, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3552, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36654 p hg
    simpa only [d8095, d3552, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36663 (p : Pattern) (guard : d8101 p = 1) : d3553 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3553, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36662 p hg
    simpa only [d8101, d3553, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3553, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36659 p hg
    simpa only [d8101, d3553, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36664 (p : Pattern) (guard : d5854 p = 1) : d3556 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d3556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36016 p hg
    simpa only [d5854, d3556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d3556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29237 p hg
    simpa only [d5854, d3556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36665 (p : Pattern) (guard : d8099 p = 1) : d3557 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d3557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36664 p hg
    simpa only [d8099, d3557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d3557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29237 p hg
    simpa only [d8099, d3557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36666 (p : Pattern) (guard : d8100 p = 1) : d3558 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3558, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36632 p hg
    simpa only [d8100, d3558, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3558, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36665 p hg
    simpa only [d8100, d3558, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36667 (p : Pattern) (guard : d5854 p = 1) : d3560 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d3560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36016 p hg
    simpa only [d5854, d3560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d3560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29244 p hg
    simpa only [d5854, d3560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36668 (p : Pattern) (guard : d8099 p = 1) : d3561 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d3561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36667 p hg
    simpa only [d8099, d3561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d3561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29244 p hg
    simpa only [d8099, d3561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36669 (p : Pattern) (guard : d8105 p = 1) : d3562 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36668 p hg
    simpa only [d8105, d3562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d3562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36670 (p : Pattern) (guard : d8106 p = 1) : d3563 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3563, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36666 p hg
    simpa only [d8106, d3563, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3563, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36669 p hg
    simpa only [d8106, d3563, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36671 (p : Pattern) (guard : d8107 p = 1) : d3564 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3564, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36663 p hg
    simpa only [d8107, d3564, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3564, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36670 p hg
    simpa only [d8107, d3564, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36672 (p : Pattern) (guard : d8108 p = 1) : d3707 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3707, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36661 p hg
    simpa only [d8108, d3707, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3707, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36671 p hg
    simpa only [d8108, d3707, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36673 (p : Pattern) (guard : d8095 p = 1) : d3552 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3552, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36491 p hg
    simpa only [d8095, d3552, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3552, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36654 p hg
    simpa only [d8095, d3552, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36674 (p : Pattern) (guard : d8101 p = 1) : d3553 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3553, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36673 p hg
    simpa only [d8101, d3553, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3553, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36659 p hg
    simpa only [d8101, d3553, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36675 (p : Pattern) (guard : d8100 p = 1) : d3558 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36350 p hg
    simpa only [d8100, d3558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36665 p hg
    simpa only [d8100, d3558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36676 (p : Pattern) (guard : d8106 p = 1) : d3563 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36675 p hg
    simpa only [d8106, d3563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36669 p hg
    simpa only [d8106, d3563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36677 (p : Pattern) (guard : d8107 p = 1) : d3564 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3564, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36674 p hg
    simpa only [d8107, d3564, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3564, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36676 p hg
    simpa only [d8107, d3564, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36678 (p : Pattern) (guard : d8112 p = 1) : d3574 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36387 p hg
    simpa only [d8112, d3574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d3574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36679 (p : Pattern) (guard : d8113 p = 1) : d3575 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3575, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36677 p hg
    simpa only [d8113, d3575, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3575, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36678 p hg
    simpa only [d8113, d3575, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
