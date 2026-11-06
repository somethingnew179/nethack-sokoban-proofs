/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons246
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare34580 (p : Pattern) (guard : d8086 p = 1) : d14 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34322 p hg
    simpa only [d8086, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34340 p hg
    simpa only [d8086, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34581 (p : Pattern) (guard : d8091 p = 1) : d14 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34580 p hg
    simpa only [d8091, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34418 p hg
    simpa only [d8091, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34582 (p : Pattern) (guard : d8096 p = 1) : d16 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d16, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34581 p hg
    simpa only [d8096, d16, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d16, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34549 p hg
    simpa only [d8096, d16, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34583 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (0 : Int) + d10 p := by
  change (2 : Int) ≤ (0 : Int) + 10
  decide
theorem compare34584 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (0 : Int) + d57 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34583 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1506 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34585 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d31, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34584 p hg
    simpa only [d31, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d31, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1507 p hg
    simpa only [d31, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34586 (p : Pattern) (guard : d8085 p = 1) : d31 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34585 p hg
    simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34408 p hg
    simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34587 (p : Pattern) (guard : d8090 p = 1) : d31 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34586 p hg
    simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34473 p hg
    simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34588 (p : Pattern) (guard : d8095 p = 1) : d31 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34587 p hg
    simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34526 p hg
    simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34589 (p : Pattern) (guard : d8100 p = 1) : d32 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34526 p hg
    simpa only [d8100, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34590 (p : Pattern) (guard : d8101 p = 1) : d53 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d53, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34588 p hg
    simpa only [d8101, d53, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d53, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34589 p hg
    simpa only [d8101, d53, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34591 (p : Pattern) (guard : d8102 p = 1) : d54 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d54, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34582 p hg
    simpa only [d8102, d54, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d54, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34590 p hg
    simpa only [d8102, d54, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34592 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (0 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare937 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare899 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34593 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d18, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34592 p hg
    simpa only [d18, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d18, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare900 p hg
    simpa only [d18, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34594 (p : Pattern) (guard : d8085 p = 1) : d18 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34593 p hg
    simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34359 p hg
    simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34595 (p : Pattern) (guard : d8090 p = 1) : d18 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34594 p hg
    simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34364 p hg
    simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34596 (p : Pattern) (guard : d8095 p = 1) : d18 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34595 p hg
    simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34441 p hg
    simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34597 (p : Pattern) (guard : d8101 p = 1) : d20 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d20, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34596 p hg
    simpa only [d8101, d20, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d20, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34553 p hg
    simpa only [d8101, d20, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34598 (p : Pattern) (guard : d8105 p = 1) : d25 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34530 p hg
    simpa only [d8105, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34599 (p : Pattern) (guard : d8106 p = 1) : d26 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34531 p hg
    simpa only [d8106, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34598 p hg
    simpa only [d8106, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34600 (p : Pattern) (guard : d8107 p = 1) : d55 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d55, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34597 p hg
    simpa only [d8107, d55, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d55, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34599 p hg
    simpa only [d8107, d55, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34601 (p : Pattern) (guard : d8108 p = 1) : d56 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d56, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34591 p hg
    simpa only [d8108, d56, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d56, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34600 p hg
    simpa only [d8108, d56, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34602 (p : Pattern) (guard : d8105 p = 1) : d59 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34536 p hg
    simpa only [d8105, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34603 (p : Pattern) (guard : d8106 p = 1) : d60 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34537 p hg
    simpa only [d8106, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34602 p hg
    simpa only [d8106, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34604 (p : Pattern) (guard : d8107 p = 1) : d61 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34554 p hg
    simpa only [d8107, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34603 p hg
    simpa only [d8107, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34605 (p : Pattern) (guard : d8105 p = 1) : d41 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34540 p hg
    simpa only [d8105, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34606 (p : Pattern) (guard : d8106 p = 1) : d62 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34541 p hg
    simpa only [d8106, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34605 p hg
    simpa only [d8106, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34607 (p : Pattern) (guard : d8112 p = 1) : d63 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34606 p hg
    simpa only [d8112, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34608 (p : Pattern) (guard : d8113 p = 1) : d64 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34604 p hg
    simpa only [d8113, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34607 p hg
    simpa only [d8113, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34609 (p : Pattern) (guard : d8114 p = 1) : d65 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d65, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34601 p hg
    simpa only [d8114, d65, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d65, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34608 p hg
    simpa only [d8114, d65, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34610 (p : Pattern) (guard : d8107 p = 1) : d83 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34571 p hg
    simpa only [d8107, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34611 (p : Pattern) (guard : d8112 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare34612 (p : Pattern) (guard : d8113 p = 1) : d84 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34610 p hg
    simpa only [d8113, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34613 (p : Pattern) (guard : d8118 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare34614 (p : Pattern) (guard : d8119 p = 1) : d85 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34612 p hg
    simpa only [d8119, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34615 (p : Pattern) (guard : d8120 p = 1) : d86 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d86, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34609 p hg
    simpa only [d8120, d86, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d86, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34614 p hg
    simpa only [d8120, d86, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34616 (p : Pattern) (guard : d8121 p = 1) : d87 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d87, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34579 p hg
    simpa only [d8121, d87, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d87, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34615 p hg
    simpa only [d8121, d87, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34617 (p : Pattern) (guard : d8122 p = 1) : d88 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8116 p = 1 := by simpa only [d8122, d88, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34548 p hg
    simpa only [d8122, d88, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8121 p = 1 := by simpa only [d8122, d88, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34616 p hg
    simpa only [d8122, d88, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34618 (p : Pattern) (guard : d8127 p = 1) : d413 p ≤ (0 : Int) + d413 p := by
  omega
theorem compare34619 (p : Pattern) (guard : d8128 p = 1) : d499 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8122 p = 1 := by simpa only [d8128, d499, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34617 p hg
    simpa only [d8128, d499, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8127 p = 1 := by simpa only [d8128, d499, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34618 p hg
    simpa only [d8128, d499, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34620 (p : Pattern) (guard : d8086 p = 1) : d14 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34404 p hg
    simpa only [d8086, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34340 p hg
    simpa only [d8086, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34621 (p : Pattern) (guard : d8091 p = 1) : d14 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34620 p hg
    simpa only [d8091, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34418 p hg
    simpa only [d8091, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34622 (p : Pattern) (guard : d8096 p = 1) : d16 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d16, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34621 p hg
    simpa only [d8096, d16, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d16, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34549 p hg
    simpa only [d8096, d16, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34623 (p : Pattern) (guard : d8097 p = 1) : d16 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34346 p hg
    simpa only [d8097, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34622 p hg
    simpa only [d8097, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34624 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (0 : Int) + d57 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1199 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare899 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34625 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d18, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34624 p hg
    simpa only [d18, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d18, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare900 p hg
    simpa only [d18, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34626 (p : Pattern) (guard : d8085 p = 1) : d18 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34625 p hg
    simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34359 p hg
    simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34627 (p : Pattern) (guard : d8090 p = 1) : d18 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34626 p hg
    simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34364 p hg
    simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34628 (p : Pattern) (guard : d8095 p = 1) : d18 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34627 p hg
    simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34441 p hg
    simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34629 (p : Pattern) (guard : d8101 p = 1) : d20 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d20, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34628 p hg
    simpa only [d8101, d20, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d20, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34553 p hg
    simpa only [d8101, d20, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34630 (p : Pattern) (guard : d8102 p = 1) : d21 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d21, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34582 p hg
    simpa only [d8102, d21, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d21, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34629 p hg
    simpa only [d8102, d21, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34631 (p : Pattern) (guard : d8103 p = 1) : d22 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d22, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34623 p hg
    simpa only [d8103, d22, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d22, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34630 p hg
    simpa only [d8103, d22, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34632 (p : Pattern) (guard : d8102 p = 1) : d21 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d21, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34550 p hg
    simpa only [d8102, d21, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d21, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34597 p hg
    simpa only [d8102, d21, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34633 (p : Pattern) (guard : d8108 p = 1) : d28 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d28, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34632 p hg
    simpa only [d8108, d28, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d28, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34560 p hg
    simpa only [d8108, d28, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34634 (p : Pattern) (guard : d8109 p = 1) : d29 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d29, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34631 p hg
    simpa only [d8109, d29, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d29, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34633 p hg
    simpa only [d8109, d29, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34635 (p : Pattern) (guard : d8096 p = 1) : d33 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d33, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34419 p hg
    simpa only [d8096, d33, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d33, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34476 p hg
    simpa only [d8096, d33, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34636 (p : Pattern) (guard : d5854 p = 1) : d14 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34416 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11458 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34637 (p : Pattern) (guard : d8094 p = 1) : d14 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34417 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34636 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34638 (p : Pattern) (guard : d8095 p = 1) : d14 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34418 p hg
    simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34637 p hg
    simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34639 (p : Pattern) (guard : d8101 p = 1) : d37 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34638 p hg
    simpa only [d8101, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34570 p hg
    simpa only [d8101, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34640 (p : Pattern) (guard : d8102 p = 1) : d38 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d38, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34635 p hg
    simpa only [d8102, d38, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d38, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34639 p hg
    simpa only [d8102, d38, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34641 (p : Pattern) (guard : d8101 p = 1) : d42 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34638 p hg
    simpa only [d8101, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34513 p hg
    simpa only [d8101, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34642 (p : Pattern) (guard : d8099 p = 1) : d18 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34440 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11461 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34643 (p : Pattern) (guard : d8100 p = 1) : d18 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34441 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34642 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34644 (p : Pattern) (guard : d8106 p = 1) : d43 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34643 p hg
    simpa only [d8106, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34645 (p : Pattern) (guard : d8107 p = 1) : d44 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34641 p hg
    simpa only [d8107, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34644 p hg
    simpa only [d8107, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34646 (p : Pattern) (guard : d8108 p = 1) : d45 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d45, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34640 p hg
    simpa only [d8108, d45, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d45, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34645 p hg
    simpa only [d8108, d45, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34647 (p : Pattern) (guard : d8101 p = 1) : d46 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34638 p hg
    simpa only [d8101, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34648 (p : Pattern) (guard : d8107 p = 1) : d47 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34647 p hg
    simpa only [d8107, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34644 p hg
    simpa only [d8107, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34649 (p : Pattern) (guard : d8112 p = 1) : d49 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34533 p hg
    simpa only [d8112, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34650 (p : Pattern) (guard : d8113 p = 1) : d50 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34648 p hg
    simpa only [d8113, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34649 p hg
    simpa only [d8113, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34651 (p : Pattern) (guard : d8114 p = 1) : d51 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d51, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34646 p hg
    simpa only [d8114, d51, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d51, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34650 p hg
    simpa only [d8114, d51, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34652 (p : Pattern) (guard : d8115 p = 1) : d52 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d52, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34634 p hg
    simpa only [d8115, d52, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d52, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34651 p hg
    simpa only [d8115, d52, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34653 (p : Pattern) (guard : d8086 p = 1) : d14 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34373 p hg
    simpa only [d8086, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34340 p hg
    simpa only [d8086, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34654 (p : Pattern) (guard : d8091 p = 1) : d14 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34653 p hg
    simpa only [d8091, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34418 p hg
    simpa only [d8091, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34655 (p : Pattern) (guard : d8096 p = 1) : d16 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d16, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34654 p hg
    simpa only [d8096, d16, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d16, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34549 p hg
    simpa only [d8096, d16, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34656 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (0 : Int) + d190 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4511 p hg
    simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1506 p hg
    simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34657 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (0 : Int) + d315 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d31, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34656 p hg
    simpa only [d31, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d31, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1507 p hg
    simpa only [d31, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34658 (p : Pattern) (guard : d8085 p = 1) : d31 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34657 p hg
    simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34408 p hg
    simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34659 (p : Pattern) (guard : d8090 p = 1) : d31 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34658 p hg
    simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34473 p hg
    simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34660 (p : Pattern) (guard : d8095 p = 1) : d31 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34659 p hg
    simpa only [d8095, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34526 p hg
    simpa only [d8095, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34661 (p : Pattern) (guard : d8101 p = 1) : d53 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d53, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34660 p hg
    simpa only [d8101, d53, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d53, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34589 p hg
    simpa only [d8101, d53, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34662 (p : Pattern) (guard : d8102 p = 1) : d54 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d54, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34655 p hg
    simpa only [d8102, d54, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d54, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34661 p hg
    simpa only [d8102, d54, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34663 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (0 : Int) + d23 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare926 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare899 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34664 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d18, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34663 p hg
    simpa only [d18, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d18, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare900 p hg
    simpa only [d18, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34665 (p : Pattern) (guard : d8085 p = 1) : d18 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34664 p hg
    simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34359 p hg
    simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34666 (p : Pattern) (guard : d8090 p = 1) : d18 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34665 p hg
    simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34364 p hg
    simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34667 (p : Pattern) (guard : d8095 p = 1) : d18 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34666 p hg
    simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34441 p hg
    simpa only [d8095, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34668 (p : Pattern) (guard : d8101 p = 1) : d20 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d20, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34667 p hg
    simpa only [d8101, d20, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d20, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34553 p hg
    simpa only [d8101, d20, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34669 (p : Pattern) (guard : d8107 p = 1) : d55 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d55, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34668 p hg
    simpa only [d8107, d55, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d55, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34599 p hg
    simpa only [d8107, d55, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34670 (p : Pattern) (guard : d8108 p = 1) : d56 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d56, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34662 p hg
    simpa only [d8108, d56, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d56, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34669 p hg
    simpa only [d8108, d56, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34671 (p : Pattern) (guard : d8107 p = 1) : d61 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d61, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34629 p hg
    simpa only [d8107, d61, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d61, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34603 p hg
    simpa only [d8107, d61, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34672 (p : Pattern) (guard : d8113 p = 1) : d64 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d64, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34671 p hg
    simpa only [d8113, d64, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d64, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34607 p hg
    simpa only [d8113, d64, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34673 (p : Pattern) (guard : d8114 p = 1) : d65 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d65, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34670 p hg
    simpa only [d8114, d65, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d65, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34672 p hg
    simpa only [d8114, d65, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34674 (p : Pattern) (guard : d8085 p = 1) : d14 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34332 p hg
    simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34339 p hg
    simpa only [d8085, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34675 (p : Pattern) (guard : d8090 p = 1) : d14 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34674 p hg
    simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34417 p hg
    simpa only [d8090, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34676 (p : Pattern) (guard : d8095 p = 1) : d14 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34675 p hg
    simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34637 p hg
    simpa only [d8095, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34677 (p : Pattern) (guard : d8101 p = 1) : d37 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d37, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34676 p hg
    simpa only [d8101, d37, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d37, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34570 p hg
    simpa only [d8101, d37, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34678 (p : Pattern) (guard : d8099 p = 1) : d31 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34525 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11495 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34679 (p : Pattern) (guard : d8100 p = 1) : d31 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34526 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34678 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34680 (p : Pattern) (guard : d8106 p = 1) : d66 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34679 p hg
    simpa only [d8106, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34681 (p : Pattern) (guard : d8107 p = 1) : d67 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d67, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34677 p hg
    simpa only [d8107, d67, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d67, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34680 p hg
    simpa only [d8107, d67, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34682 (p : Pattern) (guard : d8105 p = 1) : d24 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34530 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11467 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34683 (p : Pattern) (guard : d8111 p = 1) : d48 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34682 p hg
    simpa only [d8111, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34684 (p : Pattern) (guard : d8112 p = 1) : d68 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34644 p hg
    simpa only [d8112, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34683 p hg
    simpa only [d8112, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34685 (p : Pattern) (guard : d8113 p = 1) : d69 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d69, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34681 p hg
    simpa only [d8113, d69, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d69, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34684 p hg
    simpa only [d8113, d69, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34686 (p : Pattern) (guard : d8105 p = 1) : d58 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34536 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11502 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34687 (p : Pattern) (guard : d8111 p = 1) : d70 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34686 p hg
    simpa only [d8111, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34688 (p : Pattern) (guard : d8112 p = 1) : d71 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34644 p hg
    simpa only [d8112, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34687 p hg
    simpa only [d8112, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34689 (p : Pattern) (guard : d8105 p = 1) : d40 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34540 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11507 p hg
    simpa only [d8105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34690 (p : Pattern) (guard : d8111 p = 1) : d72 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34689 p hg
    simpa only [d8111, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34691 (p : Pattern) (guard : d8117 p = 1) : d73 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34690 p hg
    simpa only [d8117, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34692 (p : Pattern) (guard : d8118 p = 1) : d74 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34688 p hg
    simpa only [d8118, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34691 p hg
    simpa only [d8118, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34693 (p : Pattern) (guard : d8119 p = 1) : d75 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d75, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34685 p hg
    simpa only [d8119, d75, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d75, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34692 p hg
    simpa only [d8119, d75, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34694 (p : Pattern) (guard : d8120 p = 1) : d76 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d76, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34673 p hg
    simpa only [d8120, d76, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d76, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34693 p hg
    simpa only [d8120, d76, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34695 (p : Pattern) (guard : d8121 p = 1) : d77 p ≤ (0 : Int) + d419 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d77, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34652 p hg
    simpa only [d8121, d77, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d77, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34694 p hg
    simpa only [d8121, d77, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34696 (p : Pattern) (guard : d8100 p = 1) : d15 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34637 p hg
    simpa only [d8100, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34697 (p : Pattern) (guard : d8101 p = 1) : d16 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d16, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34676 p hg
    simpa only [d8101, d16, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d16, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34696 p hg
    simpa only [d8101, d16, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34698 (p : Pattern) (guard : d8102 p = 1) : d16 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34550 p hg
    simpa only [d8102, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34697 p hg
    simpa only [d8102, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34699 (p : Pattern) (guard : d8101 p = 1) : d16 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34638 p hg
    simpa only [d8101, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34696 p hg
    simpa only [d8101, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34700 (p : Pattern) (guard : d8105 p = 1) : d19 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34642 p hg
    simpa only [d8105, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34701 (p : Pattern) (guard : d8106 p = 1) : d20 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34643 p hg
    simpa only [d8106, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34700 p hg
    simpa only [d8106, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34702 (p : Pattern) (guard : d8107 p = 1) : d21 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34699 p hg
    simpa only [d8107, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34701 p hg
    simpa only [d8107, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34703 (p : Pattern) (guard : d8108 p = 1) : d22 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d22, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34698 p hg
    simpa only [d8108, d22, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d22, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34702 p hg
    simpa only [d8108, d22, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34704 (p : Pattern) (guard : d8112 p = 1) : d27 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34599 p hg
    simpa only [d8112, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34705 (p : Pattern) (guard : d8113 p = 1) : d28 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34702 p hg
    simpa only [d8113, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34704 p hg
    simpa only [d8113, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34706 (p : Pattern) (guard : d8114 p = 1) : d29 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d29, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34703 p hg
    simpa only [d8114, d29, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d29, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34705 p hg
    simpa only [d8114, d29, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34707 (p : Pattern) (guard : d8095 p = 1) : d31 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34474 p hg
    simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34526 p hg
    simpa only [d8095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34708 (p : Pattern) (guard : d8101 p = 1) : d53 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34707 p hg
    simpa only [d8101, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34589 p hg
    simpa only [d8101, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34709 (p : Pattern) (guard : d8099 p = 1) : d35 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34567 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11542 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34710 (p : Pattern) (guard : d8100 p = 1) : d35 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34568 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34709 p hg
    simpa only [d8100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34711 (p : Pattern) (guard : d8105 p = 1) : d36 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34709 p hg
    simpa only [d8105, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34712 (p : Pattern) (guard : d8106 p = 1) : d78 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34710 p hg
    simpa only [d8106, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34711 p hg
    simpa only [d8106, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34713 (p : Pattern) (guard : d8107 p = 1) : d79 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34708 p hg
    simpa only [d8107, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34712 p hg
    simpa only [d8107, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34714 (p : Pattern) (guard : d8113 p = 1) : d80 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34713 p hg
    simpa only [d8113, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34607 p hg
    simpa only [d8113, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34715 (p : Pattern) (guard : d8119 p = 1) : d81 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34714 p hg
    simpa only [d8119, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34716 (p : Pattern) (guard : d8120 p = 1) : d82 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d82, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34706 p hg
    simpa only [d8120, d82, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d82, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34715 p hg
    simpa only [d8120, d82, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34717 (p : Pattern) (guard : d8085 p = 1) : d14 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34334 p hg
    simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34339 p hg
    simpa only [d8085, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34718 (p : Pattern) (guard : d8090 p = 1) : d14 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34717 p hg
    simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34417 p hg
    simpa only [d8090, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34719 (p : Pattern) (guard : d8095 p = 1) : d14 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34718 p hg
    simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34637 p hg
    simpa only [d8095, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
