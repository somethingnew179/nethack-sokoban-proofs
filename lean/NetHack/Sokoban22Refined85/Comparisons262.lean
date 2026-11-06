/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons261
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare36680 (p : Pattern) (guard : d8114 p = 1) : d3708 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d3708, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36672 p hg
    simpa only [d8114, d3708, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d3708, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36679 p hg
    simpa only [d8114, d3708, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36681 (p : Pattern) (guard : d8101 p = 1) : d3589 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3589, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36459 p hg
    simpa only [d8101, d3589, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3589, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36224 p hg
    simpa only [d8101, d3589, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36682 (p : Pattern) (guard : d5854 p = 1) : d13 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36338 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17644 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36683 (p : Pattern) (guard : d8094 p = 1) : d13 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36339 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36682 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36684 (p : Pattern) (guard : d5854 p = 1) : d3578 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d3578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36338 p hg
    simpa only [d5854, d3578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d3578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29271 p hg
    simpa only [d5854, d3578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36685 (p : Pattern) (guard : d8099 p = 1) : d3581 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d3581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36684 p hg
    simpa only [d8099, d3581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d3581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31555 p hg
    simpa only [d8099, d3581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36686 (p : Pattern) (guard : d8100 p = 1) : d3582 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36683 p hg
    simpa only [d8100, d3582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36685 p hg
    simpa only [d8100, d3582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36687 (p : Pattern) (guard : d8106 p = 1) : d3595 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36686 p hg
    simpa only [d8106, d3595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36451 p hg
    simpa only [d8106, d3595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36688 (p : Pattern) (guard : d8107 p = 1) : d3596 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3596, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36681 p hg
    simpa only [d8107, d3596, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3596, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36687 p hg
    simpa only [d8107, d3596, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36689 (p : Pattern) (guard : d8106 p = 1) : d3600 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36686 p hg
    simpa only [d8106, d3600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36239 p hg
    simpa only [d8106, d3600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36690 (p : Pattern) (guard : d8099 p = 1) : d17 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36349 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17660 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36691 (p : Pattern) (guard : d0 p = 1) : d3604 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare36692 (p : Pattern) (guard : d8105 p = 1) : d3605 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36690 p hg
    simpa only [d8105, d3605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36691 p hg
    simpa only [d8105, d3605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36693 (p : Pattern) (guard : d8111 p = 1) : d3606 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36692 p hg
    simpa only [d8111, d3606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d3606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36694 (p : Pattern) (guard : d8112 p = 1) : d3607 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36689 p hg
    simpa only [d8112, d3607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36693 p hg
    simpa only [d8112, d3607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36695 (p : Pattern) (guard : d8113 p = 1) : d3608 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3608, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36688 p hg
    simpa only [d8113, d3608, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3608, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36694 p hg
    simpa only [d8113, d3608, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36696 (p : Pattern) (guard : d8106 p = 1) : d3609 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36686 p hg
    simpa only [d8106, d3609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d3609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36697 (p : Pattern) (guard : d8112 p = 1) : d3610 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36696 p hg
    simpa only [d8112, d3610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36693 p hg
    simpa only [d8112, d3610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36698 (p : Pattern) (guard : d8117 p = 1) : d3612 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36407 p hg
    simpa only [d8117, d3612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d3612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36699 (p : Pattern) (guard : d8118 p = 1) : d3613 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36697 p hg
    simpa only [d8118, d3613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36698 p hg
    simpa only [d8118, d3613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36700 (p : Pattern) (guard : d8119 p = 1) : d3614 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3614, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36695 p hg
    simpa only [d8119, d3614, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3614, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36699 p hg
    simpa only [d8119, d3614, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36701 (p : Pattern) (guard : d8120 p = 1) : d3709 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d3709, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36680 p hg
    simpa only [d8120, d3709, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d3709, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36700 p hg
    simpa only [d8120, d3709, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36702 (p : Pattern) (guard : d8085 p = 1) : d13 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35970 p hg
    simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35989 p hg
    simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36703 (p : Pattern) (guard : d8090 p = 1) : d13 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36702 p hg
    simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36339 p hg
    simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36704 (p : Pattern) (guard : d8095 p = 1) : d3552 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3552, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36703 p hg
    simpa only [d8095, d3552, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3552, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36654 p hg
    simpa only [d8095, d3552, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36705 (p : Pattern) (guard : d8101 p = 1) : d3553 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3553, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36704 p hg
    simpa only [d8101, d3553, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3553, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36659 p hg
    simpa only [d8101, d3553, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36706 (p : Pattern) (guard : d8084 p = 1) : d30 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10844 p hg
    simpa only [d8084, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34407 p hg
    simpa only [d8084, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36707 (p : Pattern) (guard : d8089 p = 1) : d30 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36706 p hg
    simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36125 p hg
    simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36708 (p : Pattern) (guard : d8094 p = 1) : d30 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36707 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36397 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36709 (p : Pattern) (guard : d5854 p = 1) : d3621 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d3621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36125 p hg
    simpa only [d5854, d3621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d3621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29325 p hg
    simpa only [d5854, d3621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36710 (p : Pattern) (guard : d8099 p = 1) : d3622 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d3622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36709 p hg
    simpa only [d8099, d3622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d3622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29325 p hg
    simpa only [d8099, d3622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36711 (p : Pattern) (guard : d8100 p = 1) : d3623 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3623, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36708 p hg
    simpa only [d8100, d3623, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3623, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36710 p hg
    simpa only [d8100, d3623, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36712 (p : Pattern) (guard : d5854 p = 1) : d3625 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d3625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36125 p hg
    simpa only [d5854, d3625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d3625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29330 p hg
    simpa only [d5854, d3625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36713 (p : Pattern) (guard : d8099 p = 1) : d3626 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d3626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36712 p hg
    simpa only [d8099, d3626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d3626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29330 p hg
    simpa only [d8099, d3626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36714 (p : Pattern) (guard : d8105 p = 1) : d3627 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36713 p hg
    simpa only [d8105, d3627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d3627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36715 (p : Pattern) (guard : d8106 p = 1) : d3628 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3628, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36711 p hg
    simpa only [d8106, d3628, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3628, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36714 p hg
    simpa only [d8106, d3628, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36716 (p : Pattern) (guard : d8107 p = 1) : d3710 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3710, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36705 p hg
    simpa only [d8107, d3710, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3710, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36715 p hg
    simpa only [d8107, d3710, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36717 (p : Pattern) (guard : d8084 p = 1) : d17 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1200 p hg
    simpa only [d8084, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34358 p hg
    simpa only [d8084, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36718 (p : Pattern) (guard : d8089 p = 1) : d17 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36717 p hg
    simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36016 p hg
    simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36719 (p : Pattern) (guard : d8094 p = 1) : d17 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36718 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36349 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36720 (p : Pattern) (guard : d8100 p = 1) : d3558 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3558, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36719 p hg
    simpa only [d8100, d3558, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3558, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36665 p hg
    simpa only [d8100, d3558, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36721 (p : Pattern) (guard : d8106 p = 1) : d3563 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3563, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36720 p hg
    simpa only [d8106, d3563, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3563, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36669 p hg
    simpa only [d8106, d3563, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36722 (p : Pattern) (guard : d0 p = 1) : d3572 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare36723 (p : Pattern) (guard : d8111 p = 1) : d3573 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36406 p hg
    simpa only [d8111, d3573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36722 p hg
    simpa only [d8111, d3573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36724 (p : Pattern) (guard : d8112 p = 1) : d3630 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3630, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36721 p hg
    simpa only [d8112, d3630, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3630, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36723 p hg
    simpa only [d8112, d3630, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36725 (p : Pattern) (guard : d8113 p = 1) : d3711 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3711, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36716 p hg
    simpa only [d8113, d3711, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3711, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36724 p hg
    simpa only [d8113, d3711, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36726 (p : Pattern) (guard : d8112 p = 1) : d3637 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3637, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36670 p hg
    simpa only [d8112, d3637, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3637, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36469 p hg
    simpa only [d8112, d3637, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36727 (p : Pattern) (guard : d8118 p = 1) : d3641 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3641, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36726 p hg
    simpa only [d8118, d3641, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3641, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36473 p hg
    simpa only [d8118, d3641, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36728 (p : Pattern) (guard : d8119 p = 1) : d3712 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3712, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36725 p hg
    simpa only [d8119, d3712, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3712, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36727 p hg
    simpa only [d8119, d3712, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36729 (p : Pattern) (guard : d8099 p = 1) : d30 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36397 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17673 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36730 (p : Pattern) (guard : d0 p = 1) : d3587 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare36731 (p : Pattern) (guard : d8105 p = 1) : d3643 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36729 p hg
    simpa only [d8105, d3643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36730 p hg
    simpa only [d8105, d3643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36732 (p : Pattern) (guard : d8111 p = 1) : d3644 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36731 p hg
    simpa only [d8111, d3644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d3644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36733 (p : Pattern) (guard : d8112 p = 1) : d3645 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36687 p hg
    simpa only [d8112, d3645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36732 p hg
    simpa only [d8112, d3645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36734 (p : Pattern) (guard : d0 p = 1) : d3611 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare36735 (p : Pattern) (guard : d8117 p = 1) : d3646 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36693 p hg
    simpa only [d8117, d3646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36734 p hg
    simpa only [d8117, d3646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36736 (p : Pattern) (guard : d8118 p = 1) : d3647 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36733 p hg
    simpa only [d8118, d3647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36735 p hg
    simpa only [d8118, d3647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36737 (p : Pattern) (guard : d0 p = 1) : d3648 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare36738 (p : Pattern) (guard : d8117 p = 1) : d3649 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36693 p hg
    simpa only [d8117, d3649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36737 p hg
    simpa only [d8117, d3649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36739 (p : Pattern) (guard : d0 p = 1) : d3651 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare36740 (p : Pattern) (guard : d8123 p = 1) : d3652 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36738 p hg
    simpa only [d8123, d3652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36739 p hg
    simpa only [d8123, d3652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36741 (p : Pattern) (guard : d8124 p = 1) : d3653 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36736 p hg
    simpa only [d8124, d3653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36740 p hg
    simpa only [d8124, d3653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36742 (p : Pattern) (guard : d8125 p = 1) : d3713 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3713, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36728 p hg
    simpa only [d8125, d3713, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3713, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36741 p hg
    simpa only [d8125, d3713, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36743 (p : Pattern) (guard : d8126 p = 1) : d3714 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d3714, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36701 p hg
    simpa only [d8126, d3714, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d3714, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36742 p hg
    simpa only [d8126, d3714, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36744 (p : Pattern) (guard : d5854 p = 1) : d3656 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d3656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36304 p hg
    simpa only [d5854, d3656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d3656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29271 p hg
    simpa only [d5854, d3656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36745 (p : Pattern) (guard : d8094 p = 1) : d3657 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d3657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36342 p hg
    simpa only [d8094, d3657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d3657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36744 p hg
    simpa only [d8094, d3657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36746 (p : Pattern) (guard : d8095 p = 1) : d3658 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3658, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36491 p hg
    simpa only [d8095, d3658, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3658, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36745 p hg
    simpa only [d8095, d3658, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36747 (p : Pattern) (guard : d8100 p = 1) : d3659 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36654 p hg
    simpa only [d8100, d3659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d3659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36748 (p : Pattern) (guard : d8101 p = 1) : d3660 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3660, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36746 p hg
    simpa only [d8101, d3660, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3660, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36747 p hg
    simpa only [d8101, d3660, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36749 (p : Pattern) (guard : d8099 p = 1) : d3663 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d3663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36684 p hg
    simpa only [d8099, d3663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d3663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31651 p hg
    simpa only [d8099, d3663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36750 (p : Pattern) (guard : d8105 p = 1) : d3664 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36749 p hg
    simpa only [d8105, d3664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d3664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36751 (p : Pattern) (guard : d8106 p = 1) : d3665 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36686 p hg
    simpa only [d8106, d3665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36750 p hg
    simpa only [d8106, d3665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36752 (p : Pattern) (guard : d8107 p = 1) : d3666 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3666, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36748 p hg
    simpa only [d8107, d3666, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3666, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36751 p hg
    simpa only [d8107, d3666, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36753 (p : Pattern) (guard : d8105 p = 1) : d3667 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36685 p hg
    simpa only [d8105, d3667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d3667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36754 (p : Pattern) (guard : d8106 p = 1) : d3668 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36686 p hg
    simpa only [d8106, d3668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36753 p hg
    simpa only [d8106, d3668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36755 (p : Pattern) (guard : d0 p = 1) : d3669 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare36756 (p : Pattern) (guard : d8111 p = 1) : d3670 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36692 p hg
    simpa only [d8111, d3670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36755 p hg
    simpa only [d8111, d3670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36757 (p : Pattern) (guard : d8112 p = 1) : d3671 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36754 p hg
    simpa only [d8112, d3671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36756 p hg
    simpa only [d8112, d3671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36758 (p : Pattern) (guard : d8113 p = 1) : d3672 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3672, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36752 p hg
    simpa only [d8113, d3672, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3672, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36757 p hg
    simpa only [d8113, d3672, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36759 (p : Pattern) (guard : d8117 p = 1) : d3675 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36465 p hg
    simpa only [d8117, d3675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d3675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36760 (p : Pattern) (guard : d8118 p = 1) : d3676 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36757 p hg
    simpa only [d8118, d3676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36759 p hg
    simpa only [d8118, d3676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36761 (p : Pattern) (guard : d8119 p = 1) : d3677 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3677, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36758 p hg
    simpa only [d8119, d3677, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3677, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36760 p hg
    simpa only [d8119, d3677, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36762 (p : Pattern) (guard : d8099 p = 1) : d34 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36446 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17677 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36763 (p : Pattern) (guard : d0 p = 1) : d3593 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare36764 (p : Pattern) (guard : d8105 p = 1) : d3679 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36762 p hg
    simpa only [d8105, d3679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36763 p hg
    simpa only [d8105, d3679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36765 (p : Pattern) (guard : d0 p = 1) : d3594 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare36766 (p : Pattern) (guard : d8111 p = 1) : d3680 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36764 p hg
    simpa only [d8111, d3680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36765 p hg
    simpa only [d8111, d3680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36767 (p : Pattern) (guard : d8112 p = 1) : d3681 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36462 p hg
    simpa only [d8112, d3681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36766 p hg
    simpa only [d8112, d3681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36768 (p : Pattern) (guard : d8118 p = 1) : d3682 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36767 p hg
    simpa only [d8118, d3682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36473 p hg
    simpa only [d8118, d3682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36769 (p : Pattern) (guard : d8124 p = 1) : d3683 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36768 p hg
    simpa only [d8124, d3683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d3683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36770 (p : Pattern) (guard : d8125 p = 1) : d3684 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3684, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36761 p hg
    simpa only [d8125, d3684, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3684, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36769 p hg
    simpa only [d8125, d3684, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36771 (p : Pattern) (guard : d8084 p = 1) : d13 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1493 p hg
    simpa only [d8084, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34338 p hg
    simpa only [d8084, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36772 (p : Pattern) (guard : d8089 p = 1) : d13 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36771 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36338 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36773 (p : Pattern) (guard : d8094 p = 1) : d13 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36772 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36682 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36774 (p : Pattern) (guard : d8100 p = 1) : d3582 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3582, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36773 p hg
    simpa only [d8100, d3582, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3582, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36685 p hg
    simpa only [d8100, d3582, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36775 (p : Pattern) (guard : d8106 p = 1) : d3665 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3665, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36774 p hg
    simpa only [d8106, d3665, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3665, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36750 p hg
    simpa only [d8106, d3665, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36776 (p : Pattern) (guard : d0 p = 1) : d3588 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare36777 (p : Pattern) (guard : d8111 p = 1) : d3678 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d3678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36731 p hg
    simpa only [d8111, d3678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d3678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36776 p hg
    simpa only [d8111, d3678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36778 (p : Pattern) (guard : d8112 p = 1) : d3685 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3685, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36775 p hg
    simpa only [d8112, d3685, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3685, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36777 p hg
    simpa only [d8112, d3685, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36779 (p : Pattern) (guard : d0 p = 1) : d3674 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare36780 (p : Pattern) (guard : d8117 p = 1) : d3686 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36756 p hg
    simpa only [d8117, d3686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36779 p hg
    simpa only [d8117, d3686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36781 (p : Pattern) (guard : d8118 p = 1) : d3687 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3687, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36778 p hg
    simpa only [d8118, d3687, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3687, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36780 p hg
    simpa only [d8118, d3687, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36782 (p : Pattern) (guard : d0 p = 1) : d3636 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare36783 (p : Pattern) (guard : d8117 p = 1) : d3688 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36756 p hg
    simpa only [d8117, d3688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36782 p hg
    simpa only [d8117, d3688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36784 (p : Pattern) (guard : d0 p = 1) : d3640 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare36785 (p : Pattern) (guard : d8123 p = 1) : d3689 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36783 p hg
    simpa only [d8123, d3689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36784 p hg
    simpa only [d8123, d3689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36786 (p : Pattern) (guard : d8124 p = 1) : d3690 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3690, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36781 p hg
    simpa only [d8124, d3690, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3690, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36785 p hg
    simpa only [d8124, d3690, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36787 (p : Pattern) (guard : d8117 p = 1) : d3691 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d3691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36766 p hg
    simpa only [d8117, d3691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d3691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d3691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36788 (p : Pattern) (guard : d8123 p = 1) : d3692 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d3692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36787 p hg
    simpa only [d8123, d3692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d3692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d3692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36789 (p : Pattern) (guard : d8129 p = 1) : d3693 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d3693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36788 p hg
    simpa only [d8129, d3693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d3693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d3693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36790 (p : Pattern) (guard : d8130 p = 1) : d3694 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3694, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36786 p hg
    simpa only [d8130, d3694, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3694, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36789 p hg
    simpa only [d8130, d3694, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36791 (p : Pattern) (guard : d8131 p = 1) : d3695 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d3695, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36770 p hg
    simpa only [d8131, d3695, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d3695, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36790 p hg
    simpa only [d8131, d3695, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36792 (p : Pattern) (guard : d8132 p = 1) : d3715 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d3715, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36743 p hg
    simpa only [d8132, d3715, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d3715, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36791 p hg
    simpa only [d8132, d3715, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36793 (p : Pattern) (guard : d8095 p = 1) : d3658 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3658, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36593 p hg
    simpa only [d8095, d3658, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3658, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36745 p hg
    simpa only [d8095, d3658, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36794 (p : Pattern) (guard : d8101 p = 1) : d3660 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3660, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36793 p hg
    simpa only [d8101, d3660, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3660, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36747 p hg
    simpa only [d8101, d3660, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36795 (p : Pattern) (guard : d8107 p = 1) : d3666 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3666, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36794 p hg
    simpa only [d8107, d3666, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3666, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36775 p hg
    simpa only [d8107, d3666, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36796 (p : Pattern) (guard : d8113 p = 1) : d3672 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3672, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36795 p hg
    simpa only [d8113, d3672, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3672, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36757 p hg
    simpa only [d8113, d3672, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36797 (p : Pattern) (guard : d8119 p = 1) : d3677 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3677, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36796 p hg
    simpa only [d8119, d3677, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3677, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36760 p hg
    simpa only [d8119, d3677, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36798 (p : Pattern) (guard : d8125 p = 1) : d3684 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3684, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36797 p hg
    simpa only [d8125, d3684, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3684, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36769 p hg
    simpa only [d8125, d3684, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36799 (p : Pattern) (guard : d8084 p = 1) : d13 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34460 p hg
    simpa only [d8084, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34338 p hg
    simpa only [d8084, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36800 (p : Pattern) (guard : d8089 p = 1) : d13 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36799 p hg
    simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36338 p hg
    simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36801 (p : Pattern) (guard : d8094 p = 1) : d13 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36800 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36682 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36802 (p : Pattern) (guard : d8100 p = 1) : d3582 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3582, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36801 p hg
    simpa only [d8100, d3582, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3582, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36685 p hg
    simpa only [d8100, d3582, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36803 (p : Pattern) (guard : d8106 p = 1) : d3665 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3665, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36802 p hg
    simpa only [d8106, d3665, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3665, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36750 p hg
    simpa only [d8106, d3665, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36804 (p : Pattern) (guard : d8112 p = 1) : d3685 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3685, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36803 p hg
    simpa only [d8112, d3685, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3685, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36777 p hg
    simpa only [d8112, d3685, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36805 (p : Pattern) (guard : d8118 p = 1) : d3687 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3687, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36804 p hg
    simpa only [d8118, d3687, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3687, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36780 p hg
    simpa only [d8118, d3687, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36806 (p : Pattern) (guard : d8124 p = 1) : d3690 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3690, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36805 p hg
    simpa only [d8124, d3690, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3690, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36785 p hg
    simpa only [d8124, d3690, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36807 (p : Pattern) (guard : d8130 p = 1) : d3694 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3694, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36806 p hg
    simpa only [d8130, d3694, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3694, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36789 p hg
    simpa only [d8130, d3694, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36808 (p : Pattern) (guard : d8131 p = 1) : d3695 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d3695, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36798 p hg
    simpa only [d8131, d3695, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d3695, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36807 p hg
    simpa only [d8131, d3695, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36809 (p : Pattern) (guard : d8136 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare36810 (p : Pattern) (guard : d8137 p = 1) : d3716 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d3716, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36808 p hg
    simpa only [d8137, d3716, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d3716, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36809 p hg
    simpa only [d8137, d3716, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36811 (p : Pattern) (guard : d8138 p = 1) : d3717 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d3717, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36792 p hg
    simpa only [d8138, d3717, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d3717, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36810 p hg
    simpa only [d8138, d3717, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36812 (p : Pattern) (guard : d8139 p = 1) : d3731 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8133 p = 1 := by simpa only [d8139, d3731, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36651 p hg
    simpa only [d8139, d3731, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8138 p = 1 := by simpa only [d8139, d3731, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36811 p hg
    simpa only [d8139, d3731, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36813 (p : Pattern) (guard : d8140 p = 1) : d3732 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8134 p = 1 := by simpa only [d8140, d3732, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36502 p hg
    simpa only [d8140, d3732, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8139 p = 1 := by simpa only [d8140, d3732, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36812 p hg
    simpa only [d8140, d3732, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36814 (p : Pattern) (guard : d8086 p = 1) : d3545 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d3545, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35875 p hg
    simpa only [d8086, d3545, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d3545, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35891 p hg
    simpa only [d8086, d3545, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36815 (p : Pattern) (guard : d8087 p = 1) : d3546 p ≤ (0 : Int) + d322 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d3546, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35873 p hg
    simpa only [d8087, d3546, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d3546, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36814 p hg
    simpa only [d8087, d3546, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36816 (p : Pattern) (guard : d8086 p = 1) : d3549 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d3549, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35879 p hg
    simpa only [d8086, d3549, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d3549, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35896 p hg
    simpa only [d8086, d3549, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36817 (p : Pattern) (guard : d8091 p = 1) : d3550 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3550, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36816 p hg
    simpa only [d8091, d3550, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3550, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d3550, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36818 (p : Pattern) (guard : d8092 p = 1) : d3551 p ≤ (0 : Int) + d325 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d3551, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36815 p hg
    simpa only [d8092, d3551, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d3551, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36817 p hg
    simpa only [d8092, d3551, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36819 (p : Pattern) (guard : d8097 p = 1) : d3554 p ≤ (0 : Int) + d338 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d3554, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36818 p hg
    simpa only [d8097, d3554, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d3554, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36551 p hg
    simpa only [d8097, d3554, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
