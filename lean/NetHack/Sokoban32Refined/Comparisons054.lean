/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons053
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare7560 (p : Pattern) (guard : d1254 p = 1) : d676 p ≤ (0 : Int) + d365 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1250 p = 1 := by simpa only [d1254, d676, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7543 p hg
    simpa only [d1254, d676, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1253 p = 1 := by simpa only [d1254, d676, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7532 p hg
    simpa only [d1254, d676, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7561 (p : Pattern) (guard : d1254 p = 1) : d677 p ≤ (0 : Int) + d366 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d677, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7546 p hg
    simpa only [d677, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d677, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7560 p hg
    simpa only [d677, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7562 (p : Pattern) (guard : d1254 p = 1) : d678 p ≤ (0 : Int) + d367 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d678, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7534 p hg
    simpa only [d678, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d678, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7561 p hg
    simpa only [d678, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7563 (p : Pattern) (guard : d1254 p = 1) : d679 p ≤ (0 : Int) + d368 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1250 p = 1 := by simpa only [d1254, d679, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7552 p hg
    simpa only [d1254, d679, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1253 p = 1 := by simpa only [d1254, d679, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4174 p hg
    simpa only [d1254, d679, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7564 (p : Pattern) (guard : d1254 p = 1) : d680 p ≤ (0 : Int) + d369 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d680, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7556 p hg
    simpa only [d680, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d680, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7563 p hg
    simpa only [d680, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7565 (p : Pattern) (guard : d1250 p = 1) : d659 p ≤ (0 : Int) + d370 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1250, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7124 p hg
    simpa only [d1250, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1250, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7109 p hg
    simpa only [d1250, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7566 (p : Pattern) (guard : d1253 p = 1) : d659 p ≤ (0 : Int) + d370 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d1253, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7553 p hg
    simpa only [d1253, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1253, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7109 p hg
    simpa only [d1253, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7567 (p : Pattern) (guard : d1254 p = 1) : d659 p ≤ (0 : Int) + d370 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1250 p = 1 := by simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7565 p hg
    simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1253 p = 1 := by simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7566 p hg
    simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7568 (p : Pattern) (guard : d1254 p = 1) : d681 p ≤ (0 : Int) + d371 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1250 p = 1 := by simpa only [d1254, d681, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7565 p hg
    simpa only [d1254, d681, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1253 p = 1 := by simpa only [d1254, d681, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4174 p hg
    simpa only [d1254, d681, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7569 (p : Pattern) (guard : d1254 p = 1) : d682 p ≤ (0 : Int) + d372 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d682, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7567 p hg
    simpa only [d682, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d682, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7568 p hg
    simpa only [d682, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7570 (p : Pattern) (guard : d1254 p = 1) : d683 p ≤ (0 : Int) + d373 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d683, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7564 p hg
    simpa only [d683, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d683, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7569 p hg
    simpa only [d683, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7571 (p : Pattern) (guard : d1254 p = 1) : d684 p ≤ (0 : Int) + d374 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d684, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7562 p hg
    simpa only [d684, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d684, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7570 p hg
    simpa only [d684, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7572 (p : Pattern) (guard : d1254 p = 1) : d685 p ≤ (0 : Int) + d375 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d685, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7559 p hg
    simpa only [d685, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d685, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7571 p hg
    simpa only [d685, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7573 (p : Pattern) (guard : d1254 p = 1) : d686 p ≤ (0 : Int) + d376 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d686, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7542 p hg
    simpa only [d686, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d686, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7572 p hg
    simpa only [d686, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7574 (p : Pattern) (guard : d1254 p = 1) : d687 p ≤ (0 : Int) + d377 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d687, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7534 p hg
    simpa only [d687, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d687, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7540 p hg
    simpa only [d687, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7575 (p : Pattern) (guard : d1254 p = 1) : d688 p ≤ (0 : Int) + d378 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d688, d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7526 p hg
    simpa only [d688, d378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d688, d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7574 p hg
    simpa only [d688, d378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7576 (p : Pattern) (guard : d1254 p = 1) : d659 p ≤ (0 : Int) + d379 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1250 p = 1 := by simpa only [d1254, d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7565 p hg
    simpa only [d1254, d379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1253 p = 1 := by simpa only [d1254, d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7532 p hg
    simpa only [d1254, d379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7577 (p : Pattern) (guard : d1254 p = 1) : d659 p ≤ (0 : Int) + d380 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7567 p hg
    simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7576 p hg
    simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7578 (p : Pattern) (guard : d1254 p = 1) : d689 p ≤ (0 : Int) + d381 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d689, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7558 p hg
    simpa only [d689, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d689, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7577 p hg
    simpa only [d689, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7579 (p : Pattern) (guard : d1254 p = 1) : d690 p ≤ (0 : Int) + d382 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d690, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7551 p hg
    simpa only [d690, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d690, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7578 p hg
    simpa only [d690, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7580 (p : Pattern) (guard : d1254 p = 1) : d691 p ≤ (0 : Int) + d383 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d691, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7534 p hg
    simpa only [d691, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d691, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7539 p hg
    simpa only [d691, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7581 (p : Pattern) (guard : d1254 p = 1) : d692 p ≤ (0 : Int) + d384 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d692, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7569 p hg
    simpa only [d692, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d692, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4193 p hg
    simpa only [d692, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7582 (p : Pattern) (guard : d1254 p = 1) : d693 p ≤ (0 : Int) + d385 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d693, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7580 p hg
    simpa only [d693, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d693, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7581 p hg
    simpa only [d693, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7583 (p : Pattern) (guard : d1254 p = 1) : d694 p ≤ (0 : Int) + d386 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d694, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7579 p hg
    simpa only [d694, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d694, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7582 p hg
    simpa only [d694, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7584 (p : Pattern) (guard : d1254 p = 1) : d695 p ≤ (0 : Int) + d387 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d695, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7575 p hg
    simpa only [d695, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d695, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7583 p hg
    simpa only [d695, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7585 (p : Pattern) (guard : d1254 p = 1) : d696 p ≤ (0 : Int) + d388 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d696, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7573 p hg
    simpa only [d696, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d696, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7584 p hg
    simpa only [d696, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7586 (p : Pattern) (guard : d1171 p = 1) : d7 p ≤ (0 : Int) + d8 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1171, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7086 p hg
    simpa only [d1171, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1171, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare663 p hg
    simpa only [d1171, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7587 (p : Pattern) (guard : d1171 p = 1) : d13 p ≤ (0 : Int) + d14 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1171, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7088 p hg
    simpa only [d1171, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1171, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare668 p hg
    simpa only [d1171, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7588 (p : Pattern) (guard : d1171 p = 1) : d653 p ≤ (0 : Int) + d15 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d653, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7586 p hg
    simpa only [d653, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d653, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7587 p hg
    simpa only [d653, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7589 (p : Pattern) (guard : d1171 p = 1) : d654 p ≤ (0 : Int) + d16 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d654, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7586 p hg
    simpa only [d654, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d654, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7588 p hg
    simpa only [d654, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7590 (p : Pattern) (guard : d0 p = 1) : d7 p ≤ (0 : Int) + d19 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7591 (p : Pattern) (guard : d1171 p = 1) : d7 p ≤ (0 : Int) + d20 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1171, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7272 p hg
    simpa only [d1171, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1171, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7590 p hg
    simpa only [d1171, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7592 (p : Pattern) (guard : d0 p = 1) : d13 p ≤ (0 : Int) + d23 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7593 (p : Pattern) (guard : d1171 p = 1) : d13 p ≤ (0 : Int) + d24 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1171, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7274 p hg
    simpa only [d1171, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1171, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7592 p hg
    simpa only [d1171, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7594 (p : Pattern) (guard : d1171 p = 1) : d653 p ≤ (0 : Int) + d25 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d653, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7591 p hg
    simpa only [d653, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d653, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7593 p hg
    simpa only [d653, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7595 (p : Pattern) (guard : d1171 p = 1) : d654 p ≤ (0 : Int) + d26 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d654, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7591 p hg
    simpa only [d654, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d654, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7594 p hg
    simpa only [d654, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7596 (p : Pattern) (guard : d1171 p = 1) : d654 p ≤ (0 : Int) + d27 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7589 p hg
    simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7595 p hg
    simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7597 (p : Pattern) (guard : d1172 p = 1) : d654 p ≤ (0 : Int) + d28 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1172, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7091 p hg
    simpa only [d1172, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d1172, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7596 p hg
    simpa only [d1172, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7598 (p : Pattern) (guard : d0 p = 1) : d654 p ≤ (0 : Int) + d141 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7599 (p : Pattern) (guard : d1173 p = 1) : d654 p ≤ (0 : Int) + d256 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1172 p = 1 := by simpa only [d1173, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7597 p hg
    simpa only [d1173, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1173, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7598 p hg
    simpa only [d1173, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7600 (p : Pattern) (guard : d1171 p = 1) : d653 p ≤ (0 : Int) + d46 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7588 p hg
    simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7594 p hg
    simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7601 (p : Pattern) (guard : d1172 p = 1) : d653 p ≤ (0 : Int) + d47 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1172, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7090 p hg
    simpa only [d1172, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d1172, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7600 p hg
    simpa only [d1172, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7602 (p : Pattern) (guard : d0 p = 1) : d653 p ≤ (0 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7603 (p : Pattern) (guard : d1173 p = 1) : d653 p ≤ (0 : Int) + d257 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1172 p = 1 := by simpa only [d1173, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7601 p hg
    simpa only [d1173, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1173, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7602 p hg
    simpa only [d1173, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7604 (p : Pattern) (guard : d1171 p = 1) : d655 p ≤ (0 : Int) + d52 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d655, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7586 p hg
    simpa only [d655, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d655, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2819 p hg
    simpa only [d655, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7605 (p : Pattern) (guard : d1171 p = 1) : d656 p ≤ (0 : Int) + d53 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d656, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7588 p hg
    simpa only [d656, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d656, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7604 p hg
    simpa only [d656, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7606 (p : Pattern) (guard : d1171 p = 1) : d655 p ≤ (0 : Int) + d54 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d655, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7591 p hg
    simpa only [d655, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d655, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2819 p hg
    simpa only [d655, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7607 (p : Pattern) (guard : d1171 p = 1) : d656 p ≤ (0 : Int) + d55 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d656, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7594 p hg
    simpa only [d656, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d656, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7606 p hg
    simpa only [d656, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7608 (p : Pattern) (guard : d1171 p = 1) : d656 p ≤ (0 : Int) + d56 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7605 p hg
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7607 p hg
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7609 (p : Pattern) (guard : d1172 p = 1) : d656 p ≤ (0 : Int) + d57 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1172, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7097 p hg
    simpa only [d1172, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d1172, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7608 p hg
    simpa only [d1172, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7610 (p : Pattern) (guard : d0 p = 1) : d656 p ≤ (0 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7611 (p : Pattern) (guard : d1173 p = 1) : d656 p ≤ (0 : Int) + d258 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1172 p = 1 := by simpa only [d1173, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7609 p hg
    simpa only [d1173, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1173, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7610 p hg
    simpa only [d1173, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7612 (p : Pattern) (guard : d1173 p = 1) : d657 p ≤ (0 : Int) + d259 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d657, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7603 p hg
    simpa only [d657, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d657, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7611 p hg
    simpa only [d657, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7613 (p : Pattern) (guard : d1173 p = 1) : d658 p ≤ (0 : Int) + d260 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d658, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7599 p hg
    simpa only [d658, d260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d658, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7612 p hg
    simpa only [d658, d260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7614 (p : Pattern) (guard : d0 p = 1) : d661 p ≤ (0 : Int) + d141 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7615 (p : Pattern) (guard : d1173 p = 1) : d662 p ≤ (0 : Int) + d256 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1172 p = 1 := by simpa only [d1173, d662, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7597 p hg
    simpa only [d1173, d662, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1173, d662, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7614 p hg
    simpa only [d1173, d662, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7616 (p : Pattern) (guard : d0 p = 1) : d663 p ≤ (0 : Int) + d149 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7617 (p : Pattern) (guard : d1173 p = 1) : d664 p ≤ (0 : Int) + d261 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1172 p = 1 := by simpa only [d1173, d664, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7597 p hg
    simpa only [d1173, d664, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1173, d664, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7616 p hg
    simpa only [d1173, d664, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7618 (p : Pattern) (guard : d1173 p = 1) : d665 p ≤ (0 : Int) + d262 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d665, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7615 p hg
    simpa only [d665, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d665, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7617 p hg
    simpa only [d665, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7619 (p : Pattern) (guard : d0 p = 1) : d666 p ≤ (0 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7620 (p : Pattern) (guard : d1173 p = 1) : d667 p ≤ (0 : Int) + d257 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1172 p = 1 := by simpa only [d1173, d667, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7601 p hg
    simpa only [d1173, d667, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1173, d667, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7619 p hg
    simpa only [d1173, d667, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7621 (p : Pattern) (guard : d0 p = 1) : d668 p ≤ (0 : Int) + d153 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7622 (p : Pattern) (guard : d1173 p = 1) : d669 p ≤ (0 : Int) + d263 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1172 p = 1 := by simpa only [d1173, d669, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7609 p hg
    simpa only [d1173, d669, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1173, d669, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7621 p hg
    simpa only [d1173, d669, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7623 (p : Pattern) (guard : d1173 p = 1) : d670 p ≤ (0 : Int) + d264 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d670, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7620 p hg
    simpa only [d670, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d670, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7622 p hg
    simpa only [d670, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7624 (p : Pattern) (guard : d1173 p = 1) : d671 p ≤ (0 : Int) + d265 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d671, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7618 p hg
    simpa only [d671, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d671, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7623 p hg
    simpa only [d671, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7625 (p : Pattern) (guard : d1173 p = 1) : d672 p ≤ (0 : Int) + d266 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d672, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7613 p hg
    simpa only [d672, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d672, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7624 p hg
    simpa only [d672, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7626 (p : Pattern) (guard : d1171 p = 1) : d673 p ≤ (0 : Int) + d86 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d673, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7586 p hg
    simpa only [d673, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d673, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7604 p hg
    simpa only [d673, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7627 (p : Pattern) (guard : d1171 p = 1) : d673 p ≤ (0 : Int) + d87 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d673, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7591 p hg
    simpa only [d673, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d673, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7606 p hg
    simpa only [d673, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7628 (p : Pattern) (guard : d1171 p = 1) : d673 p ≤ (0 : Int) + d88 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7626 p hg
    simpa only [d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7627 p hg
    simpa only [d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7629 (p : Pattern) (guard : d1172 p = 1) : d673 p ≤ (0 : Int) + d89 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1172, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7117 p hg
    simpa only [d1172, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d1172, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7628 p hg
    simpa only [d1172, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7630 (p : Pattern) (guard : d0 p = 1) : d673 p ≤ (0 : Int) + d149 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7631 (p : Pattern) (guard : d1173 p = 1) : d673 p ≤ (0 : Int) + d267 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1172 p = 1 := by simpa only [d1173, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7629 p hg
    simpa only [d1173, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1173, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7630 p hg
    simpa only [d1173, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7632 (p : Pattern) (guard : d1173 p = 1) : d674 p ≤ (0 : Int) + d268 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d674, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7599 p hg
    simpa only [d674, d268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d674, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7631 p hg
    simpa only [d674, d268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7633 (p : Pattern) (guard : d1171 p = 1) : d659 p ≤ (0 : Int) + d97 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d659, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7587 p hg
    simpa only [d659, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d659, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2819 p hg
    simpa only [d659, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7634 (p : Pattern) (guard : d1171 p = 1) : d660 p ≤ (0 : Int) + d98 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d660, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7587 p hg
    simpa only [d660, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d660, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7633 p hg
    simpa only [d660, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7635 (p : Pattern) (guard : d1171 p = 1) : d659 p ≤ (0 : Int) + d70 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d659, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7593 p hg
    simpa only [d659, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d659, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2819 p hg
    simpa only [d659, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7636 (p : Pattern) (guard : d1171 p = 1) : d660 p ≤ (0 : Int) + d71 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d660, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7593 p hg
    simpa only [d660, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d660, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7635 p hg
    simpa only [d660, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7637 (p : Pattern) (guard : d1171 p = 1) : d660 p ≤ (0 : Int) + d99 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7634 p hg
    simpa only [d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7636 p hg
    simpa only [d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7638 (p : Pattern) (guard : d1172 p = 1) : d660 p ≤ (0 : Int) + d100 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1172, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7125 p hg
    simpa only [d1172, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d1172, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7637 p hg
    simpa only [d1172, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7639 (p : Pattern) (guard : d0 p = 1) : d660 p ≤ (0 : Int) + d152 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7640 (p : Pattern) (guard : d1173 p = 1) : d660 p ≤ (0 : Int) + d269 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1172 p = 1 := by simpa only [d1173, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7638 p hg
    simpa only [d1173, d269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1173, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7639 p hg
    simpa only [d1173, d269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7641 (p : Pattern) (guard : d0 p = 1) : d660 p ≤ (0 : Int) + d153 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7642 (p : Pattern) (guard : d1173 p = 1) : d660 p ≤ (0 : Int) + d270 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1172 p = 1 := by simpa only [d1173, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7638 p hg
    simpa only [d1173, d270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1173, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7641 p hg
    simpa only [d1173, d270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7643 (p : Pattern) (guard : d1173 p = 1) : d660 p ≤ (0 : Int) + d271 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7640 p hg
    simpa only [d271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7642 p hg
    simpa only [d271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7644 (p : Pattern) (guard : d1173 p = 1) : d675 p ≤ (0 : Int) + d272 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d675, d272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7632 p hg
    simpa only [d675, d272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d675, d272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7643 p hg
    simpa only [d675, d272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7645 (p : Pattern) (guard : d0 p = 1) : d676 p ≤ (0 : Int) + d160 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7646 (p : Pattern) (guard : d1173 p = 1) : d677 p ≤ (0 : Int) + d273 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1172 p = 1 := by simpa only [d1173, d677, d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7629 p hg
    simpa only [d1173, d677, d273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1173, d677, d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7645 p hg
    simpa only [d1173, d677, d273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7647 (p : Pattern) (guard : d1173 p = 1) : d678 p ≤ (0 : Int) + d274 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d678, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7617 p hg
    simpa only [d678, d274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d678, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7646 p hg
    simpa only [d678, d274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7648 (p : Pattern) (guard : d0 p = 1) : d679 p ≤ (0 : Int) + d153 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7649 (p : Pattern) (guard : d1173 p = 1) : d680 p ≤ (0 : Int) + d270 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1172 p = 1 := by simpa only [d1173, d680, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7638 p hg
    simpa only [d1173, d680, d270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1173, d680, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7648 p hg
    simpa only [d1173, d680, d270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7650 (p : Pattern) (guard : d1171 p = 1) : d659 p ≤ (0 : Int) + d109 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7633 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7635 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7651 (p : Pattern) (guard : d1172 p = 1) : d659 p ≤ (0 : Int) + d110 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1172, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7124 p hg
    simpa only [d1172, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1171 p = 1 := by simpa only [d1172, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7650 p hg
    simpa only [d1172, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7652 (p : Pattern) (guard : d0 p = 1) : d681 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7653 (p : Pattern) (guard : d1173 p = 1) : d682 p ≤ (0 : Int) + d275 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1172 p = 1 := by simpa only [d1173, d682, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7651 p hg
    simpa only [d1173, d682, d275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1173, d682, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7652 p hg
    simpa only [d1173, d682, d275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7654 (p : Pattern) (guard : d1173 p = 1) : d683 p ≤ (0 : Int) + d276 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d683, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7649 p hg
    simpa only [d683, d276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d683, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7653 p hg
    simpa only [d683, d276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7655 (p : Pattern) (guard : d1173 p = 1) : d684 p ≤ (0 : Int) + d277 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d684, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7647 p hg
    simpa only [d684, d277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d684, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7654 p hg
    simpa only [d684, d277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7656 (p : Pattern) (guard : d1173 p = 1) : d685 p ≤ (0 : Int) + d278 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d685, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7644 p hg
    simpa only [d685, d278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d685, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7655 p hg
    simpa only [d685, d278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7657 (p : Pattern) (guard : d1173 p = 1) : d686 p ≤ (0 : Int) + d279 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d686, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7625 p hg
    simpa only [d686, d279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d686, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7656 p hg
    simpa only [d686, d279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7658 (p : Pattern) (guard : d0 p = 1) : d654 p ≤ (0 : Int) + d149 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7659 (p : Pattern) (guard : d1173 p = 1) : d654 p ≤ (0 : Int) + d261 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1172 p = 1 := by simpa only [d1173, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7597 p hg
    simpa only [d1173, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1173, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7658 p hg
    simpa only [d1173, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7660 (p : Pattern) (guard : d1173 p = 1) : d654 p ≤ (0 : Int) + d262 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7599 p hg
    simpa only [d262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7659 p hg
    simpa only [d262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7661 (p : Pattern) (guard : d0 p = 1) : d656 p ≤ (0 : Int) + d153 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7662 (p : Pattern) (guard : d1173 p = 1) : d656 p ≤ (0 : Int) + d263 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1172 p = 1 := by simpa only [d1173, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7609 p hg
    simpa only [d1173, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1173, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7661 p hg
    simpa only [d1173, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7663 (p : Pattern) (guard : d1173 p = 1) : d657 p ≤ (0 : Int) + d264 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d657, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7603 p hg
    simpa only [d657, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d657, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7662 p hg
    simpa only [d657, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7664 (p : Pattern) (guard : d1173 p = 1) : d658 p ≤ (0 : Int) + d265 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d658, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7660 p hg
    simpa only [d658, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d658, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7663 p hg
    simpa only [d658, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7665 (p : Pattern) (guard : d0 p = 1) : d663 p ≤ (0 : Int) + d160 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7666 (p : Pattern) (guard : d1173 p = 1) : d664 p ≤ (0 : Int) + d280 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1172 p = 1 := by simpa only [d1173, d664, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7597 p hg
    simpa only [d1173, d664, d280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1173, d664, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7665 p hg
    simpa only [d1173, d664, d280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7667 (p : Pattern) (guard : d1173 p = 1) : d664 p ≤ (0 : Int) + d281 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7617 p hg
    simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7666 p hg
    simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7668 (p : Pattern) (guard : d0 p = 1) : d666 p ≤ (0 : Int) + d153 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7669 (p : Pattern) (guard : d1173 p = 1) : d667 p ≤ (0 : Int) + d282 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1172 p = 1 := by simpa only [d1173, d667, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7601 p hg
    simpa only [d1173, d667, d282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1173, d667, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7668 p hg
    simpa only [d1173, d667, d282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7670 (p : Pattern) (guard : d0 p = 1) : d668 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7671 (p : Pattern) (guard : d1173 p = 1) : d669 p ≤ (0 : Int) + d283 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1172 p = 1 := by simpa only [d1173, d669, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7609 p hg
    simpa only [d1173, d669, d283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1173, d669, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7670 p hg
    simpa only [d1173, d669, d283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7672 (p : Pattern) (guard : d1173 p = 1) : d670 p ≤ (0 : Int) + d284 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d670, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7669 p hg
    simpa only [d670, d284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d670, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7671 p hg
    simpa only [d670, d284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7673 (p : Pattern) (guard : d1173 p = 1) : d687 p ≤ (0 : Int) + d285 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d687, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7667 p hg
    simpa only [d687, d285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d687, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7672 p hg
    simpa only [d687, d285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7674 (p : Pattern) (guard : d1173 p = 1) : d688 p ≤ (0 : Int) + d286 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d688, d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7664 p hg
    simpa only [d688, d286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d688, d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7673 p hg
    simpa only [d688, d286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7675 (p : Pattern) (guard : d0 p = 1) : d673 p ≤ (0 : Int) + d160 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7676 (p : Pattern) (guard : d1173 p = 1) : d673 p ≤ (0 : Int) + d273 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1172 p = 1 := by simpa only [d1173, d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7629 p hg
    simpa only [d1173, d273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1173, d273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7675 p hg
    simpa only [d1173, d273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7677 (p : Pattern) (guard : d1173 p = 1) : d674 p ≤ (0 : Int) + d274 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d674, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7659 p hg
    simpa only [d674, d274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d674, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7676 p hg
    simpa only [d674, d274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7678 (p : Pattern) (guard : d1173 p = 1) : d659 p ≤ (0 : Int) + d275 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1172 p = 1 := by simpa only [d1173, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7651 p hg
    simpa only [d1173, d275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1173, d275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7109 p hg
    simpa only [d1173, d275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7679 (p : Pattern) (guard : d1173 p = 1) : d689 p ≤ (0 : Int) + d276 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d689, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7642 p hg
    simpa only [d689, d276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d689, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7678 p hg
    simpa only [d689, d276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7680 (p : Pattern) (guard : d1173 p = 1) : d690 p ≤ (0 : Int) + d277 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d690, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7677 p hg
    simpa only [d690, d277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d690, d277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7679 p hg
    simpa only [d690, d277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7681 (p : Pattern) (guard : d1173 p = 1) : d691 p ≤ (0 : Int) + d287 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d691, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7666 p hg
    simpa only [d691, d287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d691, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7671 p hg
    simpa only [d691, d287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7682 (p : Pattern) (guard : d1173 p = 1) : d692 p ≤ (0 : Int) + d288 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d692, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7653 p hg
    simpa only [d692, d288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d692, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2902 p hg
    simpa only [d692, d288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7683 (p : Pattern) (guard : d1173 p = 1) : d693 p ≤ (0 : Int) + d289 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d693, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7681 p hg
    simpa only [d693, d289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d693, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7682 p hg
    simpa only [d693, d289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7684 (p : Pattern) (guard : d1173 p = 1) : d694 p ≤ (0 : Int) + d290 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d694, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7680 p hg
    simpa only [d694, d290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d694, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7683 p hg
    simpa only [d694, d290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7685 (p : Pattern) (guard : d1173 p = 1) : d695 p ≤ (0 : Int) + d291 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d695, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7674 p hg
    simpa only [d695, d291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d695, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7684 p hg
    simpa only [d695, d291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7686 (p : Pattern) (guard : d1173 p = 1) : d696 p ≤ (0 : Int) + d292 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1173 p = 1 := by simpa only [d696, d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7657 p hg
    simpa only [d696, d292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d696, d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7685 p hg
    simpa only [d696, d292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7687 (p : Pattern) (guard : d917 p = 1) : d5 p ≤ (0 : Int) + d6 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4109 p hg
    simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3406 p hg
    simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7688 (p : Pattern) (guard : d917 p = 1) : d37 p ≤ (0 : Int) + d7 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d37, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4109 p hg
    simpa only [d37, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d37, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare952 p hg
    simpa only [d37, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7689 (p : Pattern) (guard : d917 p = 1) : d697 p ≤ (0 : Int) + d8 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d697, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7687 p hg
    simpa only [d697, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d697, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7688 p hg
    simpa only [d697, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7690 (p : Pattern) (guard : d917 p = 1) : d11 p ≤ (0 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4112 p hg
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3412 p hg
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7691 (p : Pattern) (guard : d917 p = 1) : d39 p ≤ (0 : Int) + d13 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d39, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4112 p hg
    simpa only [d39, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d39, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare952 p hg
    simpa only [d39, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7692 (p : Pattern) (guard : d917 p = 1) : d698 p ≤ (0 : Int) + d14 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d698, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7690 p hg
    simpa only [d698, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d698, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7691 p hg
    simpa only [d698, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7693 (p : Pattern) (guard : d917 p = 1) : d699 p ≤ (0 : Int) + d15 p := by
  cases selected : p 139 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d699, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7689 p hg
    simpa only [d699, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d699, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7692 p hg
    simpa only [d699, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7694 (p : Pattern) (guard : d917 p = 1) : d700 p ≤ (0 : Int) + d16 p := by
  cases selected : p 138 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d700, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7689 p hg
    simpa only [d700, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d700, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7693 p hg
    simpa only [d700, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7695 (p : Pattern) (guard : d0 p = 1) : d700 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare7696 (p : Pattern) (guard : d1248 p = 1) : d700 p ≤ (0 : Int) + d328 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1248, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7694 p hg
    simpa only [d1248, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1248, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7695 p hg
    simpa only [d1248, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7697 (p : Pattern) (guard : d917 p = 1) : d697 p ≤ (0 : Int) + d38 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d697, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7687 p hg
    simpa only [d697, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d697, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3738 p hg
    simpa only [d697, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7698 (p : Pattern) (guard : d917 p = 1) : d698 p ≤ (0 : Int) + d40 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d698, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7690 p hg
    simpa only [d698, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d698, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3740 p hg
    simpa only [d698, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare7699 (p : Pattern) (guard : d917 p = 1) : d699 p ≤ (0 : Int) + d41 p := by
  cases selected : p 139 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d699, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7697 p hg
    simpa only [d699, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d699, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7698 p hg
    simpa only [d699, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
