/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons038
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare5460 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d530 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5461 (p : Pattern) (guard : d4117 p = 1) : d726 p ≤ (2 : Int) + d531 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d726, d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5449 p hg
    simpa only [d4117, d726, d531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d726, d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5460 p hg
    simpa only [d4117, d726, d531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5462 (p : Pattern) (guard : d4117 p = 1) : d727 p ≤ (2 : Int) + d543 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d727, d543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5461 p hg
    simpa only [d727, d543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d727, d543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5454 p hg
    simpa only [d727, d543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5463 (p : Pattern) (guard : d4118 p = 1) : d728 p ≤ (2 : Int) + d543 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4118, d728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5459 p hg
    simpa only [d4118, d728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d4118, d728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5462 p hg
    simpa only [d4118, d728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5464 (p : Pattern) (guard : d0 p = 1) : d729 p ≤ (2 : Int) + d543 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5465 (p : Pattern) (guard : d4119 p = 1) : d730 p ≤ (2 : Int) + d543 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4118 p = 1 := by simpa only [d4119, d730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5463 p hg
    simpa only [d4119, d730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4119, d730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5464 p hg
    simpa only [d4119, d730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5466 (p : Pattern) (guard : d4119 p = 1) : d731 p ≤ (2 : Int) + d543 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4119 p = 1 := by simpa only [d731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5458 p hg
    simpa only [d731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4119 p = 1 := by simpa only [d731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5465 p hg
    simpa only [d731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5467 (p : Pattern) (guard : d0 p = 1) : d734 p ≤ (2 : Int) + d543 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5468 (p : Pattern) (guard : d4118 p = 1) : d735 p ≤ (2 : Int) + d543 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4118, d735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5467 p hg
    simpa only [d4118, d735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d4118, d735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5462 p hg
    simpa only [d4118, d735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5469 (p : Pattern) (guard : d0 p = 1) : d736 p ≤ (2 : Int) + d543 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5470 (p : Pattern) (guard : d4119 p = 1) : d737 p ≤ (2 : Int) + d543 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4118 p = 1 := by simpa only [d4119, d737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5468 p hg
    simpa only [d4119, d737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4119, d737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5469 p hg
    simpa only [d4119, d737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5471 (p : Pattern) (guard : d0 p = 1) : d718 p ≤ (2 : Int) + d543 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5472 (p : Pattern) (guard : d4118 p = 1) : d738 p ≤ (2 : Int) + d543 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4118, d738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5471 p hg
    simpa only [d4118, d738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d4118, d738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5462 p hg
    simpa only [d4118, d738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5473 (p : Pattern) (guard : d4119 p = 1) : d739 p ≤ (2 : Int) + d543 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4118 p = 1 := by simpa only [d4119, d739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5472 p hg
    simpa only [d4119, d739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4119, d739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5464 p hg
    simpa only [d4119, d739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5474 (p : Pattern) (guard : d4119 p = 1) : d740 p ≤ (2 : Int) + d543 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4119 p = 1 := by simpa only [d740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5470 p hg
    simpa only [d740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4119 p = 1 := by simpa only [d740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5473 p hg
    simpa only [d740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5475 (p : Pattern) (guard : d4119 p = 1) : d741 p ≤ (2 : Int) + d543 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4119 p = 1 := by simpa only [d741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5466 p hg
    simpa only [d741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4119 p = 1 := by simpa only [d741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5474 p hg
    simpa only [d741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5476 (p : Pattern) (guard : d0 p = 1) : d744 p ≤ (2 : Int) + d579 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5477 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d568 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5478 (p : Pattern) (guard : d4117 p = 1) : d745 p ≤ (2 : Int) + d569 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d745, d569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2155 p hg
    simpa only [d4117, d745, d569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d745, d569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5477 p hg
    simpa only [d4117, d745, d569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5479 (p : Pattern) (guard : d1 p = 1) : d138 p ≤ (2 : Int) + d138 p := by
  omega
theorem compare5480 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d577 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5481 (p : Pattern) (guard : d4117 p = 1) : d746 p ≤ (2 : Int) + d578 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d746, d578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5479 p hg
    simpa only [d4117, d746, d578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d746, d578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5480 p hg
    simpa only [d4117, d746, d578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5482 (p : Pattern) (guard : d4117 p = 1) : d747 p ≤ (2 : Int) + d579 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d747, d579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5478 p hg
    simpa only [d747, d579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d747, d579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5481 p hg
    simpa only [d747, d579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5483 (p : Pattern) (guard : d4118 p = 1) : d748 p ≤ (2 : Int) + d579 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4118, d748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5476 p hg
    simpa only [d4118, d748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d4118, d748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5482 p hg
    simpa only [d4118, d748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5484 (p : Pattern) (guard : d0 p = 1) : d751 p ≤ (2 : Int) + d579 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5485 (p : Pattern) (guard : d4119 p = 1) : d752 p ≤ (2 : Int) + d579 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4118 p = 1 := by simpa only [d4119, d752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5483 p hg
    simpa only [d4119, d752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4119, d752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5484 p hg
    simpa only [d4119, d752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5486 (p : Pattern) (guard : d0 p = 1) : d754 p ≤ (2 : Int) + d579 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5487 (p : Pattern) (guard : d4118 p = 1) : d755 p ≤ (2 : Int) + d579 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4118, d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5486 p hg
    simpa only [d4118, d755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d4118, d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5482 p hg
    simpa only [d4118, d755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5488 (p : Pattern) (guard : d0 p = 1) : d756 p ≤ (2 : Int) + d579 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5489 (p : Pattern) (guard : d4119 p = 1) : d757 p ≤ (2 : Int) + d579 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4118 p = 1 := by simpa only [d4119, d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5487 p hg
    simpa only [d4119, d757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4119, d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5488 p hg
    simpa only [d4119, d757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5490 (p : Pattern) (guard : d4119 p = 1) : d758 p ≤ (2 : Int) + d579 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4119 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5485 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4119 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5489 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5491 (p : Pattern) (guard : d4119 p = 1) : d759 p ≤ (2 : Int) + d4463 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4119 p = 1 := by simpa only [d759, d4463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5466 p hg
    simpa only [d759, d4463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4119 p = 1 := by simpa only [d759, d4463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5490 p hg
    simpa only [d759, d4463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5492 (p : Pattern) (guard : d4119 p = 1) : d760 p ≤ (2 : Int) + d4464 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4119 p = 1 := by simpa only [d760, d4464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5475 p hg
    simpa only [d760, d4464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4119 p = 1 := by simpa only [d760, d4464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5491 p hg
    simpa only [d760, d4464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5493 (p : Pattern) (guard : d0 p = 1) : d718 p ≤ (2 : Int) + d605 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5494 (p : Pattern) (guard : d1 p = 1) : d189 p ≤ (2 : Int) + d189 p := by
  omega
theorem compare5495 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d595 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5496 (p : Pattern) (guard : d4117 p = 1) : d761 p ≤ (2 : Int) + d596 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d761, d596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5494 p hg
    simpa only [d4117, d761, d596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d761, d596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5495 p hg
    simpa only [d4117, d761, d596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5497 (p : Pattern) (guard : d1 p = 1) : d200 p ≤ (2 : Int) + d200 p := by
  omega
theorem compare5498 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d603 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5499 (p : Pattern) (guard : d4117 p = 1) : d762 p ≤ (2 : Int) + d604 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d762, d604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5497 p hg
    simpa only [d4117, d762, d604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d762, d604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5498 p hg
    simpa only [d4117, d762, d604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5500 (p : Pattern) (guard : d4117 p = 1) : d763 p ≤ (2 : Int) + d605 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d763, d605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5496 p hg
    simpa only [d763, d605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d763, d605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5499 p hg
    simpa only [d763, d605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5501 (p : Pattern) (guard : d4118 p = 1) : d764 p ≤ (2 : Int) + d605 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4118, d764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5493 p hg
    simpa only [d4118, d764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d4118, d764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5500 p hg
    simpa only [d4118, d764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5502 (p : Pattern) (guard : d0 p = 1) : d765 p ≤ (2 : Int) + d605 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5503 (p : Pattern) (guard : d4119 p = 1) : d766 p ≤ (2 : Int) + d605 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4118 p = 1 := by simpa only [d4119, d766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5501 p hg
    simpa only [d4119, d766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4119, d766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5502 p hg
    simpa only [d4119, d766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5504 (p : Pattern) (guard : d4119 p = 1) : d767 p ≤ (2 : Int) + d4465 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4119 p = 1 := by simpa only [d767, d4465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5470 p hg
    simpa only [d767, d4465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4119 p = 1 := by simpa only [d767, d4465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5503 p hg
    simpa only [d767, d4465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5505 (p : Pattern) (guard : d4119 p = 1) : d768 p ≤ (2 : Int) + d4466 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4119 p = 1 := by simpa only [d768, d4466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5466 p hg
    simpa only [d768, d4466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4119 p = 1 := by simpa only [d768, d4466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5504 p hg
    simpa only [d768, d4466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5506 (p : Pattern) (guard : d0 p = 1) : d770 p ≤ (2 : Int) + d616 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5507 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d614 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5508 (p : Pattern) (guard : d4117 p = 1) : d771 p ≤ (2 : Int) + d615 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d771, d615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2185 p hg
    simpa only [d4117, d771, d615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d771, d615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5507 p hg
    simpa only [d4117, d771, d615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5509 (p : Pattern) (guard : d4117 p = 1) : d772 p ≤ (2 : Int) + d616 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d772, d616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5478 p hg
    simpa only [d772, d616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d772, d616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5508 p hg
    simpa only [d772, d616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5510 (p : Pattern) (guard : d4118 p = 1) : d773 p ≤ (2 : Int) + d616 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4118, d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5506 p hg
    simpa only [d4118, d773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d4118, d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5509 p hg
    simpa only [d4118, d773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5511 (p : Pattern) (guard : d0 p = 1) : d775 p ≤ (2 : Int) + d616 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5512 (p : Pattern) (guard : d4119 p = 1) : d776 p ≤ (2 : Int) + d616 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4118 p = 1 := by simpa only [d4119, d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5510 p hg
    simpa only [d4119, d776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4119, d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5511 p hg
    simpa only [d4119, d776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5513 (p : Pattern) (guard : d0 p = 1) : d777 p ≤ (2 : Int) + d646 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5514 (p : Pattern) (guard : d1 p = 1) : d132 p ≤ (2 : Int) + d132 p := by
  omega
theorem compare5515 (p : Pattern) (guard : d1 p = 1) : d241 p ≤ (2 : Int) + d252 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d241, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5514 p hg
    simpa only [d241, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d241, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4743 p hg
    simpa only [d241, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5516 (p : Pattern) (guard : d1 p = 1) : d242 p ≤ (2 : Int) + d253 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d242, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2199 p hg
    simpa only [d242, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d242, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5515 p hg
    simpa only [d242, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5517 (p : Pattern) (guard : d1 p = 1) : d109 p ≤ (2 : Int) + d109 p := by
  omega
theorem compare5518 (p : Pattern) (guard : d1 p = 1) : d136 p ≤ (2 : Int) + d254 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d136, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5517 p hg
    simpa only [d136, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d136, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4743 p hg
    simpa only [d136, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5519 (p : Pattern) (guard : d1 p = 1) : d137 p ≤ (2 : Int) + d255 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d137, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5518 p hg
    simpa only [d137, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d137, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1724 p hg
    simpa only [d137, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5520 (p : Pattern) (guard : d1 p = 1) : d243 p ≤ (2 : Int) + d256 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d243, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5516 p hg
    simpa only [d243, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d243, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5519 p hg
    simpa only [d243, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5521 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d630 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5522 (p : Pattern) (guard : d4117 p = 1) : d778 p ≤ (2 : Int) + d631 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d778, d631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5520 p hg
    simpa only [d4117, d778, d631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d778, d631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5521 p hg
    simpa only [d4117, d778, d631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5523 (p : Pattern) (guard : d1 p = 1) : d246 p ≤ (2 : Int) + d246 p := by
  omega
theorem compare5524 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d644 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5525 (p : Pattern) (guard : d4117 p = 1) : d779 p ≤ (2 : Int) + d645 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d779, d645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5523 p hg
    simpa only [d4117, d779, d645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d779, d645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5524 p hg
    simpa only [d4117, d779, d645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5526 (p : Pattern) (guard : d4117 p = 1) : d780 p ≤ (2 : Int) + d646 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d780, d646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5522 p hg
    simpa only [d780, d646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d780, d646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5525 p hg
    simpa only [d780, d646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5527 (p : Pattern) (guard : d4118 p = 1) : d781 p ≤ (2 : Int) + d646 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4118, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5513 p hg
    simpa only [d4118, d781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d4118, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5526 p hg
    simpa only [d4118, d781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5528 (p : Pattern) (guard : d0 p = 1) : d784 p ≤ (2 : Int) + d646 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5529 (p : Pattern) (guard : d4119 p = 1) : d785 p ≤ (2 : Int) + d646 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4118 p = 1 := by simpa only [d4119, d785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5527 p hg
    simpa only [d4119, d785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4119, d785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5528 p hg
    simpa only [d4119, d785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5530 (p : Pattern) (guard : d4119 p = 1) : d786 p ≤ (2 : Int) + d4467 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4119 p = 1 := by simpa only [d786, d4467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5512 p hg
    simpa only [d786, d4467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4119 p = 1 := by simpa only [d786, d4467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5529 p hg
    simpa only [d786, d4467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5531 (p : Pattern) (guard : d4119 p = 1) : d787 p ≤ (2 : Int) + d4468 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4119 p = 1 := by simpa only [d787, d4468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5466 p hg
    simpa only [d787, d4468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4119 p = 1 := by simpa only [d787, d4468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5530 p hg
    simpa only [d787, d4468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5532 (p : Pattern) (guard : d4119 p = 1) : d788 p ≤ (2 : Int) + d4469 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4119 p = 1 := by simpa only [d788, d4469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5505 p hg
    simpa only [d788, d4469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4119 p = 1 := by simpa only [d788, d4469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5531 p hg
    simpa only [d788, d4469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5533 (p : Pattern) (guard : d4119 p = 1) : d789 p ≤ (2 : Int) + d4470 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4119 p = 1 := by simpa only [d789, d4470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5492 p hg
    simpa only [d789, d4470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4119 p = 1 := by simpa only [d789, d4470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5532 p hg
    simpa only [d789, d4470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5534 (p : Pattern) (guard : d0 p = 1) : d376 p ≤ (0 : Int) + d1512 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5535 (p : Pattern) (guard : d4471 p = 1) : d710 p ≤ (0 : Int) + d1513 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d710, d1513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5061 p hg
    simpa only [d4471, d710, d1513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d710, d1513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5534 p hg
    simpa only [d4471, d710, d1513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5536 (p : Pattern) (guard : d0 p = 1) : d391 p ≤ (0 : Int) + d1520 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5537 (p : Pattern) (guard : d4471 p = 1) : d711 p ≤ (0 : Int) + d1521 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d711, d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5087 p hg
    simpa only [d4471, d711, d1521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d711, d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5536 p hg
    simpa only [d4471, d711, d1521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5538 (p : Pattern) (guard : d4471 p = 1) : d712 p ≤ (0 : Int) + d1522 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d712, d1522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5535 p hg
    simpa only [d712, d1522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d712, d1522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5537 p hg
    simpa only [d712, d1522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5539 (p : Pattern) (guard : d0 p = 1) : d396 p ≤ (0 : Int) + d1523 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5540 (p : Pattern) (guard : d4471 p = 1) : d713 p ≤ (0 : Int) + d1524 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d713, d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5097 p hg
    simpa only [d4471, d713, d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d713, d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5539 p hg
    simpa only [d4471, d713, d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5541 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1525 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5542 (p : Pattern) (guard : d4471 p = 1) : d714 p ≤ (0 : Int) + d1526 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d714, d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5105 p hg
    simpa only [d4471, d714, d1526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d714, d1526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5541 p hg
    simpa only [d4471, d714, d1526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5543 (p : Pattern) (guard : d4471 p = 1) : d715 p ≤ (0 : Int) + d1527 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d715, d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5540 p hg
    simpa only [d715, d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d715, d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5542 p hg
    simpa only [d715, d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5544 (p : Pattern) (guard : d4471 p = 1) : d716 p ≤ (0 : Int) + d1528 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d716, d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5538 p hg
    simpa only [d716, d1528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d716, d1528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5543 p hg
    simpa only [d716, d1528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5545 (p : Pattern) (guard : d0 p = 1) : d405 p ≤ (0 : Int) + d1523 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5546 (p : Pattern) (guard : d4471 p = 1) : d717 p ≤ (0 : Int) + d1532 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d717, d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5114 p hg
    simpa only [d4471, d717, d1532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d717, d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5545 p hg
    simpa only [d4471, d717, d1532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5547 (p : Pattern) (guard : d4471 p = 1) : d718 p ≤ (0 : Int) + d1533 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d718, d1533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5546 p hg
    simpa only [d718, d1533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d718, d1533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5542 p hg
    simpa only [d718, d1533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5548 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1538 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5549 (p : Pattern) (guard : d4471 p = 1) : d719 p ≤ (0 : Int) + d1539 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d719, d1539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5120 p hg
    simpa only [d4471, d719, d1539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d719, d1539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5548 p hg
    simpa only [d4471, d719, d1539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5550 (p : Pattern) (guard : d4471 p = 1) : d95 p ≤ (0 : Int) + d1540 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d95, d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5121 p hg
    simpa only [d4471, d95, d1540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d95, d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4471, d95, d1540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5551 (p : Pattern) (guard : d4471 p = 1) : d720 p ≤ (0 : Int) + d1541 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d720, d1541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5549 p hg
    simpa only [d720, d1541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d720, d1541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5550 p hg
    simpa only [d720, d1541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5552 (p : Pattern) (guard : d4471 p = 1) : d721 p ≤ (0 : Int) + d1542 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d721, d1542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5547 p hg
    simpa only [d721, d1542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d721, d1542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5551 p hg
    simpa only [d721, d1542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5553 (p : Pattern) (guard : d4471 p = 1) : d722 p ≤ (0 : Int) + d1543 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d722, d1543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5544 p hg
    simpa only [d722, d1543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d722, d1543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5552 p hg
    simpa only [d722, d1543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5554 (p : Pattern) (guard : d0 p = 1) : d409 p ≤ (0 : Int) + d1512 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5555 (p : Pattern) (guard : d4471 p = 1) : d723 p ≤ (0 : Int) + d1547 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d723, d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5129 p hg
    simpa only [d4471, d723, d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d723, d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5554 p hg
    simpa only [d4471, d723, d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5556 (p : Pattern) (guard : d0 p = 1) : d396 p ≤ (0 : Int) + d1520 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5557 (p : Pattern) (guard : d4471 p = 1) : d724 p ≤ (0 : Int) + d1520 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5105 p hg
    simpa only [d4471, d724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5556 p hg
    simpa only [d4471, d724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5558 (p : Pattern) (guard : d4471 p = 1) : d725 p ≤ (0 : Int) + d1548 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d725, d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5555 p hg
    simpa only [d725, d1548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d725, d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5557 p hg
    simpa only [d725, d1548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5559 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1523 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5560 (p : Pattern) (guard : d4471 p = 1) : d726 p ≤ (0 : Int) + d1524 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d726, d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5097 p hg
    simpa only [d4471, d726, d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d726, d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5559 p hg
    simpa only [d4471, d726, d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5561 (p : Pattern) (guard : d4471 p = 1) : d727 p ≤ (0 : Int) + d1527 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d727, d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5560 p hg
    simpa only [d727, d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d727, d1527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5542 p hg
    simpa only [d727, d1527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5562 (p : Pattern) (guard : d4471 p = 1) : d728 p ≤ (0 : Int) + d1549 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d728, d1549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5558 p hg
    simpa only [d728, d1549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d728, d1549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5561 p hg
    simpa only [d728, d1549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5563 (p : Pattern) (guard : d4471 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare5564 (p : Pattern) (guard : d4471 p = 1) : d729 p ≤ (0 : Int) + d1550 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d729, d1550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5561 p hg
    simpa only [d729, d1550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d729, d1550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5563 p hg
    simpa only [d729, d1550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5565 (p : Pattern) (guard : d4471 p = 1) : d730 p ≤ (0 : Int) + d1551 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d730, d1551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5562 p hg
    simpa only [d730, d1551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d730, d1551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5564 p hg
    simpa only [d730, d1551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5566 (p : Pattern) (guard : d4471 p = 1) : d731 p ≤ (0 : Int) + d1552 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d731, d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5553 p hg
    simpa only [d731, d1552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d731, d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5565 p hg
    simpa only [d731, d1552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5567 (p : Pattern) (guard : d0 p = 1) : d398 p ≤ (0 : Int) + d1512 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5568 (p : Pattern) (guard : d4471 p = 1) : d732 p ≤ (0 : Int) + d1557 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d732, d1557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5141 p hg
    simpa only [d4471, d732, d1557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d732, d1557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5567 p hg
    simpa only [d4471, d732, d1557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5569 (p : Pattern) (guard : d0 p = 1) : d409 p ≤ (0 : Int) + d1520 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5570 (p : Pattern) (guard : d4471 p = 1) : d733 p ≤ (0 : Int) + d1561 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d733, d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5145 p hg
    simpa only [d4471, d733, d1561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d733, d1561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5569 p hg
    simpa only [d4471, d733, d1561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5571 (p : Pattern) (guard : d4471 p = 1) : d734 p ≤ (0 : Int) + d1562 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d734, d1562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5568 p hg
    simpa only [d734, d1562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d734, d1562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5570 p hg
    simpa only [d734, d1562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5572 (p : Pattern) (guard : d4471 p = 1) : d735 p ≤ (0 : Int) + d1563 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d735, d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5571 p hg
    simpa only [d735, d1563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d735, d1563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5561 p hg
    simpa only [d735, d1563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5573 (p : Pattern) (guard : d4471 p = 1) : d736 p ≤ (0 : Int) + d1564 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d736, d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5543 p hg
    simpa only [d736, d1564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d736, d1564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5551 p hg
    simpa only [d736, d1564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5574 (p : Pattern) (guard : d4471 p = 1) : d737 p ≤ (0 : Int) + d1565 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d737, d1565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5572 p hg
    simpa only [d737, d1565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d737, d1565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5573 p hg
    simpa only [d737, d1565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5575 (p : Pattern) (guard : d0 p = 1) : d405 p ≤ (0 : Int) + d1512 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5576 (p : Pattern) (guard : d4471 p = 1) : d717 p ≤ (0 : Int) + d1566 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d717, d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5114 p hg
    simpa only [d4471, d717, d1566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d717, d1566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5575 p hg
    simpa only [d4471, d717, d1566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5577 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1520 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5578 (p : Pattern) (guard : d4471 p = 1) : d714 p ≤ (0 : Int) + d1520 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5105 p hg
    simpa only [d4471, d714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5577 p hg
    simpa only [d4471, d714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5579 (p : Pattern) (guard : d4471 p = 1) : d718 p ≤ (0 : Int) + d1567 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d718, d1567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5576 p hg
    simpa only [d718, d1567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d718, d1567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5578 p hg
    simpa only [d718, d1567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5580 (p : Pattern) (guard : d4471 p = 1) : d738 p ≤ (0 : Int) + d1568 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d738, d1568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5579 p hg
    simpa only [d738, d1568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d738, d1568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5561 p hg
    simpa only [d738, d1568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5581 (p : Pattern) (guard : d4471 p = 1) : d739 p ≤ (0 : Int) + d1569 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d739, d1569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5580 p hg
    simpa only [d739, d1569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d739, d1569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5564 p hg
    simpa only [d739, d1569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5582 (p : Pattern) (guard : d4471 p = 1) : d740 p ≤ (0 : Int) + d1570 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d740, d1570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5574 p hg
    simpa only [d740, d1570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d740, d1570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5581 p hg
    simpa only [d740, d1570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5583 (p : Pattern) (guard : d4471 p = 1) : d741 p ≤ (0 : Int) + d1571 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d741, d1571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5566 p hg
    simpa only [d741, d1571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d741, d1571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5582 p hg
    simpa only [d741, d1571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5584 (p : Pattern) (guard : d0 p = 1) : d398 p ≤ (0 : Int) + d1578 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5585 (p : Pattern) (guard : d4471 p = 1) : d742 p ≤ (0 : Int) + d1579 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d742, d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5170 p hg
    simpa only [d4471, d742, d1579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d742, d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5584 p hg
    simpa only [d4471, d742, d1579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5586 (p : Pattern) (guard : d0 p = 1) : d409 p ≤ (0 : Int) + d1586 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5587 (p : Pattern) (guard : d4471 p = 1) : d743 p ≤ (0 : Int) + d1587 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d743, d1587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5189 p hg
    simpa only [d4471, d743, d1587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d743, d1587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5586 p hg
    simpa only [d4471, d743, d1587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5588 (p : Pattern) (guard : d4471 p = 1) : d744 p ≤ (0 : Int) + d1588 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d744, d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5585 p hg
    simpa only [d744, d1588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d744, d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5587 p hg
    simpa only [d744, d1588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5589 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1589 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5590 (p : Pattern) (guard : d4471 p = 1) : d745 p ≤ (0 : Int) + d1590 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d745, d1590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5199 p hg
    simpa only [d4471, d745, d1590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d745, d1590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5589 p hg
    simpa only [d4471, d745, d1590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5591 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1591 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5592 (p : Pattern) (guard : d4471 p = 1) : d746 p ≤ (0 : Int) + d1592 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d746, d1592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5207 p hg
    simpa only [d4471, d746, d1592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d746, d1592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5591 p hg
    simpa only [d4471, d746, d1592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5593 (p : Pattern) (guard : d4471 p = 1) : d747 p ≤ (0 : Int) + d1593 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d747, d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5590 p hg
    simpa only [d747, d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d747, d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5592 p hg
    simpa only [d747, d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5594 (p : Pattern) (guard : d4471 p = 1) : d748 p ≤ (0 : Int) + d1594 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d748, d1594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5588 p hg
    simpa only [d748, d1594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d748, d1594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5593 p hg
    simpa only [d748, d1594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5595 (p : Pattern) (guard : d0 p = 1) : d396 p ≤ (0 : Int) + d1589 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5596 (p : Pattern) (guard : d4471 p = 1) : d749 p ≤ (0 : Int) + d1590 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d749, d1590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5199 p hg
    simpa only [d4471, d749, d1590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d749, d1590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5595 p hg
    simpa only [d4471, d749, d1590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5597 (p : Pattern) (guard : d4471 p = 1) : d750 p ≤ (0 : Int) + d1593 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d750, d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5596 p hg
    simpa only [d750, d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d750, d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5592 p hg
    simpa only [d750, d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5598 (p : Pattern) (guard : d4471 p = 1) : d161 p ≤ (0 : Int) + d1597 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d161, d1597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5215 p hg
    simpa only [d4471, d161, d1597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d161, d1597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4471, d161, d1597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5599 (p : Pattern) (guard : d4471 p = 1) : d162 p ≤ (0 : Int) + d1598 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d162, d1598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5598 p hg
    simpa only [d162, d1598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d162, d1598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5563 p hg
    simpa only [d162, d1598, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
