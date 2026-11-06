import NetHack.Soko22Hazard87.Compare174
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare43750 (p : Pattern) (guard : d366374 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 182 with
  | false =>
    have hg : d366373 p = 1 := by simpa only [d366374, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43749 p hg
    simpa only [d366374, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366374, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43008 p hg
    simpa only [d366374, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43751 (p : Pattern) (guard : d366375 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 180 with
  | false =>
    have hg : d366374 p = 1 := by simpa only [d366375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43750 p hg
    simpa only [d366375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366365 p = 1 := by simpa only [d366375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43739 p hg
    simpa only [d366375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43752 (p : Pattern) (guard : d366451 p = 1) : d51529 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366451, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42993 p hg
    simpa only [d366451, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366375 p = 1 := by simpa only [d366451, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43751 p hg
    simpa only [d366451, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43753 (p : Pattern) (guard : d366376 p = 1) : d51530 p ≤ (8 : Int) + d338814 p := by
  have ha := bounds51530 p
  have hb := bounds338814 p
  omega
theorem compare43754 (p : Pattern) (guard : d366452 p = 1) : d51531 p ≤ (8 : Int) + d338815 p := by
  cases selected : p 162 with
  | false =>
    have hg : d366451 p = 1 := by simpa only [d366452, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43752 p hg
    simpa only [d366452, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366376 p = 1 := by simpa only [d366452, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43753 p hg
    simpa only [d366452, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43755 (p : Pattern) (guard : d366377 p = 1) : d51291 p ≤ (8 : Int) + d338710 p := by
  have ha := bounds51291 p
  have hb := bounds338710 p
  omega
theorem compare43756 (p : Pattern) (guard : d366453 p = 1) : d51532 p ≤ (8 : Int) + d338816 p := by
  cases selected : p 161 with
  | false =>
    have hg : d366452 p = 1 := by simpa only [d366453, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43754 p hg
    simpa only [d366453, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366377 p = 1 := by simpa only [d366453, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43755 p hg
    simpa only [d366453, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43757 (p : Pattern) (guard : d366454 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366453 p = 1 := by simpa only [d366454, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43756 p hg
    simpa only [d366454, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366454, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43017 p hg
    simpa only [d366454, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43758 (p : Pattern) (guard : d366455 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366454 p = 1 := by simpa only [d366455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43757 p hg
    simpa only [d366455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343035 p = 1 := by simpa only [d366455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43417 p hg
    simpa only [d366455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43759 (p : Pattern) (guard : d366456 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366450 p = 1 := by simpa only [d366456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43747 p hg
    simpa only [d366456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366455 p = 1 := by simpa only [d366456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43758 p hg
    simpa only [d366456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43760 (p : Pattern) (guard : d366457 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 157 with
  | false =>
    have hg : d366456 p = 1 := by simpa only [d366457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43759 p hg
    simpa only [d366457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366276 p = 1 := by simpa only [d366457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43419 p hg
    simpa only [d366457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43761 (p : Pattern) (guard : d366458 p = 1) : d51537 p ≤ (8 : Int) + d338821 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366458, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42992 p hg
    simpa only [d366458, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366457 p = 1 := by simpa only [d366458, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43760 p hg
    simpa only [d366458, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43762 (p : Pattern) (guard : d366459 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366459, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42991 p hg
    simpa only [d366459, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366458 p = 1 := by simpa only [d366459, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43761 p hg
    simpa only [d366459, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43763 (p : Pattern) (guard : d343265 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 158 with
  | false =>
    have hg : d343036 p = 1 := by simpa only [d343265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43418 p hg
    simpa only [d343265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342759 p = 1 := by simpa only [d343265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43020 p hg
    simpa only [d343265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43764 (p : Pattern) (guard : d366460 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 157 with
  | false =>
    have hg : d366276 p = 1 := by simpa only [d366460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43419 p hg
    simpa only [d366460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343265 p = 1 := by simpa only [d366460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43763 p hg
    simpa only [d366460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43765 (p : Pattern) (guard : d366461 p = 1) : d51537 p ≤ (8 : Int) + d338821 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366461, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42992 p hg
    simpa only [d366461, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366460 p = 1 := by simpa only [d366461, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43764 p hg
    simpa only [d366461, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43766 (p : Pattern) (guard : d366462 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366462, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42991 p hg
    simpa only [d366462, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366461 p = 1 := by simpa only [d366462, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43765 p hg
    simpa only [d366462, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43767 (p : Pattern) (guard : d366463 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 136 with
  | false =>
    have hg : d366459 p = 1 := by simpa only [d366463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43762 p hg
    simpa only [d366463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366462 p = 1 := by simpa only [d366463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43766 p hg
    simpa only [d366463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43768 (p : Pattern) (guard : d366464 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 135 with
  | false =>
    have hg : d366463 p = 1 := by simpa only [d366464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43767 p hg
    simpa only [d366464, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366280 p = 1 := by simpa only [d366464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43423 p hg
    simpa only [d366464, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43769 (p : Pattern) (guard : d366465 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 119 with
  | false =>
    have hg : d366464 p = 1 := by simpa only [d366465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43768 p hg
    simpa only [d366465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43025 p hg
    simpa only [d366465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43770 (p : Pattern) (guard : d366466 p = 1) : d51540 p ≤ (8 : Int) + d338824 p := by
  cases selected : p 116 with
  | false =>
    have hg : d366465 p = 1 := by simpa only [d366466, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43769 p hg
    simpa only [d366466, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366466, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43029 p hg
    simpa only [d366466, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43771 (p : Pattern) (guard : d366467 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366467, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42898 p hg
    simpa only [d366467, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366466 p = 1 := by simpa only [d366467, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43770 p hg
    simpa only [d366467, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43772 (p : Pattern) (guard : d343274 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 136 with
  | false =>
    have hg : d342887 p = 1 := by simpa only [d343274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43202 p hg
    simpa only [d343274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43025 p hg
    simpa only [d343274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43773 (p : Pattern) (guard : d366468 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 135 with
  | false =>
    have hg : d366280 p = 1 := by simpa only [d366468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43423 p hg
    simpa only [d366468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343274 p = 1 := by simpa only [d366468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43772 p hg
    simpa only [d366468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43774 (p : Pattern) (guard : d366469 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 119 with
  | false =>
    have hg : d366468 p = 1 := by simpa only [d366469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43773 p hg
    simpa only [d366469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43025 p hg
    simpa only [d366469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43775 (p : Pattern) (guard : d366470 p = 1) : d51540 p ≤ (8 : Int) + d338824 p := by
  cases selected : p 116 with
  | false =>
    have hg : d366469 p = 1 := by simpa only [d366470, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43774 p hg
    simpa only [d366470, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366470, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43029 p hg
    simpa only [d366470, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43776 (p : Pattern) (guard : d366471 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366471, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42898 p hg
    simpa only [d366471, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366470 p = 1 := by simpa only [d366471, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43775 p hg
    simpa only [d366471, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43777 (p : Pattern) (guard : d366472 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366467 p = 1 := by simpa only [d366472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43771 p hg
    simpa only [d366472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366471 p = 1 := by simpa only [d366472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43776 p hg
    simpa only [d366472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43778 (p : Pattern) (guard : d366473 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366472 p = 1 := by simpa only [d366473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43777 p hg
    simpa only [d366473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d366473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43779 (p : Pattern) (guard : d366474 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366473 p = 1 := by simpa only [d366474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43778 p hg
    simpa only [d366474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d366474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43780 (p : Pattern) (guard : d366475 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366474 p = 1 := by simpa only [d366475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43779 p hg
    simpa only [d366475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d366475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43781 (p : Pattern) (guard : d343283 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 135 with
  | false =>
    have hg : d343274 p = 1 := by simpa only [d343283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43772 p hg
    simpa only [d343283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43025 p hg
    simpa only [d343283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43782 (p : Pattern) (guard : d343284 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 119 with
  | false =>
    have hg : d343283 p = 1 := by simpa only [d343284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43781 p hg
    simpa only [d343284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43025 p hg
    simpa only [d343284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43783 (p : Pattern) (guard : d343285 p = 1) : d51540 p ≤ (8 : Int) + d338824 p := by
  cases selected : p 116 with
  | false =>
    have hg : d343284 p = 1 := by simpa only [d343285, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43782 p hg
    simpa only [d343285, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343285, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43029 p hg
    simpa only [d343285, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43784 (p : Pattern) (guard : d343286 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343286, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42898 p hg
    simpa only [d343286, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343285 p = 1 := by simpa only [d343286, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43783 p hg
    simpa only [d343286, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43785 (p : Pattern) (guard : d366476 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366471 p = 1 := by simpa only [d366476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43776 p hg
    simpa only [d366476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343286 p = 1 := by simpa only [d366476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43784 p hg
    simpa only [d366476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43786 (p : Pattern) (guard : d366477 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366476 p = 1 := by simpa only [d366477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43785 p hg
    simpa only [d366477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d366477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43787 (p : Pattern) (guard : d366478 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366477 p = 1 := by simpa only [d366478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43786 p hg
    simpa only [d366478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d366478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43788 (p : Pattern) (guard : d366479 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366478 p = 1 := by simpa only [d366479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43787 p hg
    simpa only [d366479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d366479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43789 (p : Pattern) (guard : d366480 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366475 p = 1 := by simpa only [d366480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43780 p hg
    simpa only [d366480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366479 p = 1 := by simpa only [d366480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43788 p hg
    simpa only [d366480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43790 (p : Pattern) (guard : d366481 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 90 with
  | false =>
    have hg : d366480 p = 1 := by simpa only [d366481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43789 p hg
    simpa only [d366481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d366481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43791 (p : Pattern) (guard : d366482 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366471 p = 1 := by simpa only [d366482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43776 p hg
    simpa only [d366482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d366482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43792 (p : Pattern) (guard : d366483 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366482 p = 1 := by simpa only [d366483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43791 p hg
    simpa only [d366483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d366483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43793 (p : Pattern) (guard : d366484 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366483 p = 1 := by simpa only [d366484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43792 p hg
    simpa only [d366484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d366484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43794 (p : Pattern) (guard : d366485 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366484 p = 1 := by simpa only [d366485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43793 p hg
    simpa only [d366485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d366485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43795 (p : Pattern) (guard : d366486 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366485 p = 1 := by simpa only [d366486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43794 p hg
    simpa only [d366486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d366486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43796 (p : Pattern) (guard : d366487 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 90 with
  | false =>
    have hg : d366486 p = 1 := by simpa only [d366487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43795 p hg
    simpa only [d366487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d366487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43797 (p : Pattern) (guard : d366488 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366481 p = 1 := by simpa only [d366488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43790 p hg
    simpa only [d366488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366487 p = 1 := by simpa only [d366488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43796 p hg
    simpa only [d366488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43798 (p : Pattern) (guard : d366489 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d366489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366488 p = 1 := by simpa only [d366489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43797 p hg
    simpa only [d366489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43799 (p : Pattern) (guard : d366490 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d366490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366489 p = 1 := by simpa only [d366490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43798 p hg
    simpa only [d366490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43800 (p : Pattern) (guard : d366491 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366491, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366491, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366490 p = 1 := by simpa only [d366491, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43799 p hg
    simpa only [d366491, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43801 (p : Pattern) (guard : d366492 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42989 p hg
    simpa only [d366492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366491 p = 1 := by simpa only [d366492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43800 p hg
    simpa only [d366492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43802 (p : Pattern) (guard : d343304 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 113 with
  | false =>
    have hg : d343286 p = 1 := by simpa only [d343304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43784 p hg
    simpa only [d343304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d343304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43803 (p : Pattern) (guard : d343305 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 96 with
  | false =>
    have hg : d343304 p = 1 := by simpa only [d343305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43802 p hg
    simpa only [d343305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d343305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43804 (p : Pattern) (guard : d343306 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 95 with
  | false =>
    have hg : d343305 p = 1 := by simpa only [d343306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43803 p hg
    simpa only [d343306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d343306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43805 (p : Pattern) (guard : d343307 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 93 with
  | false =>
    have hg : d343306 p = 1 := by simpa only [d343307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43804 p hg
    simpa only [d343307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d343307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43806 (p : Pattern) (guard : d343308 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 91 with
  | false =>
    have hg : d343307 p = 1 := by simpa only [d343308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43805 p hg
    simpa only [d343308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d343308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43807 (p : Pattern) (guard : d343309 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d343309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343308 p = 1 := by simpa only [d343309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43806 p hg
    simpa only [d343309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43808 (p : Pattern) (guard : d343310 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 89 with
  | false =>
    have hg : d343309 p = 1 := by simpa only [d343310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43807 p hg
    simpa only [d343310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d343310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43809 (p : Pattern) (guard : d343311 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d343311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343310 p = 1 := by simpa only [d343311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43808 p hg
    simpa only [d343311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43810 (p : Pattern) (guard : d343312 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d343312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343311 p = 1 := by simpa only [d343312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43809 p hg
    simpa only [d343312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43811 (p : Pattern) (guard : d343313 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343313, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d343313, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343312 p = 1 := by simpa only [d343313, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43810 p hg
    simpa only [d343313, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43812 (p : Pattern) (guard : d343314 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d343314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42989 p hg
    simpa only [d343314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343313 p = 1 := by simpa only [d343314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43811 p hg
    simpa only [d343314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43813 (p : Pattern) (guard : d366493 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  cases selected : p 69 with
  | false =>
    have hg : d366492 p = 1 := by simpa only [d366493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43801 p hg
    simpa only [d366493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343314 p = 1 := by simpa only [d366493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43812 p hg
    simpa only [d366493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43814 (p : Pattern) (guard : d366494 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  cases selected : p 51 with
  | false =>
    have hg : d366493 p = 1 := by simpa only [d366494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43813 p hg
    simpa only [d366494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42989 p hg
    simpa only [d366494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43815 (p : Pattern) (guard : d366495 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  cases selected : p 50 with
  | false =>
    have hg : d366494 p = 1 := by simpa only [d366495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43814 p hg
    simpa only [d366495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42989 p hg
    simpa only [d366495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43816 (p : Pattern) (guard : d366496 p = 1) : d51634 p ≤ (8 : Int) + d338882 p := by
  cases selected : p 49 with
  | false =>
    have hg : d366495 p = 1 := by simpa only [d366496, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43815 p hg
    simpa only [d366496, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366496, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43046 p hg
    simpa only [d366496, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43817 (p : Pattern) (guard : d366497 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 48 with
  | false =>
    have hg : d366441 p = 1 := by simpa only [d366497, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43715 p hg
    simpa only [d366497, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366496 p = 1 := by simpa only [d366497, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43816 p hg
    simpa only [d366497, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43818 (p : Pattern) (guard : d366498 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d366498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366497 p = 1 := by simpa only [d366498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43817 p hg
    simpa only [d366498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43819 (p : Pattern) (guard : d366499 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d366499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366498 p = 1 := by simpa only [d366499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43818 p hg
    simpa only [d366499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43820 (p : Pattern) (guard : d366500 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d366500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366499 p = 1 := by simpa only [d366500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43819 p hg
    simpa only [d366500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43821 (p : Pattern) (guard : d366501 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d366501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366500 p = 1 := by simpa only [d366501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43820 p hg
    simpa only [d366501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43822 (p : Pattern) (guard : d366502 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d366502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366501 p = 1 := by simpa only [d366502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43821 p hg
    simpa only [d366502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43823 (p : Pattern) (guard : d366503 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d366503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366502 p = 1 := by simpa only [d366503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43822 p hg
    simpa only [d366503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43824 (p : Pattern) (guard : d366504 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d366504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366503 p = 1 := by simpa only [d366504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43823 p hg
    simpa only [d366504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43825 (p : Pattern) (guard : d366505 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d366307 p = 1 := by simpa only [d366505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43462 p hg
    simpa only [d366505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366504 p = 1 := by simpa only [d366505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43824 p hg
    simpa only [d366505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43826 (p : Pattern) (guard : d366518 p = 1) : d51288 p ≤ (8 : Int) + d338690 p := by
  have ha := bounds51288 p
  have hb := bounds338690 p
  omega
theorem compare43827 (p : Pattern) (guard : d366519 p = 1) : d51289 p ≤ (8 : Int) + d338691 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366519, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42901 p hg
    simpa only [d366519, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366518 p = 1 := by simpa only [d366519, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43826 p hg
    simpa only [d366519, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43828 (p : Pattern) (guard : d366520 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366519 p = 1 := by simpa only [d366520, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43827 p hg
    simpa only [d366520, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366520, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42904 p hg
    simpa only [d366520, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43829 (p : Pattern) (guard : d366530 p = 1) : d51288 p ≤ (8 : Int) + d338690 p := by
  have ha := bounds51288 p
  have hb := bounds338690 p
  omega
theorem compare43830 (p : Pattern) (guard : d366531 p = 1) : d51289 p ≤ (8 : Int) + d338691 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366531, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42901 p hg
    simpa only [d366531, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366530 p = 1 := by simpa only [d366531, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43829 p hg
    simpa only [d366531, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43831 (p : Pattern) (guard : d366532 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366531 p = 1 := by simpa only [d366532, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43830 p hg
    simpa only [d366532, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366532, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42904 p hg
    simpa only [d366532, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43832 (p : Pattern) (guard : d366533 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366520 p = 1 := by simpa only [d366533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43828 p hg
    simpa only [d366533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366532 p = 1 := by simpa only [d366533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43831 p hg
    simpa only [d366533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43833 (p : Pattern) (guard : d366539 p = 1) : d51288 p ≤ (8 : Int) + d338690 p := by
  have ha := bounds51288 p
  have hb := bounds338690 p
  omega
theorem compare43834 (p : Pattern) (guard : d366540 p = 1) : d51289 p ≤ (8 : Int) + d338691 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366540, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42901 p hg
    simpa only [d366540, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366539 p = 1 := by simpa only [d366540, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43833 p hg
    simpa only [d366540, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43835 (p : Pattern) (guard : d366541 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366540 p = 1 := by simpa only [d366541, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43834 p hg
    simpa only [d366541, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366541, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42904 p hg
    simpa only [d366541, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43836 (p : Pattern) (guard : d366547 p = 1) : d51288 p ≤ (8 : Int) + d338690 p := by
  have ha := bounds51288 p
  have hb := bounds338690 p
  omega
theorem compare43837 (p : Pattern) (guard : d366548 p = 1) : d51289 p ≤ (8 : Int) + d338691 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366548, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42901 p hg
    simpa only [d366548, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366547 p = 1 := by simpa only [d366548, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43836 p hg
    simpa only [d366548, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43838 (p : Pattern) (guard : d366549 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366548 p = 1 := by simpa only [d366549, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43837 p hg
    simpa only [d366549, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366549, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42904 p hg
    simpa only [d366549, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43839 (p : Pattern) (guard : d366550 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366541 p = 1 := by simpa only [d366550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43835 p hg
    simpa only [d366550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366549 p = 1 := by simpa only [d366550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43838 p hg
    simpa only [d366550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43840 (p : Pattern) (guard : d366551 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366533 p = 1 := by simpa only [d366551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43832 p hg
    simpa only [d366551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366550 p = 1 := by simpa only [d366551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43839 p hg
    simpa only [d366551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43841 (p : Pattern) (guard : d366554 p = 1) : d51288 p ≤ (8 : Int) + d338690 p := by
  have ha := bounds51288 p
  have hb := bounds338690 p
  omega
theorem compare43842 (p : Pattern) (guard : d366555 p = 1) : d51289 p ≤ (8 : Int) + d338691 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366555, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42901 p hg
    simpa only [d366555, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366554 p = 1 := by simpa only [d366555, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43841 p hg
    simpa only [d366555, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43843 (p : Pattern) (guard : d366556 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366555 p = 1 := by simpa only [d366556, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43842 p hg
    simpa only [d366556, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366556, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42904 p hg
    simpa only [d366556, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43844 (p : Pattern) (guard : d366557 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366556 p = 1 := by simpa only [d366557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43843 p hg
    simpa only [d366557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366549 p = 1 := by simpa only [d366557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43838 p hg
    simpa only [d366557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43845 (p : Pattern) (guard : d366558 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366549 p = 1 := by simpa only [d366558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43838 p hg
    simpa only [d366558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42906 p hg
    simpa only [d366558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43846 (p : Pattern) (guard : d366559 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366557 p = 1 := by simpa only [d366559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43844 p hg
    simpa only [d366559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366558 p = 1 := by simpa only [d366559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43845 p hg
    simpa only [d366559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43847 (p : Pattern) (guard : d366560 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 157 with
  | false =>
    have hg : d366551 p = 1 := by simpa only [d366560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43840 p hg
    simpa only [d366560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366559 p = 1 := by simpa only [d366560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43846 p hg
    simpa only [d366560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43848 (p : Pattern) (guard : d366561 p = 1) : d51294 p ≤ (8 : Int) + d338713 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366561, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42900 p hg
    simpa only [d366561, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366560 p = 1 := by simpa only [d366561, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43847 p hg
    simpa only [d366561, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43849 (p : Pattern) (guard : d366562 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366562, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42899 p hg
    simpa only [d366562, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366561 p = 1 := by simpa only [d366562, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43848 p hg
    simpa only [d366562, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43850 (p : Pattern) (guard : d366563 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366558 p = 1 := by simpa only [d366563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43845 p hg
    simpa only [d366563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42906 p hg
    simpa only [d366563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43851 (p : Pattern) (guard : d366564 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 157 with
  | false =>
    have hg : d366559 p = 1 := by simpa only [d366564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43846 p hg
    simpa only [d366564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366563 p = 1 := by simpa only [d366564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43850 p hg
    simpa only [d366564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43852 (p : Pattern) (guard : d366565 p = 1) : d51294 p ≤ (8 : Int) + d338713 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366565, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42900 p hg
    simpa only [d366565, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366564 p = 1 := by simpa only [d366565, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43851 p hg
    simpa only [d366565, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43853 (p : Pattern) (guard : d366566 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366566, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42899 p hg
    simpa only [d366566, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366565 p = 1 := by simpa only [d366566, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43852 p hg
    simpa only [d366566, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43854 (p : Pattern) (guard : d366567 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 136 with
  | false =>
    have hg : d366562 p = 1 := by simpa only [d366567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43849 p hg
    simpa only [d366567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366566 p = 1 := by simpa only [d366567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43853 p hg
    simpa only [d366567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43855 (p : Pattern) (guard : d366568 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 136 with
  | false =>
    have hg : d366566 p = 1 := by simpa only [d366568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43853 p hg
    simpa only [d366568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42912 p hg
    simpa only [d366568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43856 (p : Pattern) (guard : d366569 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 135 with
  | false =>
    have hg : d366567 p = 1 := by simpa only [d366569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43854 p hg
    simpa only [d366569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366568 p = 1 := by simpa only [d366569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43855 p hg
    simpa only [d366569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43857 (p : Pattern) (guard : d366570 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 119 with
  | false =>
    have hg : d366569 p = 1 := by simpa only [d366570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43856 p hg
    simpa only [d366570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42912 p hg
    simpa only [d366570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43858 (p : Pattern) (guard : d366571 p = 1) : d51316 p ≤ (8 : Int) + d338726 p := by
  cases selected : p 116 with
  | false =>
    have hg : d366570 p = 1 := by simpa only [d366571, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43857 p hg
    simpa only [d366571, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366571, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42916 p hg
    simpa only [d366571, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43859 (p : Pattern) (guard : d366572 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366572, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42898 p hg
    simpa only [d366572, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366571 p = 1 := by simpa only [d366572, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43858 p hg
    simpa only [d366572, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43860 (p : Pattern) (guard : d366573 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 135 with
  | false =>
    have hg : d366568 p = 1 := by simpa only [d366573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43855 p hg
    simpa only [d366573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42912 p hg
    simpa only [d366573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43861 (p : Pattern) (guard : d366574 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 119 with
  | false =>
    have hg : d366573 p = 1 := by simpa only [d366574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43860 p hg
    simpa only [d366574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42912 p hg
    simpa only [d366574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43862 (p : Pattern) (guard : d366575 p = 1) : d51316 p ≤ (8 : Int) + d338726 p := by
  cases selected : p 116 with
  | false =>
    have hg : d366574 p = 1 := by simpa only [d366575, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43861 p hg
    simpa only [d366575, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366575, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42916 p hg
    simpa only [d366575, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43863 (p : Pattern) (guard : d366576 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366576, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42898 p hg
    simpa only [d366576, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366575 p = 1 := by simpa only [d366576, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43862 p hg
    simpa only [d366576, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43864 (p : Pattern) (guard : d366577 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366572 p = 1 := by simpa only [d366577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43859 p hg
    simpa only [d366577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366576 p = 1 := by simpa only [d366577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43863 p hg
    simpa only [d366577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43865 (p : Pattern) (guard : d366578 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366577 p = 1 := by simpa only [d366578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43864 p hg
    simpa only [d366578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43866 (p : Pattern) (guard : d366579 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366578 p = 1 := by simpa only [d366579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43865 p hg
    simpa only [d366579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43867 (p : Pattern) (guard : d366580 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366579 p = 1 := by simpa only [d366580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43866 p hg
    simpa only [d366580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43868 (p : Pattern) (guard : d366581 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366576 p = 1 := by simpa only [d366581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43863 p hg
    simpa only [d366581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43869 (p : Pattern) (guard : d366582 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366581 p = 1 := by simpa only [d366582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43868 p hg
    simpa only [d366582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43870 (p : Pattern) (guard : d366583 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366582 p = 1 := by simpa only [d366583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43869 p hg
    simpa only [d366583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43871 (p : Pattern) (guard : d366584 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366583 p = 1 := by simpa only [d366584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43870 p hg
    simpa only [d366584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43872 (p : Pattern) (guard : d366585 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366580 p = 1 := by simpa only [d366585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43867 p hg
    simpa only [d366585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366584 p = 1 := by simpa only [d366585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43871 p hg
    simpa only [d366585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43873 (p : Pattern) (guard : d366586 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366585 p = 1 := by simpa only [d366586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43872 p hg
    simpa only [d366586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43874 (p : Pattern) (guard : d366587 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366586 p = 1 := by simpa only [d366587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43873 p hg
    simpa only [d366587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43875 (p : Pattern) (guard : d366588 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366587 p = 1 := by simpa only [d366588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43874 p hg
    simpa only [d366588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43876 (p : Pattern) (guard : d366589 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366588 p = 1 := by simpa only [d366589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43875 p hg
    simpa only [d366589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43877 (p : Pattern) (guard : d366590 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366590, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366590, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366589 p = 1 := by simpa only [d366590, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43876 p hg
    simpa only [d366590, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43878 (p : Pattern) (guard : d366591 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42895 p hg
    simpa only [d366591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366590 p = 1 := by simpa only [d366591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43877 p hg
    simpa only [d366591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43879 (p : Pattern) (guard : d366592 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 69 with
  | false =>
    have hg : d366591 p = 1 := by simpa only [d366592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43878 p hg
    simpa only [d366592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42895 p hg
    simpa only [d366592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43880 (p : Pattern) (guard : d366572 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366572, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42929 p hg
    simpa only [d366572, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366571 p = 1 := by simpa only [d366572, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43858 p hg
    simpa only [d366572, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43881 (p : Pattern) (guard : d366576 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366576, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42929 p hg
    simpa only [d366576, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366575 p = 1 := by simpa only [d366576, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43862 p hg
    simpa only [d366576, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43882 (p : Pattern) (guard : d366577 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366572 p = 1 := by simpa only [d366577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43880 p hg
    simpa only [d366577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366576 p = 1 := by simpa only [d366577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43881 p hg
    simpa only [d366577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43883 (p : Pattern) (guard : d366578 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366577 p = 1 := by simpa only [d366578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43882 p hg
    simpa only [d366578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43884 (p : Pattern) (guard : d366579 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366578 p = 1 := by simpa only [d366579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43883 p hg
    simpa only [d366579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43885 (p : Pattern) (guard : d366580 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366579 p = 1 := by simpa only [d366580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43884 p hg
    simpa only [d366580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43886 (p : Pattern) (guard : d366581 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366576 p = 1 := by simpa only [d366581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43881 p hg
    simpa only [d366581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43887 (p : Pattern) (guard : d366582 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366581 p = 1 := by simpa only [d366582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43886 p hg
    simpa only [d366582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43888 (p : Pattern) (guard : d366583 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366582 p = 1 := by simpa only [d366583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43887 p hg
    simpa only [d366583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43889 (p : Pattern) (guard : d366584 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366583 p = 1 := by simpa only [d366584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43888 p hg
    simpa only [d366584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43890 (p : Pattern) (guard : d366585 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366580 p = 1 := by simpa only [d366585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43885 p hg
    simpa only [d366585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366584 p = 1 := by simpa only [d366585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43889 p hg
    simpa only [d366585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43891 (p : Pattern) (guard : d366586 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366585 p = 1 := by simpa only [d366586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43890 p hg
    simpa only [d366586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43892 (p : Pattern) (guard : d366587 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366586 p = 1 := by simpa only [d366587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43891 p hg
    simpa only [d366587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43893 (p : Pattern) (guard : d366588 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366587 p = 1 := by simpa only [d366588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43892 p hg
    simpa only [d366588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43894 (p : Pattern) (guard : d366589 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366588 p = 1 := by simpa only [d366589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43893 p hg
    simpa only [d366589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43895 (p : Pattern) (guard : d366593 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366579 p = 1 := by simpa only [d366593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43866 p hg
    simpa only [d366593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43896 (p : Pattern) (guard : d366594 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366583 p = 1 := by simpa only [d366594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43870 p hg
    simpa only [d366594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43897 (p : Pattern) (guard : d366595 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366593 p = 1 := by simpa only [d366595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43895 p hg
    simpa only [d366595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366594 p = 1 := by simpa only [d366595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43896 p hg
    simpa only [d366595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43898 (p : Pattern) (guard : d366596 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366595 p = 1 := by simpa only [d366596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43897 p hg
    simpa only [d366596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43899 (p : Pattern) (guard : d366597 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366596 p = 1 := by simpa only [d366597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43898 p hg
    simpa only [d366597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43900 (p : Pattern) (guard : d366598 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366597 p = 1 := by simpa only [d366598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43899 p hg
    simpa only [d366598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43901 (p : Pattern) (guard : d366599 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366598 p = 1 := by simpa only [d366599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43900 p hg
    simpa only [d366599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43902 (p : Pattern) (guard : d366600 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d366589 p = 1 := by simpa only [d366600, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43894 p hg
    simpa only [d366600, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366599 p = 1 := by simpa only [d366600, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43901 p hg
    simpa only [d366600, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43903 (p : Pattern) (guard : d366601 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 70 with
  | false =>
    have hg : d366590 p = 1 := by simpa only [d366601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43877 p hg
    simpa only [d366601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366600 p = 1 := by simpa only [d366601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43902 p hg
    simpa only [d366601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43904 (p : Pattern) (guard : d366602 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 69 with
  | false =>
    have hg : d366601 p = 1 := by simpa only [d366602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43903 p hg
    simpa only [d366602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42895 p hg
    simpa only [d366602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43905 (p : Pattern) (guard : d366603 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 51 with
  | false =>
    have hg : d366592 p = 1 := by simpa only [d366603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43879 p hg
    simpa only [d366603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366602 p = 1 := by simpa only [d366603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43904 p hg
    simpa only [d366603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43906 (p : Pattern) (guard : d366604 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366578 p = 1 := by simpa only [d366604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43865 p hg
    simpa only [d366604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43907 (p : Pattern) (guard : d366605 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366604 p = 1 := by simpa only [d366605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43906 p hg
    simpa only [d366605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43908 (p : Pattern) (guard : d366606 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366582 p = 1 := by simpa only [d366606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43869 p hg
    simpa only [d366606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43909 (p : Pattern) (guard : d366607 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366606 p = 1 := by simpa only [d366607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43908 p hg
    simpa only [d366607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43910 (p : Pattern) (guard : d366608 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366605 p = 1 := by simpa only [d366608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43907 p hg
    simpa only [d366608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366607 p = 1 := by simpa only [d366608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43909 p hg
    simpa only [d366608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43911 (p : Pattern) (guard : d366609 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366608 p = 1 := by simpa only [d366609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43910 p hg
    simpa only [d366609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43912 (p : Pattern) (guard : d366610 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366609 p = 1 := by simpa only [d366610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43911 p hg
    simpa only [d366610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43913 (p : Pattern) (guard : d366611 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366610 p = 1 := by simpa only [d366611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43912 p hg
    simpa only [d366611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43914 (p : Pattern) (guard : d366612 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366577 p = 1 := by simpa only [d366612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43864 p hg
    simpa only [d366612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43915 (p : Pattern) (guard : d366613 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366612 p = 1 := by simpa only [d366613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43914 p hg
    simpa only [d366613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43916 (p : Pattern) (guard : d366614 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366613 p = 1 := by simpa only [d366614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43915 p hg
    simpa only [d366614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43917 (p : Pattern) (guard : d366615 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366581 p = 1 := by simpa only [d366615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43868 p hg
    simpa only [d366615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43918 (p : Pattern) (guard : d366616 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366615 p = 1 := by simpa only [d366616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43917 p hg
    simpa only [d366616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43919 (p : Pattern) (guard : d366617 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366616 p = 1 := by simpa only [d366617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43918 p hg
    simpa only [d366617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43920 (p : Pattern) (guard : d366618 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366614 p = 1 := by simpa only [d366618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43916 p hg
    simpa only [d366618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366617 p = 1 := by simpa only [d366618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43919 p hg
    simpa only [d366618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43921 (p : Pattern) (guard : d366619 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366618 p = 1 := by simpa only [d366619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43920 p hg
    simpa only [d366619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43922 (p : Pattern) (guard : d366620 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366619 p = 1 := by simpa only [d366620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43921 p hg
    simpa only [d366620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43923 (p : Pattern) (guard : d366626 p = 1) : d51288 p ≤ (8 : Int) + d338690 p := by
  have ha := bounds51288 p
  have hb := bounds338690 p
  omega
theorem compare43924 (p : Pattern) (guard : d366627 p = 1) : d51289 p ≤ (8 : Int) + d338691 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366627, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42901 p hg
    simpa only [d366627, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366626 p = 1 := by simpa only [d366627, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43923 p hg
    simpa only [d366627, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43925 (p : Pattern) (guard : d366628 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366627 p = 1 := by simpa only [d366628, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43924 p hg
    simpa only [d366628, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366628, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42904 p hg
    simpa only [d366628, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43926 (p : Pattern) (guard : d366634 p = 1) : d51288 p ≤ (8 : Int) + d338690 p := by
  have ha := bounds51288 p
  have hb := bounds338690 p
  omega
theorem compare43927 (p : Pattern) (guard : d366635 p = 1) : d51289 p ≤ (8 : Int) + d338691 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366635, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42901 p hg
    simpa only [d366635, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366634 p = 1 := by simpa only [d366635, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43926 p hg
    simpa only [d366635, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43928 (p : Pattern) (guard : d366636 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366635 p = 1 := by simpa only [d366636, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43927 p hg
    simpa only [d366636, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366636, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42904 p hg
    simpa only [d366636, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43929 (p : Pattern) (guard : d366637 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366628 p = 1 := by simpa only [d366637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43925 p hg
    simpa only [d366637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366636 p = 1 := by simpa only [d366637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43928 p hg
    simpa only [d366637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43930 (p : Pattern) (guard : d366643 p = 1) : d51288 p ≤ (8 : Int) + d338690 p := by
  have ha := bounds51288 p
  have hb := bounds338690 p
  omega
theorem compare43931 (p : Pattern) (guard : d366644 p = 1) : d51289 p ≤ (8 : Int) + d338691 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366644, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42901 p hg
    simpa only [d366644, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366643 p = 1 := by simpa only [d366644, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43930 p hg
    simpa only [d366644, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43932 (p : Pattern) (guard : d366645 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366644 p = 1 := by simpa only [d366645, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43931 p hg
    simpa only [d366645, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366645, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42904 p hg
    simpa only [d366645, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43933 (p : Pattern) (guard : d366646 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366645 p = 1 := by simpa only [d366646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43932 p hg
    simpa only [d366646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366541 p = 1 := by simpa only [d366646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43835 p hg
    simpa only [d366646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43934 (p : Pattern) (guard : d366647 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366637 p = 1 := by simpa only [d366647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43929 p hg
    simpa only [d366647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366646 p = 1 := by simpa only [d366647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43933 p hg
    simpa only [d366647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43935 (p : Pattern) (guard : d366648 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 157 with
  | false =>
    have hg : d366647 p = 1 := by simpa only [d366648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43934 p hg
    simpa only [d366648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366551 p = 1 := by simpa only [d366648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43840 p hg
    simpa only [d366648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43936 (p : Pattern) (guard : d366649 p = 1) : d51294 p ≤ (8 : Int) + d338713 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366649, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42900 p hg
    simpa only [d366649, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366648 p = 1 := by simpa only [d366649, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43935 p hg
    simpa only [d366649, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43937 (p : Pattern) (guard : d366650 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366650, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42899 p hg
    simpa only [d366650, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366649 p = 1 := by simpa only [d366650, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43936 p hg
    simpa only [d366650, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43938 (p : Pattern) (guard : d366656 p = 1) : d51288 p ≤ (8 : Int) + d338690 p := by
  have ha := bounds51288 p
  have hb := bounds338690 p
  omega
theorem compare43939 (p : Pattern) (guard : d366657 p = 1) : d51289 p ≤ (8 : Int) + d338691 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366657, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42901 p hg
    simpa only [d366657, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366656 p = 1 := by simpa only [d366657, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43938 p hg
    simpa only [d366657, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43940 (p : Pattern) (guard : d366658 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366657 p = 1 := by simpa only [d366658, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43939 p hg
    simpa only [d366658, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366658, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42904 p hg
    simpa only [d366658, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43941 (p : Pattern) (guard : d366659 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366658 p = 1 := by simpa only [d366659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43940 p hg
    simpa only [d366659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366549 p = 1 := by simpa only [d366659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43838 p hg
    simpa only [d366659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43942 (p : Pattern) (guard : d366660 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366659 p = 1 := by simpa only [d366660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43941 p hg
    simpa only [d366660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366558 p = 1 := by simpa only [d366660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43845 p hg
    simpa only [d366660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43943 (p : Pattern) (guard : d366661 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 157 with
  | false =>
    have hg : d366551 p = 1 := by simpa only [d366661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43840 p hg
    simpa only [d366661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366660 p = 1 := by simpa only [d366661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43942 p hg
    simpa only [d366661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43944 (p : Pattern) (guard : d366662 p = 1) : d51294 p ≤ (8 : Int) + d338713 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366662, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42900 p hg
    simpa only [d366662, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366661 p = 1 := by simpa only [d366662, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43943 p hg
    simpa only [d366662, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43945 (p : Pattern) (guard : d366663 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366663, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42899 p hg
    simpa only [d366663, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366662 p = 1 := by simpa only [d366663, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43944 p hg
    simpa only [d366663, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43946 (p : Pattern) (guard : d366664 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 136 with
  | false =>
    have hg : d366650 p = 1 := by simpa only [d366664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43937 p hg
    simpa only [d366664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366663 p = 1 := by simpa only [d366664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43945 p hg
    simpa only [d366664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43947 (p : Pattern) (guard : d366665 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 135 with
  | false =>
    have hg : d366664 p = 1 := by simpa only [d366665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43946 p hg
    simpa only [d366665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366567 p = 1 := by simpa only [d366665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43854 p hg
    simpa only [d366665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43948 (p : Pattern) (guard : d366666 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 119 with
  | false =>
    have hg : d366665 p = 1 := by simpa only [d366666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43947 p hg
    simpa only [d366666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42912 p hg
    simpa only [d366666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43949 (p : Pattern) (guard : d366667 p = 1) : d51316 p ≤ (8 : Int) + d338726 p := by
  cases selected : p 116 with
  | false =>
    have hg : d366666 p = 1 := by simpa only [d366667, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43948 p hg
    simpa only [d366667, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366667, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42916 p hg
    simpa only [d366667, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43950 (p : Pattern) (guard : d366668 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366668, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42898 p hg
    simpa only [d366668, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366667 p = 1 := by simpa only [d366668, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43949 p hg
    simpa only [d366668, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43951 (p : Pattern) (guard : d366669 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366668 p = 1 := by simpa only [d366669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43950 p hg
    simpa only [d366669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366572 p = 1 := by simpa only [d366669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43859 p hg
    simpa only [d366669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43952 (p : Pattern) (guard : d366670 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366669 p = 1 := by simpa only [d366670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43951 p hg
    simpa only [d366670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43953 (p : Pattern) (guard : d366671 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366670 p = 1 := by simpa only [d366671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43952 p hg
    simpa only [d366671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43954 (p : Pattern) (guard : d366672 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366671 p = 1 := by simpa only [d366672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43953 p hg
    simpa only [d366672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43955 (p : Pattern) (guard : d366673 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366672 p = 1 := by simpa only [d366673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43954 p hg
    simpa only [d366673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366580 p = 1 := by simpa only [d366673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43867 p hg
    simpa only [d366673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43956 (p : Pattern) (guard : d366674 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d366673 p = 1 := by simpa only [d366674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43955 p hg
    simpa only [d366674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43957 (p : Pattern) (guard : d366675 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366572 p = 1 := by simpa only [d366675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43859 p hg
    simpa only [d366675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43958 (p : Pattern) (guard : d366676 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366675 p = 1 := by simpa only [d366676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43957 p hg
    simpa only [d366676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43959 (p : Pattern) (guard : d366677 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366676 p = 1 := by simpa only [d366677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43958 p hg
    simpa only [d366677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43960 (p : Pattern) (guard : d366678 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366677 p = 1 := by simpa only [d366678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43959 p hg
    simpa only [d366678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43961 (p : Pattern) (guard : d366679 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366678 p = 1 := by simpa only [d366679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43960 p hg
    simpa only [d366679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43962 (p : Pattern) (guard : d366680 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d366679 p = 1 := by simpa only [d366680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43961 p hg
    simpa only [d366680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43963 (p : Pattern) (guard : d366681 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366674 p = 1 := by simpa only [d366681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43956 p hg
    simpa only [d366681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366680 p = 1 := by simpa only [d366681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43962 p hg
    simpa only [d366681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43964 (p : Pattern) (guard : d366682 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d366620 p = 1 := by simpa only [d366682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43922 p hg
    simpa only [d366682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366681 p = 1 := by simpa only [d366682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43963 p hg
    simpa only [d366682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43965 (p : Pattern) (guard : d366683 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d366611 p = 1 := by simpa only [d366683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43913 p hg
    simpa only [d366683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366682 p = 1 := by simpa only [d366683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43964 p hg
    simpa only [d366683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43966 (p : Pattern) (guard : d366684 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366684, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366684, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366683 p = 1 := by simpa only [d366684, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43965 p hg
    simpa only [d366684, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43967 (p : Pattern) (guard : d366604 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366578 p = 1 := by simpa only [d366604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43883 p hg
    simpa only [d366604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43968 (p : Pattern) (guard : d366605 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366604 p = 1 := by simpa only [d366605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43967 p hg
    simpa only [d366605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43969 (p : Pattern) (guard : d366606 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366582 p = 1 := by simpa only [d366606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43887 p hg
    simpa only [d366606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43970 (p : Pattern) (guard : d366607 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366606 p = 1 := by simpa only [d366607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43969 p hg
    simpa only [d366607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43971 (p : Pattern) (guard : d366608 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366605 p = 1 := by simpa only [d366608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43968 p hg
    simpa only [d366608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366607 p = 1 := by simpa only [d366608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43970 p hg
    simpa only [d366608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43972 (p : Pattern) (guard : d366609 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366608 p = 1 := by simpa only [d366609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43971 p hg
    simpa only [d366609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43973 (p : Pattern) (guard : d366610 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366609 p = 1 := by simpa only [d366610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43972 p hg
    simpa only [d366610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43974 (p : Pattern) (guard : d366611 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366610 p = 1 := by simpa only [d366611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43973 p hg
    simpa only [d366611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43975 (p : Pattern) (guard : d366612 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366577 p = 1 := by simpa only [d366612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43882 p hg
    simpa only [d366612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43976 (p : Pattern) (guard : d366613 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366612 p = 1 := by simpa only [d366613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43975 p hg
    simpa only [d366613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43977 (p : Pattern) (guard : d366614 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366613 p = 1 := by simpa only [d366614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43976 p hg
    simpa only [d366614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43978 (p : Pattern) (guard : d366615 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366581 p = 1 := by simpa only [d366615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43886 p hg
    simpa only [d366615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43979 (p : Pattern) (guard : d366616 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366615 p = 1 := by simpa only [d366616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43978 p hg
    simpa only [d366616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43980 (p : Pattern) (guard : d366617 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366616 p = 1 := by simpa only [d366617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43979 p hg
    simpa only [d366617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43981 (p : Pattern) (guard : d366618 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366614 p = 1 := by simpa only [d366618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43977 p hg
    simpa only [d366618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366617 p = 1 := by simpa only [d366618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43980 p hg
    simpa only [d366618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43982 (p : Pattern) (guard : d366619 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366618 p = 1 := by simpa only [d366619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43981 p hg
    simpa only [d366619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43983 (p : Pattern) (guard : d366620 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366619 p = 1 := by simpa only [d366620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43982 p hg
    simpa only [d366620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43984 (p : Pattern) (guard : d366668 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366668, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42929 p hg
    simpa only [d366668, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366667 p = 1 := by simpa only [d366668, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43949 p hg
    simpa only [d366668, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43985 (p : Pattern) (guard : d366669 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366668 p = 1 := by simpa only [d366669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43984 p hg
    simpa only [d366669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366572 p = 1 := by simpa only [d366669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43880 p hg
    simpa only [d366669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43986 (p : Pattern) (guard : d366670 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366669 p = 1 := by simpa only [d366670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43985 p hg
    simpa only [d366670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43987 (p : Pattern) (guard : d366671 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366670 p = 1 := by simpa only [d366671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43986 p hg
    simpa only [d366671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43988 (p : Pattern) (guard : d366672 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366671 p = 1 := by simpa only [d366672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43987 p hg
    simpa only [d366672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43989 (p : Pattern) (guard : d366673 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366672 p = 1 := by simpa only [d366673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43988 p hg
    simpa only [d366673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366580 p = 1 := by simpa only [d366673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43885 p hg
    simpa only [d366673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43990 (p : Pattern) (guard : d366674 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d366673 p = 1 := by simpa only [d366674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43989 p hg
    simpa only [d366674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43991 (p : Pattern) (guard : d366675 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366572 p = 1 := by simpa only [d366675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43880 p hg
    simpa only [d366675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43992 (p : Pattern) (guard : d366676 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366675 p = 1 := by simpa only [d366676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43991 p hg
    simpa only [d366676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43993 (p : Pattern) (guard : d366677 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366676 p = 1 := by simpa only [d366677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43992 p hg
    simpa only [d366677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43994 (p : Pattern) (guard : d366678 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366677 p = 1 := by simpa only [d366678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43993 p hg
    simpa only [d366678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43995 (p : Pattern) (guard : d366679 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366678 p = 1 := by simpa only [d366679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43994 p hg
    simpa only [d366679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43996 (p : Pattern) (guard : d366680 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d366679 p = 1 := by simpa only [d366680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43995 p hg
    simpa only [d366680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43997 (p : Pattern) (guard : d366681 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366674 p = 1 := by simpa only [d366681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43990 p hg
    simpa only [d366681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366680 p = 1 := by simpa only [d366681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43996 p hg
    simpa only [d366681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43998 (p : Pattern) (guard : d366682 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d366620 p = 1 := by simpa only [d366682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43983 p hg
    simpa only [d366682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366681 p = 1 := by simpa only [d366682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43997 p hg
    simpa only [d366682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43999 (p : Pattern) (guard : d366683 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d366611 p = 1 := by simpa only [d366683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43974 p hg
    simpa only [d366683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366682 p = 1 := by simpa only [d366683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43998 p hg
    simpa only [d366683, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
