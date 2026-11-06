import NetHack.Soko22Hazard87.Compare171
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare43000 (p : Pattern) (guard : d1086 p = 1) : d47629 p ≤ (8 : Int) + d2 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1085 p = 1 := by simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42999 p hg
    simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42994 p hg
    simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43001 (p : Pattern) (guard : d9771 p = 1) : d47629 p ≤ (8 : Int) + d2 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1086 p = 1 := by simpa only [d9771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43000 p hg
    simpa only [d9771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42994 p hg
    simpa only [d9771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43002 (p : Pattern) (guard : d342708 p = 1) : d47629 p ≤ (8 : Int) + d2 p := by
  cases selected : p 223 with
  | false =>
    have hg : d9771 p = 1 := by simpa only [d342708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43001 p hg
    simpa only [d342708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42994 p hg
    simpa only [d342708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43003 (p : Pattern) (guard : d0 p = 1) : d51186 p ≤ (8 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43004 (p : Pattern) (guard : d342709 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 204 with
  | false =>
    have hg : d342708 p = 1 := by simpa only [d342709, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43002 p hg
    simpa only [d342709, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342709, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43003 p hg
    simpa only [d342709, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43005 (p : Pattern) (guard : d0 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43006 (p : Pattern) (guard : d342710 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d342709 p = 1 := by simpa only [d342710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43004 p hg
    simpa only [d342710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43005 p hg
    simpa only [d342710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43007 (p : Pattern) (guard : d342711 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 201 with
  | false =>
    have hg : d342710 p = 1 := by simpa only [d342711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43006 p hg
    simpa only [d342711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43005 p hg
    simpa only [d342711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43008 (p : Pattern) (guard : d0 p = 1) : d51187 p ≤ (8 : Int) + d338664 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43009 (p : Pattern) (guard : d342712 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 182 with
  | false =>
    have hg : d342711 p = 1 := by simpa only [d342712, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43007 p hg
    simpa only [d342712, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342712, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43008 p hg
    simpa only [d342712, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43010 (p : Pattern) (guard : d0 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43011 (p : Pattern) (guard : d342713 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 180 with
  | false =>
    have hg : d342712 p = 1 := by simpa only [d342713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43009 p hg
    simpa only [d342713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43010 p hg
    simpa only [d342713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43012 (p : Pattern) (guard : d342755 p = 1) : d51529 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342755, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42993 p hg
    simpa only [d342755, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342713 p = 1 := by simpa only [d342755, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43011 p hg
    simpa only [d342755, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43013 (p : Pattern) (guard : d342714 p = 1) : d51530 p ≤ (8 : Int) + d338814 p := by
  have ha := bounds51530 p
  have hb := bounds338814 p
  omega
theorem compare43014 (p : Pattern) (guard : d342756 p = 1) : d51531 p ≤ (8 : Int) + d338815 p := by
  cases selected : p 162 with
  | false =>
    have hg : d342755 p = 1 := by simpa only [d342756, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43012 p hg
    simpa only [d342756, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342714 p = 1 := by simpa only [d342756, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43013 p hg
    simpa only [d342756, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43015 (p : Pattern) (guard : d342715 p = 1) : d51291 p ≤ (8 : Int) + d338710 p := by
  have ha := bounds51291 p
  have hb := bounds338710 p
  omega
theorem compare43016 (p : Pattern) (guard : d342757 p = 1) : d51532 p ≤ (8 : Int) + d338816 p := by
  cases selected : p 161 with
  | false =>
    have hg : d342756 p = 1 := by simpa only [d342757, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43014 p hg
    simpa only [d342757, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342715 p = 1 := by simpa only [d342757, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43015 p hg
    simpa only [d342757, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43017 (p : Pattern) (guard : d0 p = 1) : d51535 p ≤ (8 : Int) + d338819 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43018 (p : Pattern) (guard : d342758 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d342757 p = 1 := by simpa only [d342758, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43016 p hg
    simpa only [d342758, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342758, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43017 p hg
    simpa only [d342758, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43019 (p : Pattern) (guard : d0 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43020 (p : Pattern) (guard : d342759 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 159 with
  | false =>
    have hg : d342758 p = 1 := by simpa only [d342759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43018 p hg
    simpa only [d342759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43019 p hg
    simpa only [d342759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43021 (p : Pattern) (guard : d342760 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 158 with
  | false =>
    have hg : d342759 p = 1 := by simpa only [d342760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43020 p hg
    simpa only [d342760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43019 p hg
    simpa only [d342760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43022 (p : Pattern) (guard : d342761 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 157 with
  | false =>
    have hg : d342760 p = 1 := by simpa only [d342761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43021 p hg
    simpa only [d342761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43019 p hg
    simpa only [d342761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43023 (p : Pattern) (guard : d342762 p = 1) : d51537 p ≤ (8 : Int) + d338821 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342762, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42992 p hg
    simpa only [d342762, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342761 p = 1 := by simpa only [d342762, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43022 p hg
    simpa only [d342762, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43024 (p : Pattern) (guard : d342763 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342763, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42991 p hg
    simpa only [d342763, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342762 p = 1 := by simpa only [d342763, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43023 p hg
    simpa only [d342763, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43025 (p : Pattern) (guard : d0 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43026 (p : Pattern) (guard : d342764 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 136 with
  | false =>
    have hg : d342763 p = 1 := by simpa only [d342764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43024 p hg
    simpa only [d342764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43025 p hg
    simpa only [d342764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43027 (p : Pattern) (guard : d342765 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 135 with
  | false =>
    have hg : d342764 p = 1 := by simpa only [d342765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43026 p hg
    simpa only [d342765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43025 p hg
    simpa only [d342765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43028 (p : Pattern) (guard : d342766 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 119 with
  | false =>
    have hg : d342765 p = 1 := by simpa only [d342766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43027 p hg
    simpa only [d342766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43025 p hg
    simpa only [d342766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43029 (p : Pattern) (guard : d0 p = 1) : d51539 p ≤ (8 : Int) + d338823 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43030 (p : Pattern) (guard : d342767 p = 1) : d51540 p ≤ (8 : Int) + d338824 p := by
  cases selected : p 116 with
  | false =>
    have hg : d342766 p = 1 := by simpa only [d342767, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43028 p hg
    simpa only [d342767, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342767, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43029 p hg
    simpa only [d342767, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43031 (p : Pattern) (guard : d342768 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342768, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42898 p hg
    simpa only [d342768, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342767 p = 1 := by simpa only [d342768, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43030 p hg
    simpa only [d342768, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43032 (p : Pattern) (guard : d342769 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 113 with
  | false =>
    have hg : d342768 p = 1 := by simpa only [d342769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43031 p hg
    simpa only [d342769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d342769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43033 (p : Pattern) (guard : d342770 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 96 with
  | false =>
    have hg : d342769 p = 1 := by simpa only [d342770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43032 p hg
    simpa only [d342770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d342770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43034 (p : Pattern) (guard : d342771 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 95 with
  | false =>
    have hg : d342770 p = 1 := by simpa only [d342771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43033 p hg
    simpa only [d342771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d342771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43035 (p : Pattern) (guard : d342772 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 93 with
  | false =>
    have hg : d342771 p = 1 := by simpa only [d342772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43034 p hg
    simpa only [d342772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d342772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43036 (p : Pattern) (guard : d342773 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 91 with
  | false =>
    have hg : d342772 p = 1 := by simpa only [d342773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43035 p hg
    simpa only [d342773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d342773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43037 (p : Pattern) (guard : d342774 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 90 with
  | false =>
    have hg : d342773 p = 1 := by simpa only [d342774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43036 p hg
    simpa only [d342774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d342774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43038 (p : Pattern) (guard : d342775 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 89 with
  | false =>
    have hg : d342774 p = 1 := by simpa only [d342775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43037 p hg
    simpa only [d342775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d342775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43039 (p : Pattern) (guard : d342776 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d342776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342775 p = 1 := by simpa only [d342776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43038 p hg
    simpa only [d342776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43040 (p : Pattern) (guard : d342777 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d342777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342776 p = 1 := by simpa only [d342777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43039 p hg
    simpa only [d342777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43041 (p : Pattern) (guard : d342778 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342778, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342778, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342777 p = 1 := by simpa only [d342778, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43040 p hg
    simpa only [d342778, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43042 (p : Pattern) (guard : d342779 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42989 p hg
    simpa only [d342779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342778 p = 1 := by simpa only [d342779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43041 p hg
    simpa only [d342779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43043 (p : Pattern) (guard : d342780 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  cases selected : p 69 with
  | false =>
    have hg : d342779 p = 1 := by simpa only [d342780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43042 p hg
    simpa only [d342780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42989 p hg
    simpa only [d342780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43044 (p : Pattern) (guard : d342781 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  cases selected : p 51 with
  | false =>
    have hg : d342780 p = 1 := by simpa only [d342781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43043 p hg
    simpa only [d342781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42989 p hg
    simpa only [d342781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43045 (p : Pattern) (guard : d342782 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  cases selected : p 50 with
  | false =>
    have hg : d342781 p = 1 := by simpa only [d342782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43044 p hg
    simpa only [d342782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42989 p hg
    simpa only [d342782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43046 (p : Pattern) (guard : d0 p = 1) : d51633 p ≤ (8 : Int) + d338881 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare43047 (p : Pattern) (guard : d342783 p = 1) : d51634 p ≤ (8 : Int) + d338882 p := by
  cases selected : p 49 with
  | false =>
    have hg : d342782 p = 1 := by simpa only [d342783, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43045 p hg
    simpa only [d342783, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342783, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43046 p hg
    simpa only [d342783, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43048 (p : Pattern) (guard : d342784 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 48 with
  | false =>
    have hg : d342754 p = 1 := by simpa only [d342784, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42988 p hg
    simpa only [d342784, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342783 p = 1 := by simpa only [d342784, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43047 p hg
    simpa only [d342784, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43049 (p : Pattern) (guard : d342785 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d342785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342784 p = 1 := by simpa only [d342785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43048 p hg
    simpa only [d342785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43050 (p : Pattern) (guard : d342786 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d342786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342785 p = 1 := by simpa only [d342786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43049 p hg
    simpa only [d342786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43051 (p : Pattern) (guard : d342787 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d342787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342786 p = 1 := by simpa only [d342787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43050 p hg
    simpa only [d342787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43052 (p : Pattern) (guard : d342788 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d342788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342787 p = 1 := by simpa only [d342788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43051 p hg
    simpa only [d342788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43053 (p : Pattern) (guard : d342789 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d342789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342788 p = 1 := by simpa only [d342789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43052 p hg
    simpa only [d342789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43054 (p : Pattern) (guard : d342790 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342732 p = 1 := by simpa only [d342790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42923 p hg
    simpa only [d342790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43055 (p : Pattern) (guard : d342791 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d342790 p = 1 := by simpa only [d342791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43054 p hg
    simpa only [d342791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43056 (p : Pattern) (guard : d342792 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342791 p = 1 := by simpa only [d342792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43055 p hg
    simpa only [d342792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43057 (p : Pattern) (guard : d342793 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342792 p = 1 := by simpa only [d342793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43056 p hg
    simpa only [d342793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43058 (p : Pattern) (guard : d342794 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342794, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342794, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342793 p = 1 := by simpa only [d342794, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43057 p hg
    simpa only [d342794, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43059 (p : Pattern) (guard : d342795 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42895 p hg
    simpa only [d342795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342794 p = 1 := by simpa only [d342795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43058 p hg
    simpa only [d342795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43060 (p : Pattern) (guard : d342796 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 69 with
  | false =>
    have hg : d342795 p = 1 := by simpa only [d342796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43059 p hg
    simpa only [d342796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42895 p hg
    simpa only [d342796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43061 (p : Pattern) (guard : d342790 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342732 p = 1 := by simpa only [d342790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42935 p hg
    simpa only [d342790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43062 (p : Pattern) (guard : d342791 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d342790 p = 1 := by simpa only [d342791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43061 p hg
    simpa only [d342791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43063 (p : Pattern) (guard : d342792 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342791 p = 1 := by simpa only [d342792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43062 p hg
    simpa only [d342792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43064 (p : Pattern) (guard : d342793 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342792 p = 1 := by simpa only [d342793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43063 p hg
    simpa only [d342793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43065 (p : Pattern) (guard : d342797 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342739 p = 1 := by simpa only [d342797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42941 p hg
    simpa only [d342797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43066 (p : Pattern) (guard : d342798 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d342797 p = 1 := by simpa only [d342798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43065 p hg
    simpa only [d342798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43067 (p : Pattern) (guard : d342799 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342798 p = 1 := by simpa only [d342799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43066 p hg
    simpa only [d342799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43068 (p : Pattern) (guard : d342800 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342799 p = 1 := by simpa only [d342800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43067 p hg
    simpa only [d342800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43069 (p : Pattern) (guard : d342801 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d342793 p = 1 := by simpa only [d342801, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43064 p hg
    simpa only [d342801, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342800 p = 1 := by simpa only [d342801, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43068 p hg
    simpa only [d342801, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43070 (p : Pattern) (guard : d342802 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 70 with
  | false =>
    have hg : d342794 p = 1 := by simpa only [d342802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43058 p hg
    simpa only [d342802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342801 p = 1 := by simpa only [d342802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43069 p hg
    simpa only [d342802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43071 (p : Pattern) (guard : d342803 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 69 with
  | false =>
    have hg : d342802 p = 1 := by simpa only [d342803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43070 p hg
    simpa only [d342803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42895 p hg
    simpa only [d342803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43072 (p : Pattern) (guard : d342804 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 51 with
  | false =>
    have hg : d342796 p = 1 := by simpa only [d342804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43060 p hg
    simpa only [d342804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342803 p = 1 := by simpa only [d342804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43071 p hg
    simpa only [d342804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43073 (p : Pattern) (guard : d342805 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342729 p = 1 := by simpa only [d342805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42920 p hg
    simpa only [d342805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43074 (p : Pattern) (guard : d342806 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342805 p = 1 := by simpa only [d342806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43073 p hg
    simpa only [d342806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43075 (p : Pattern) (guard : d342807 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d342806 p = 1 := by simpa only [d342807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43074 p hg
    simpa only [d342807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43076 (p : Pattern) (guard : d342808 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342807 p = 1 := by simpa only [d342808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43075 p hg
    simpa only [d342808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43077 (p : Pattern) (guard : d342809 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d342808 p = 1 := by simpa only [d342809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43076 p hg
    simpa only [d342809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43078 (p : Pattern) (guard : d342810 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342809 p = 1 := by simpa only [d342810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43077 p hg
    simpa only [d342810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43079 (p : Pattern) (guard : d342811 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342728 p = 1 := by simpa only [d342811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42919 p hg
    simpa only [d342811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43080 (p : Pattern) (guard : d342812 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d342811 p = 1 := by simpa only [d342812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43079 p hg
    simpa only [d342812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43081 (p : Pattern) (guard : d342813 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342812 p = 1 := by simpa only [d342813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43080 p hg
    simpa only [d342813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43082 (p : Pattern) (guard : d342814 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d342813 p = 1 := by simpa only [d342814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43081 p hg
    simpa only [d342814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43083 (p : Pattern) (guard : d342815 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342814 p = 1 := by simpa only [d342815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43082 p hg
    simpa only [d342815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43084 (p : Pattern) (guard : d342816 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d342815 p = 1 := by simpa only [d342816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43083 p hg
    simpa only [d342816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43085 (p : Pattern) (guard : d342826 p = 1) : d51288 p ≤ (8 : Int) + d338690 p := by
  have ha := bounds51288 p
  have hb := bounds338690 p
  omega
theorem compare43086 (p : Pattern) (guard : d342827 p = 1) : d51289 p ≤ (8 : Int) + d338691 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342827, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42901 p hg
    simpa only [d342827, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342826 p = 1 := by simpa only [d342827, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43085 p hg
    simpa only [d342827, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43087 (p : Pattern) (guard : d342828 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 160 with
  | false =>
    have hg : d342827 p = 1 := by simpa only [d342828, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43086 p hg
    simpa only [d342828, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342828, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42904 p hg
    simpa only [d342828, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43088 (p : Pattern) (guard : d342829 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 159 with
  | false =>
    have hg : d342828 p = 1 := by simpa only [d342829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43087 p hg
    simpa only [d342829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342717 p = 1 := by simpa only [d342829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42905 p hg
    simpa only [d342829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43089 (p : Pattern) (guard : d342830 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 158 with
  | false =>
    have hg : d342829 p = 1 := by simpa only [d342830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43088 p hg
    simpa only [d342830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342718 p = 1 := by simpa only [d342830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42907 p hg
    simpa only [d342830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43090 (p : Pattern) (guard : d342831 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 157 with
  | false =>
    have hg : d342830 p = 1 := by simpa only [d342831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43089 p hg
    simpa only [d342831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342719 p = 1 := by simpa only [d342831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42908 p hg
    simpa only [d342831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43091 (p : Pattern) (guard : d342832 p = 1) : d51294 p ≤ (8 : Int) + d338713 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342832, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42900 p hg
    simpa only [d342832, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342831 p = 1 := by simpa only [d342832, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43090 p hg
    simpa only [d342832, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43092 (p : Pattern) (guard : d342833 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342833, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42899 p hg
    simpa only [d342833, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342832 p = 1 := by simpa only [d342833, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43091 p hg
    simpa only [d342833, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43093 (p : Pattern) (guard : d342834 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 136 with
  | false =>
    have hg : d342833 p = 1 := by simpa only [d342834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43092 p hg
    simpa only [d342834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342722 p = 1 := by simpa only [d342834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42911 p hg
    simpa only [d342834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43094 (p : Pattern) (guard : d342835 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 135 with
  | false =>
    have hg : d342834 p = 1 := by simpa only [d342835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43093 p hg
    simpa only [d342835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342723 p = 1 := by simpa only [d342835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42913 p hg
    simpa only [d342835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43095 (p : Pattern) (guard : d342836 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 119 with
  | false =>
    have hg : d342835 p = 1 := by simpa only [d342836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43094 p hg
    simpa only [d342836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42912 p hg
    simpa only [d342836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43096 (p : Pattern) (guard : d342837 p = 1) : d51316 p ≤ (8 : Int) + d338726 p := by
  cases selected : p 116 with
  | false =>
    have hg : d342836 p = 1 := by simpa only [d342837, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43095 p hg
    simpa only [d342837, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342837, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42916 p hg
    simpa only [d342837, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43097 (p : Pattern) (guard : d342838 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342838, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42898 p hg
    simpa only [d342838, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342837 p = 1 := by simpa only [d342838, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43096 p hg
    simpa only [d342838, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43098 (p : Pattern) (guard : d342839 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d342838 p = 1 := by simpa only [d342839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43097 p hg
    simpa only [d342839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342727 p = 1 := by simpa only [d342839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42918 p hg
    simpa only [d342839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43099 (p : Pattern) (guard : d342840 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d342839 p = 1 := by simpa only [d342840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43098 p hg
    simpa only [d342840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43100 (p : Pattern) (guard : d342841 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d342840 p = 1 := by simpa only [d342841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43099 p hg
    simpa only [d342841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43101 (p : Pattern) (guard : d342842 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342841 p = 1 := by simpa only [d342842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43100 p hg
    simpa only [d342842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43102 (p : Pattern) (guard : d342843 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d342842 p = 1 := by simpa only [d342843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43101 p hg
    simpa only [d342843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342731 p = 1 := by simpa only [d342843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42922 p hg
    simpa only [d342843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43103 (p : Pattern) (guard : d342844 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d342843 p = 1 := by simpa only [d342844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43102 p hg
    simpa only [d342844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43104 (p : Pattern) (guard : d342845 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d342844 p = 1 := by simpa only [d342845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43103 p hg
    simpa only [d342845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342733 p = 1 := by simpa only [d342845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42924 p hg
    simpa only [d342845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43105 (p : Pattern) (guard : d342846 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d342816 p = 1 := by simpa only [d342846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43084 p hg
    simpa only [d342846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342845 p = 1 := by simpa only [d342846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43104 p hg
    simpa only [d342846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43106 (p : Pattern) (guard : d342847 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d342810 p = 1 := by simpa only [d342847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43078 p hg
    simpa only [d342847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342846 p = 1 := by simpa only [d342847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43105 p hg
    simpa only [d342847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43107 (p : Pattern) (guard : d342848 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342848, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342848, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342847 p = 1 := by simpa only [d342848, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43106 p hg
    simpa only [d342848, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43108 (p : Pattern) (guard : d342805 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342729 p = 1 := by simpa only [d342805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42932 p hg
    simpa only [d342805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43109 (p : Pattern) (guard : d342806 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342805 p = 1 := by simpa only [d342806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43108 p hg
    simpa only [d342806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43110 (p : Pattern) (guard : d342807 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d342806 p = 1 := by simpa only [d342807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43109 p hg
    simpa only [d342807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43111 (p : Pattern) (guard : d342808 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342807 p = 1 := by simpa only [d342808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43110 p hg
    simpa only [d342808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43112 (p : Pattern) (guard : d342809 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d342808 p = 1 := by simpa only [d342809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43111 p hg
    simpa only [d342809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43113 (p : Pattern) (guard : d342810 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342809 p = 1 := by simpa only [d342810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43112 p hg
    simpa only [d342810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43114 (p : Pattern) (guard : d342811 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342728 p = 1 := by simpa only [d342811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42931 p hg
    simpa only [d342811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43115 (p : Pattern) (guard : d342812 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d342811 p = 1 := by simpa only [d342812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43114 p hg
    simpa only [d342812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43116 (p : Pattern) (guard : d342813 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342812 p = 1 := by simpa only [d342813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43115 p hg
    simpa only [d342813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43117 (p : Pattern) (guard : d342814 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d342813 p = 1 := by simpa only [d342814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43116 p hg
    simpa only [d342814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43118 (p : Pattern) (guard : d342815 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342814 p = 1 := by simpa only [d342815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43117 p hg
    simpa only [d342815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43119 (p : Pattern) (guard : d342816 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d342815 p = 1 := by simpa only [d342816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43118 p hg
    simpa only [d342816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43120 (p : Pattern) (guard : d342838 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342838, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42929 p hg
    simpa only [d342838, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342837 p = 1 := by simpa only [d342838, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43096 p hg
    simpa only [d342838, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43121 (p : Pattern) (guard : d342839 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d342838 p = 1 := by simpa only [d342839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43120 p hg
    simpa only [d342839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342727 p = 1 := by simpa only [d342839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42930 p hg
    simpa only [d342839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43122 (p : Pattern) (guard : d342840 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d342839 p = 1 := by simpa only [d342840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43121 p hg
    simpa only [d342840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43123 (p : Pattern) (guard : d342841 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d342840 p = 1 := by simpa only [d342841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43122 p hg
    simpa only [d342841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43124 (p : Pattern) (guard : d342842 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342841 p = 1 := by simpa only [d342842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43123 p hg
    simpa only [d342842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43125 (p : Pattern) (guard : d342843 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d342842 p = 1 := by simpa only [d342843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43124 p hg
    simpa only [d342843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342731 p = 1 := by simpa only [d342843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42934 p hg
    simpa only [d342843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43126 (p : Pattern) (guard : d342844 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d342843 p = 1 := by simpa only [d342844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43125 p hg
    simpa only [d342844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43127 (p : Pattern) (guard : d342845 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d342844 p = 1 := by simpa only [d342845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43126 p hg
    simpa only [d342845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342733 p = 1 := by simpa only [d342845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42936 p hg
    simpa only [d342845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43128 (p : Pattern) (guard : d342846 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d342816 p = 1 := by simpa only [d342846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43119 p hg
    simpa only [d342846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342845 p = 1 := by simpa only [d342846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43127 p hg
    simpa only [d342846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43129 (p : Pattern) (guard : d342847 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d342810 p = 1 := by simpa only [d342847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43113 p hg
    simpa only [d342847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342846 p = 1 := by simpa only [d342847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43128 p hg
    simpa only [d342847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43130 (p : Pattern) (guard : d342849 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d342805 p = 1 := by simpa only [d342849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43073 p hg
    simpa only [d342849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43131 (p : Pattern) (guard : d342850 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d342849 p = 1 := by simpa only [d342850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43130 p hg
    simpa only [d342850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43132 (p : Pattern) (guard : d342851 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342850 p = 1 := by simpa only [d342851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43131 p hg
    simpa only [d342851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43133 (p : Pattern) (guard : d342852 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d342851 p = 1 := by simpa only [d342852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43132 p hg
    simpa only [d342852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43134 (p : Pattern) (guard : d342853 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342852 p = 1 := by simpa only [d342853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43133 p hg
    simpa only [d342853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43135 (p : Pattern) (guard : d342854 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d342812 p = 1 := by simpa only [d342854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43080 p hg
    simpa only [d342854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43136 (p : Pattern) (guard : d342855 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d342854 p = 1 := by simpa only [d342855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43135 p hg
    simpa only [d342855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43137 (p : Pattern) (guard : d342856 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342855 p = 1 := by simpa only [d342856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43136 p hg
    simpa only [d342856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43138 (p : Pattern) (guard : d342857 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d342856 p = 1 := by simpa only [d342857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43137 p hg
    simpa only [d342857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43139 (p : Pattern) (guard : d342858 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d342841 p = 1 := by simpa only [d342858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43100 p hg
    simpa only [d342858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43140 (p : Pattern) (guard : d342859 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d342858 p = 1 := by simpa only [d342859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43139 p hg
    simpa only [d342859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342738 p = 1 := by simpa only [d342859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42940 p hg
    simpa only [d342859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43141 (p : Pattern) (guard : d342860 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d342859 p = 1 := by simpa only [d342860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43140 p hg
    simpa only [d342860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43142 (p : Pattern) (guard : d342861 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d342860 p = 1 := by simpa only [d342861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43141 p hg
    simpa only [d342861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342740 p = 1 := by simpa only [d342861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42942 p hg
    simpa only [d342861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43143 (p : Pattern) (guard : d342862 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d342857 p = 1 := by simpa only [d342862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43138 p hg
    simpa only [d342862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342861 p = 1 := by simpa only [d342862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43142 p hg
    simpa only [d342862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43144 (p : Pattern) (guard : d342863 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d342853 p = 1 := by simpa only [d342863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43134 p hg
    simpa only [d342863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342862 p = 1 := by simpa only [d342863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43143 p hg
    simpa only [d342863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43145 (p : Pattern) (guard : d342864 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d342847 p = 1 := by simpa only [d342864, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43129 p hg
    simpa only [d342864, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342863 p = 1 := by simpa only [d342864, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43144 p hg
    simpa only [d342864, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43146 (p : Pattern) (guard : d342865 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 70 with
  | false =>
    have hg : d342848 p = 1 := by simpa only [d342865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43107 p hg
    simpa only [d342865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342864 p = 1 := by simpa only [d342865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43145 p hg
    simpa only [d342865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43147 (p : Pattern) (guard : d342866 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d342793 p = 1 := by simpa only [d342866, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43064 p hg
    simpa only [d342866, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342866, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342866, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43148 (p : Pattern) (guard : d342867 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 70 with
  | false =>
    have hg : d342866 p = 1 := by simpa only [d342867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43147 p hg
    simpa only [d342867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42895 p hg
    simpa only [d342867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43149 (p : Pattern) (guard : d342868 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 69 with
  | false =>
    have hg : d342865 p = 1 := by simpa only [d342868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43146 p hg
    simpa only [d342868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342867 p = 1 := by simpa only [d342868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43148 p hg
    simpa only [d342868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43150 (p : Pattern) (guard : d342869 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 51 with
  | false =>
    have hg : d342868 p = 1 := by simpa only [d342869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43149 p hg
    simpa only [d342869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42895 p hg
    simpa only [d342869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43151 (p : Pattern) (guard : d342870 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 50 with
  | false =>
    have hg : d342804 p = 1 := by simpa only [d342870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43072 p hg
    simpa only [d342870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342869 p = 1 := by simpa only [d342870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43150 p hg
    simpa only [d342870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43152 (p : Pattern) (guard : d342826 p = 1) : d51447 p ≤ (8 : Int) + d338755 p := by
  have ha := bounds51447 p
  have hb := bounds338755 p
  omega
theorem compare43153 (p : Pattern) (guard : d342827 p = 1) : d51448 p ≤ (8 : Int) + d338756 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342827, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42956 p hg
    simpa only [d342827, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342826 p = 1 := by simpa only [d342827, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43152 p hg
    simpa only [d342827, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43154 (p : Pattern) (guard : d342828 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d342827 p = 1 := by simpa only [d342828, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43153 p hg
    simpa only [d342828, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342828, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42959 p hg
    simpa only [d342828, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43155 (p : Pattern) (guard : d342829 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 159 with
  | false =>
    have hg : d342828 p = 1 := by simpa only [d342829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43154 p hg
    simpa only [d342829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342717 p = 1 := by simpa only [d342829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42960 p hg
    simpa only [d342829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43156 (p : Pattern) (guard : d342830 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 158 with
  | false =>
    have hg : d342829 p = 1 := by simpa only [d342830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43155 p hg
    simpa only [d342830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342718 p = 1 := by simpa only [d342830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42962 p hg
    simpa only [d342830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43157 (p : Pattern) (guard : d342831 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 157 with
  | false =>
    have hg : d342830 p = 1 := by simpa only [d342831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43156 p hg
    simpa only [d342831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342719 p = 1 := by simpa only [d342831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42963 p hg
    simpa only [d342831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43158 (p : Pattern) (guard : d342832 p = 1) : d51453 p ≤ (8 : Int) + d338775 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342832, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42955 p hg
    simpa only [d342832, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342831 p = 1 := by simpa only [d342832, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43157 p hg
    simpa only [d342832, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43159 (p : Pattern) (guard : d342833 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342833, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42954 p hg
    simpa only [d342833, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342832 p = 1 := by simpa only [d342833, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43158 p hg
    simpa only [d342833, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43160 (p : Pattern) (guard : d342834 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 136 with
  | false =>
    have hg : d342833 p = 1 := by simpa only [d342834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43159 p hg
    simpa only [d342834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342722 p = 1 := by simpa only [d342834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42966 p hg
    simpa only [d342834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43161 (p : Pattern) (guard : d342835 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 135 with
  | false =>
    have hg : d342834 p = 1 := by simpa only [d342835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43160 p hg
    simpa only [d342835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342723 p = 1 := by simpa only [d342835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42968 p hg
    simpa only [d342835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43162 (p : Pattern) (guard : d342836 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 119 with
  | false =>
    have hg : d342835 p = 1 := by simpa only [d342836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43161 p hg
    simpa only [d342836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42967 p hg
    simpa only [d342836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43163 (p : Pattern) (guard : d342837 p = 1) : d51467 p ≤ (8 : Int) + d338784 p := by
  cases selected : p 116 with
  | false =>
    have hg : d342836 p = 1 := by simpa only [d342837, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43162 p hg
    simpa only [d342837, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342837, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42971 p hg
    simpa only [d342837, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43164 (p : Pattern) (guard : d342838 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342838, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42953 p hg
    simpa only [d342838, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342837 p = 1 := by simpa only [d342838, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43163 p hg
    simpa only [d342838, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43165 (p : Pattern) (guard : d342839 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 113 with
  | false =>
    have hg : d342838 p = 1 := by simpa only [d342839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43164 p hg
    simpa only [d342839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342727 p = 1 := by simpa only [d342839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42973 p hg
    simpa only [d342839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43166 (p : Pattern) (guard : d342840 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 96 with
  | false =>
    have hg : d342839 p = 1 := by simpa only [d342840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43165 p hg
    simpa only [d342840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d342840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43167 (p : Pattern) (guard : d342841 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 95 with
  | false =>
    have hg : d342840 p = 1 := by simpa only [d342841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43166 p hg
    simpa only [d342841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d342841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43168 (p : Pattern) (guard : d342858 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 93 with
  | false =>
    have hg : d342841 p = 1 := by simpa only [d342858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43167 p hg
    simpa only [d342858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d342858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43169 (p : Pattern) (guard : d342859 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 91 with
  | false =>
    have hg : d342858 p = 1 := by simpa only [d342859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43168 p hg
    simpa only [d342859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342738 p = 1 := by simpa only [d342859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42977 p hg
    simpa only [d342859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43170 (p : Pattern) (guard : d342860 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 90 with
  | false =>
    have hg : d342859 p = 1 := by simpa only [d342860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43169 p hg
    simpa only [d342860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d342860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43171 (p : Pattern) (guard : d342861 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 89 with
  | false =>
    have hg : d342860 p = 1 := by simpa only [d342861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43170 p hg
    simpa only [d342861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342740 p = 1 := by simpa only [d342861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42979 p hg
    simpa only [d342861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43172 (p : Pattern) (guard : d342871 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d342871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342861 p = 1 := by simpa only [d342871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43171 p hg
    simpa only [d342871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43173 (p : Pattern) (guard : d342872 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d342872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342871 p = 1 := by simpa only [d342872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43172 p hg
    simpa only [d342872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43174 (p : Pattern) (guard : d342873 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342873, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342873, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342872 p = 1 := by simpa only [d342873, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43173 p hg
    simpa only [d342873, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43175 (p : Pattern) (guard : d342874 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42951 p hg
    simpa only [d342874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342873 p = 1 := by simpa only [d342874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43174 p hg
    simpa only [d342874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43176 (p : Pattern) (guard : d342875 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  cases selected : p 69 with
  | false =>
    have hg : d342874 p = 1 := by simpa only [d342875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43175 p hg
    simpa only [d342875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42951 p hg
    simpa only [d342875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43177 (p : Pattern) (guard : d342876 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  cases selected : p 51 with
  | false =>
    have hg : d342875 p = 1 := by simpa only [d342876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43176 p hg
    simpa only [d342876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42951 p hg
    simpa only [d342876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43178 (p : Pattern) (guard : d342877 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  cases selected : p 50 with
  | false =>
    have hg : d342876 p = 1 := by simpa only [d342877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43177 p hg
    simpa only [d342877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42951 p hg
    simpa only [d342877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43179 (p : Pattern) (guard : d342878 p = 1) : d51470 p ≤ (8 : Int) + d338787 p := by
  cases selected : p 49 with
  | false =>
    have hg : d342870 p = 1 := by simpa only [d342878, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43151 p hg
    simpa only [d342878, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342877 p = 1 := by simpa only [d342878, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43178 p hg
    simpa only [d342878, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43180 (p : Pattern) (guard : d127 p = 1) : d2 p ≤ (8 : Int) + d2 p := by
  omega
theorem compare43181 (p : Pattern) (guard : d308 p = 1) : d47629 p ≤ (8 : Int) + d2 p := by
  cases selected : p 247 with
  | false =>
    have hg : d127 p = 1 := by simpa only [d308, d47629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43180 p hg
    simpa only [d308, d47629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d308, d47629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42996 p hg
    simpa only [d308, d47629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43182 (p : Pattern) (guard : d1523 p = 1) : d47629 p ≤ (8 : Int) + d2 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42994 p hg
    simpa only [d1523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d308 p = 1 := by simpa only [d1523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43181 p hg
    simpa only [d1523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43183 (p : Pattern) (guard : d1524 p = 1) : d47629 p ≤ (8 : Int) + d2 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1523 p = 1 := by simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43182 p hg
    simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1084 p = 1 := by simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42998 p hg
    simpa only [d1524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43184 (p : Pattern) (guard : d342817 p = 1) : d47629 p ≤ (8 : Int) + d2 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1524 p = 1 := by simpa only [d342817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43183 p hg
    simpa only [d342817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1085 p = 1 := by simpa only [d342817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42999 p hg
    simpa only [d342817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43185 (p : Pattern) (guard : d342818 p = 1) : d47629 p ≤ (8 : Int) + d2 p := by
  cases selected : p 224 with
  | false =>
    have hg : d342817 p = 1 := by simpa only [d342818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43184 p hg
    simpa only [d342818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1086 p = 1 := by simpa only [d342818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43000 p hg
    simpa only [d342818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43186 (p : Pattern) (guard : d342819 p = 1) : d47629 p ≤ (8 : Int) + d2 p := by
  cases selected : p 223 with
  | false =>
    have hg : d342818 p = 1 := by simpa only [d342819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43185 p hg
    simpa only [d342819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42994 p hg
    simpa only [d342819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43187 (p : Pattern) (guard : d342820 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 204 with
  | false =>
    have hg : d342819 p = 1 := by simpa only [d342820, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43186 p hg
    simpa only [d342820, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342820, d51242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43003 p hg
    simpa only [d342820, d51242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43188 (p : Pattern) (guard : d342821 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d342820 p = 1 := by simpa only [d342821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43187 p hg
    simpa only [d342821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342709 p = 1 := by simpa only [d342821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43004 p hg
    simpa only [d342821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43189 (p : Pattern) (guard : d342822 p = 1) : d51242 p ≤ (8 : Int) + d2 p := by
  cases selected : p 201 with
  | false =>
    have hg : d342821 p = 1 := by simpa only [d342822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43188 p hg
    simpa only [d342822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342710 p = 1 := by simpa only [d342822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43006 p hg
    simpa only [d342822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43190 (p : Pattern) (guard : d342823 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 182 with
  | false =>
    have hg : d342822 p = 1 := by simpa only [d342823, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43189 p hg
    simpa only [d342823, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342823, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43008 p hg
    simpa only [d342823, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43191 (p : Pattern) (guard : d342824 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 180 with
  | false =>
    have hg : d342823 p = 1 := by simpa only [d342824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43190 p hg
    simpa only [d342824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342712 p = 1 := by simpa only [d342824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43009 p hg
    simpa only [d342824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43192 (p : Pattern) (guard : d342879 p = 1) : d51529 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342879, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42993 p hg
    simpa only [d342879, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342824 p = 1 := by simpa only [d342879, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43191 p hg
    simpa only [d342879, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43193 (p : Pattern) (guard : d342825 p = 1) : d51530 p ≤ (8 : Int) + d338814 p := by
  have ha := bounds51530 p
  have hb := bounds338814 p
  omega
theorem compare43194 (p : Pattern) (guard : d342880 p = 1) : d51531 p ≤ (8 : Int) + d338815 p := by
  cases selected : p 162 with
  | false =>
    have hg : d342879 p = 1 := by simpa only [d342880, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43192 p hg
    simpa only [d342880, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342825 p = 1 := by simpa only [d342880, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43193 p hg
    simpa only [d342880, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43195 (p : Pattern) (guard : d342826 p = 1) : d51291 p ≤ (8 : Int) + d338710 p := by
  have ha := bounds51291 p
  have hb := bounds338710 p
  omega
theorem compare43196 (p : Pattern) (guard : d342881 p = 1) : d51532 p ≤ (8 : Int) + d338816 p := by
  cases selected : p 161 with
  | false =>
    have hg : d342880 p = 1 := by simpa only [d342881, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43194 p hg
    simpa only [d342881, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342826 p = 1 := by simpa only [d342881, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43195 p hg
    simpa only [d342881, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43197 (p : Pattern) (guard : d342882 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d342881 p = 1 := by simpa only [d342882, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43196 p hg
    simpa only [d342882, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342882, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43017 p hg
    simpa only [d342882, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43198 (p : Pattern) (guard : d342883 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 159 with
  | false =>
    have hg : d342882 p = 1 := by simpa only [d342883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43197 p hg
    simpa only [d342883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342758 p = 1 := by simpa only [d342883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43018 p hg
    simpa only [d342883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43199 (p : Pattern) (guard : d342884 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 158 with
  | false =>
    have hg : d342883 p = 1 := by simpa only [d342884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43198 p hg
    simpa only [d342884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342759 p = 1 := by simpa only [d342884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43020 p hg
    simpa only [d342884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43200 (p : Pattern) (guard : d342885 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 157 with
  | false =>
    have hg : d342884 p = 1 := by simpa only [d342885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43199 p hg
    simpa only [d342885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342760 p = 1 := by simpa only [d342885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43021 p hg
    simpa only [d342885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43201 (p : Pattern) (guard : d342886 p = 1) : d51537 p ≤ (8 : Int) + d338821 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342886, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42992 p hg
    simpa only [d342886, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342885 p = 1 := by simpa only [d342886, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43200 p hg
    simpa only [d342886, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43202 (p : Pattern) (guard : d342887 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342887, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42991 p hg
    simpa only [d342887, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342886 p = 1 := by simpa only [d342887, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43201 p hg
    simpa only [d342887, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43203 (p : Pattern) (guard : d342888 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 136 with
  | false =>
    have hg : d342887 p = 1 := by simpa only [d342888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43202 p hg
    simpa only [d342888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342763 p = 1 := by simpa only [d342888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43024 p hg
    simpa only [d342888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43204 (p : Pattern) (guard : d342889 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 135 with
  | false =>
    have hg : d342888 p = 1 := by simpa only [d342889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43203 p hg
    simpa only [d342889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342764 p = 1 := by simpa only [d342889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43026 p hg
    simpa only [d342889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43205 (p : Pattern) (guard : d342890 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 119 with
  | false =>
    have hg : d342889 p = 1 := by simpa only [d342890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43204 p hg
    simpa only [d342890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43025 p hg
    simpa only [d342890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43206 (p : Pattern) (guard : d342891 p = 1) : d51540 p ≤ (8 : Int) + d338824 p := by
  cases selected : p 116 with
  | false =>
    have hg : d342890 p = 1 := by simpa only [d342891, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43205 p hg
    simpa only [d342891, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342891, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43029 p hg
    simpa only [d342891, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43207 (p : Pattern) (guard : d342892 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342892, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42898 p hg
    simpa only [d342892, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342891 p = 1 := by simpa only [d342892, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43206 p hg
    simpa only [d342892, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43208 (p : Pattern) (guard : d342893 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 113 with
  | false =>
    have hg : d342892 p = 1 := by simpa only [d342893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43207 p hg
    simpa only [d342893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342768 p = 1 := by simpa only [d342893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43031 p hg
    simpa only [d342893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43209 (p : Pattern) (guard : d342894 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 96 with
  | false =>
    have hg : d342893 p = 1 := by simpa only [d342894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43208 p hg
    simpa only [d342894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d342894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43210 (p : Pattern) (guard : d342895 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 95 with
  | false =>
    have hg : d342894 p = 1 := by simpa only [d342895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43209 p hg
    simpa only [d342895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d342895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43211 (p : Pattern) (guard : d342896 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 93 with
  | false =>
    have hg : d342895 p = 1 := by simpa only [d342896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43210 p hg
    simpa only [d342896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d342896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43212 (p : Pattern) (guard : d342897 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 91 with
  | false =>
    have hg : d342896 p = 1 := by simpa only [d342897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43211 p hg
    simpa only [d342897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342772 p = 1 := by simpa only [d342897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43035 p hg
    simpa only [d342897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43213 (p : Pattern) (guard : d342898 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 90 with
  | false =>
    have hg : d342897 p = 1 := by simpa only [d342898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43212 p hg
    simpa only [d342898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d342898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43214 (p : Pattern) (guard : d342899 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 89 with
  | false =>
    have hg : d342898 p = 1 := by simpa only [d342899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43213 p hg
    simpa only [d342899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342774 p = 1 := by simpa only [d342899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43037 p hg
    simpa only [d342899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43215 (p : Pattern) (guard : d342900 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d342900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342899 p = 1 := by simpa only [d342900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43214 p hg
    simpa only [d342900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43216 (p : Pattern) (guard : d342901 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d342901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342900 p = 1 := by simpa only [d342901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43215 p hg
    simpa only [d342901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43217 (p : Pattern) (guard : d342902 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342902, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342902, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342901 p = 1 := by simpa only [d342902, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43216 p hg
    simpa only [d342902, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43218 (p : Pattern) (guard : d342903 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42989 p hg
    simpa only [d342903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342902 p = 1 := by simpa only [d342903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43217 p hg
    simpa only [d342903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43219 (p : Pattern) (guard : d342904 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  cases selected : p 69 with
  | false =>
    have hg : d342903 p = 1 := by simpa only [d342904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43218 p hg
    simpa only [d342904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42989 p hg
    simpa only [d342904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43220 (p : Pattern) (guard : d342905 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  cases selected : p 51 with
  | false =>
    have hg : d342904 p = 1 := by simpa only [d342905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43219 p hg
    simpa only [d342905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42989 p hg
    simpa only [d342905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43221 (p : Pattern) (guard : d342906 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  cases selected : p 50 with
  | false =>
    have hg : d342905 p = 1 := by simpa only [d342906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43220 p hg
    simpa only [d342906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42989 p hg
    simpa only [d342906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43222 (p : Pattern) (guard : d342907 p = 1) : d51634 p ≤ (8 : Int) + d338882 p := by
  cases selected : p 49 with
  | false =>
    have hg : d342906 p = 1 := by simpa only [d342907, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43221 p hg
    simpa only [d342907, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342907, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43046 p hg
    simpa only [d342907, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43223 (p : Pattern) (guard : d342908 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 48 with
  | false =>
    have hg : d342878 p = 1 := by simpa only [d342908, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43179 p hg
    simpa only [d342908, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342907 p = 1 := by simpa only [d342908, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43222 p hg
    simpa only [d342908, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43224 (p : Pattern) (guard : d342909 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d342909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342908 p = 1 := by simpa only [d342909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43223 p hg
    simpa only [d342909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43225 (p : Pattern) (guard : d342910 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d342910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342909 p = 1 := by simpa only [d342910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43224 p hg
    simpa only [d342910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43226 (p : Pattern) (guard : d342911 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d342911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342910 p = 1 := by simpa only [d342911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43225 p hg
    simpa only [d342911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43227 (p : Pattern) (guard : d342912 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d342912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342911 p = 1 := by simpa only [d342912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43226 p hg
    simpa only [d342912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43228 (p : Pattern) (guard : d342913 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d342913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342912 p = 1 := by simpa only [d342913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43227 p hg
    simpa only [d342913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43229 (p : Pattern) (guard : d342914 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d342789 p = 1 := by simpa only [d342914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43053 p hg
    simpa only [d342914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342913 p = 1 := by simpa only [d342914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43228 p hg
    simpa only [d342914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43230 (p : Pattern) (guard : d342915 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342843 p = 1 := by simpa only [d342915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43102 p hg
    simpa only [d342915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43231 (p : Pattern) (guard : d342916 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d342915 p = 1 := by simpa only [d342916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43230 p hg
    simpa only [d342916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43232 (p : Pattern) (guard : d342917 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342916 p = 1 := by simpa only [d342917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43231 p hg
    simpa only [d342917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43233 (p : Pattern) (guard : d342918 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342917 p = 1 := by simpa only [d342918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43232 p hg
    simpa only [d342918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43234 (p : Pattern) (guard : d342919 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342919, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342919, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342918 p = 1 := by simpa only [d342919, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43233 p hg
    simpa only [d342919, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43235 (p : Pattern) (guard : d342920 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42895 p hg
    simpa only [d342920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342919 p = 1 := by simpa only [d342920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43234 p hg
    simpa only [d342920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43236 (p : Pattern) (guard : d342921 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 69 with
  | false =>
    have hg : d342920 p = 1 := by simpa only [d342921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43235 p hg
    simpa only [d342921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42895 p hg
    simpa only [d342921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43237 (p : Pattern) (guard : d342915 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342843 p = 1 := by simpa only [d342915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43125 p hg
    simpa only [d342915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43238 (p : Pattern) (guard : d342916 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d342915 p = 1 := by simpa only [d342916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43237 p hg
    simpa only [d342916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43239 (p : Pattern) (guard : d342917 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342916 p = 1 := by simpa only [d342917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43238 p hg
    simpa only [d342917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43240 (p : Pattern) (guard : d342918 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342917 p = 1 := by simpa only [d342918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43239 p hg
    simpa only [d342918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43241 (p : Pattern) (guard : d342922 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342859 p = 1 := by simpa only [d342922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43140 p hg
    simpa only [d342922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43242 (p : Pattern) (guard : d342923 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d342922 p = 1 := by simpa only [d342923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43241 p hg
    simpa only [d342923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43243 (p : Pattern) (guard : d342924 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342923 p = 1 := by simpa only [d342924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43242 p hg
    simpa only [d342924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43244 (p : Pattern) (guard : d342925 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342924 p = 1 := by simpa only [d342925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43243 p hg
    simpa only [d342925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43245 (p : Pattern) (guard : d342926 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d342918 p = 1 := by simpa only [d342926, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43240 p hg
    simpa only [d342926, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342925 p = 1 := by simpa only [d342926, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43244 p hg
    simpa only [d342926, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43246 (p : Pattern) (guard : d342927 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 70 with
  | false =>
    have hg : d342919 p = 1 := by simpa only [d342927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43234 p hg
    simpa only [d342927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342926 p = 1 := by simpa only [d342927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43245 p hg
    simpa only [d342927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43247 (p : Pattern) (guard : d342928 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 69 with
  | false =>
    have hg : d342927 p = 1 := by simpa only [d342928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43246 p hg
    simpa only [d342928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42895 p hg
    simpa only [d342928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43248 (p : Pattern) (guard : d342929 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 51 with
  | false =>
    have hg : d342921 p = 1 := by simpa only [d342929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43236 p hg
    simpa only [d342929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342928 p = 1 := by simpa only [d342929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43247 p hg
    simpa only [d342929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43249 (p : Pattern) (guard : d342930 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342840 p = 1 := by simpa only [d342930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43099 p hg
    simpa only [d342930, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
