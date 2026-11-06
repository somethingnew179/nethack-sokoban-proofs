import NetHack.Soko22Hazard87.Compare176
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare44250 (p : Pattern) (guard : d366655 p = 1) : d51530 p ≤ (8 : Int) + d338814 p := by
  have ha := bounds51530 p
  have hb := bounds338814 p
  omega
theorem compare44251 (p : Pattern) (guard : d366771 p = 1) : d51531 p ≤ (8 : Int) + d338815 p := by
  cases selected : p 162 with
  | false =>
    have hg : d366770 p = 1 := by simpa only [d366771, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44249 p hg
    simpa only [d366771, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366655 p = 1 := by simpa only [d366771, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44250 p hg
    simpa only [d366771, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44252 (p : Pattern) (guard : d366656 p = 1) : d51291 p ≤ (8 : Int) + d338710 p := by
  have ha := bounds51291 p
  have hb := bounds338710 p
  omega
theorem compare44253 (p : Pattern) (guard : d366772 p = 1) : d51532 p ≤ (8 : Int) + d338816 p := by
  cases selected : p 161 with
  | false =>
    have hg : d366771 p = 1 := by simpa only [d366772, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44251 p hg
    simpa only [d366772, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366656 p = 1 := by simpa only [d366772, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44252 p hg
    simpa only [d366772, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44254 (p : Pattern) (guard : d366773 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366772 p = 1 := by simpa only [d366773, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44253 p hg
    simpa only [d366773, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366773, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43017 p hg
    simpa only [d366773, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44255 (p : Pattern) (guard : d366774 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366773 p = 1 := by simpa only [d366774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44254 p hg
    simpa only [d366774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366764 p = 1 := by simpa only [d366774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44239 p hg
    simpa only [d366774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44256 (p : Pattern) (guard : d366775 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366764 p = 1 := by simpa only [d366775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44239 p hg
    simpa only [d366775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43019 p hg
    simpa only [d366775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44257 (p : Pattern) (guard : d366776 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366774 p = 1 := by simpa only [d366776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44255 p hg
    simpa only [d366776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366775 p = 1 := by simpa only [d366776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44256 p hg
    simpa only [d366776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44258 (p : Pattern) (guard : d366777 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 157 with
  | false =>
    have hg : d366766 p = 1 := by simpa only [d366777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44241 p hg
    simpa only [d366777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366776 p = 1 := by simpa only [d366777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44257 p hg
    simpa only [d366777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44259 (p : Pattern) (guard : d366778 p = 1) : d51537 p ≤ (8 : Int) + d338821 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366778, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42992 p hg
    simpa only [d366778, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366777 p = 1 := by simpa only [d366778, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44258 p hg
    simpa only [d366778, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44260 (p : Pattern) (guard : d366779 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366779, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42991 p hg
    simpa only [d366779, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366778 p = 1 := by simpa only [d366779, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44259 p hg
    simpa only [d366779, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44261 (p : Pattern) (guard : d366780 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 136 with
  | false =>
    have hg : d366769 p = 1 := by simpa only [d366780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44244 p hg
    simpa only [d366780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366779 p = 1 := by simpa only [d366780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44260 p hg
    simpa only [d366780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44262 (p : Pattern) (guard : d366552 p = 1) : d51277 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 180 with
  | false =>
    have hg : d366522 p = 1 := by simpa only [d366552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44221 p hg
    simpa only [d366552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366544 p = 1 := by simpa only [d366552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44232 p hg
    simpa only [d366552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44263 (p : Pattern) (guard : d366781 p = 1) : d51529 p ≤ (8 : Int) + d338681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366781, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42993 p hg
    simpa only [d366781, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366552 p = 1 := by simpa only [d366781, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44262 p hg
    simpa only [d366781, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44264 (p : Pattern) (guard : d366553 p = 1) : d51530 p ≤ (8 : Int) + d338814 p := by
  have ha := bounds51530 p
  have hb := bounds338814 p
  omega
theorem compare44265 (p : Pattern) (guard : d366782 p = 1) : d51531 p ≤ (8 : Int) + d338815 p := by
  cases selected : p 162 with
  | false =>
    have hg : d366781 p = 1 := by simpa only [d366782, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44263 p hg
    simpa only [d366782, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366553 p = 1 := by simpa only [d366782, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44264 p hg
    simpa only [d366782, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44266 (p : Pattern) (guard : d366554 p = 1) : d51291 p ≤ (8 : Int) + d338710 p := by
  have ha := bounds51291 p
  have hb := bounds338710 p
  omega
theorem compare44267 (p : Pattern) (guard : d366783 p = 1) : d51532 p ≤ (8 : Int) + d338816 p := by
  cases selected : p 161 with
  | false =>
    have hg : d366782 p = 1 := by simpa only [d366783, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44265 p hg
    simpa only [d366783, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366554 p = 1 := by simpa only [d366783, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44266 p hg
    simpa only [d366783, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44268 (p : Pattern) (guard : d366784 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366783 p = 1 := by simpa only [d366784, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44267 p hg
    simpa only [d366784, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366784, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43017 p hg
    simpa only [d366784, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44269 (p : Pattern) (guard : d366785 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366784 p = 1 := by simpa only [d366785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44268 p hg
    simpa only [d366785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366764 p = 1 := by simpa only [d366785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44239 p hg
    simpa only [d366785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44270 (p : Pattern) (guard : d366786 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366785 p = 1 := by simpa only [d366786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44269 p hg
    simpa only [d366786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366775 p = 1 := by simpa only [d366786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44256 p hg
    simpa only [d366786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44271 (p : Pattern) (guard : d366787 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 157 with
  | false =>
    have hg : d366766 p = 1 := by simpa only [d366787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44241 p hg
    simpa only [d366787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366786 p = 1 := by simpa only [d366787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44270 p hg
    simpa only [d366787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44272 (p : Pattern) (guard : d366788 p = 1) : d51537 p ≤ (8 : Int) + d338821 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366788, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42992 p hg
    simpa only [d366788, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366787 p = 1 := by simpa only [d366788, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44271 p hg
    simpa only [d366788, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44273 (p : Pattern) (guard : d366789 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366789, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42991 p hg
    simpa only [d366789, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366788 p = 1 := by simpa only [d366789, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44272 p hg
    simpa only [d366789, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44274 (p : Pattern) (guard : d366790 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366775 p = 1 := by simpa only [d366790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44256 p hg
    simpa only [d366790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43019 p hg
    simpa only [d366790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44275 (p : Pattern) (guard : d366791 p = 1) : d51536 p ≤ (8 : Int) + d338820 p := by
  cases selected : p 157 with
  | false =>
    have hg : d366786 p = 1 := by simpa only [d366791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44270 p hg
    simpa only [d366791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366790 p = 1 := by simpa only [d366791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44274 p hg
    simpa only [d366791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44276 (p : Pattern) (guard : d366792 p = 1) : d51537 p ≤ (8 : Int) + d338821 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366792, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42992 p hg
    simpa only [d366792, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366791 p = 1 := by simpa only [d366792, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44275 p hg
    simpa only [d366792, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44277 (p : Pattern) (guard : d366793 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366793, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42991 p hg
    simpa only [d366793, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366792 p = 1 := by simpa only [d366793, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44276 p hg
    simpa only [d366793, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44278 (p : Pattern) (guard : d366794 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 136 with
  | false =>
    have hg : d366789 p = 1 := by simpa only [d366794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44273 p hg
    simpa only [d366794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366793 p = 1 := by simpa only [d366794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44277 p hg
    simpa only [d366794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44279 (p : Pattern) (guard : d366795 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 135 with
  | false =>
    have hg : d366780 p = 1 := by simpa only [d366795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44261 p hg
    simpa only [d366795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366794 p = 1 := by simpa only [d366795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44278 p hg
    simpa only [d366795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44280 (p : Pattern) (guard : d366796 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 119 with
  | false =>
    have hg : d366795 p = 1 := by simpa only [d366796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44279 p hg
    simpa only [d366796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43025 p hg
    simpa only [d366796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44281 (p : Pattern) (guard : d366797 p = 1) : d51540 p ≤ (8 : Int) + d338824 p := by
  cases selected : p 116 with
  | false =>
    have hg : d366796 p = 1 := by simpa only [d366797, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44280 p hg
    simpa only [d366797, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366797, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43029 p hg
    simpa only [d366797, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44282 (p : Pattern) (guard : d366798 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366798, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42898 p hg
    simpa only [d366798, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366797 p = 1 := by simpa only [d366798, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44281 p hg
    simpa only [d366798, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44283 (p : Pattern) (guard : d366799 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 136 with
  | false =>
    have hg : d366793 p = 1 := by simpa only [d366799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44277 p hg
    simpa only [d366799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43025 p hg
    simpa only [d366799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44284 (p : Pattern) (guard : d366800 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 135 with
  | false =>
    have hg : d366794 p = 1 := by simpa only [d366800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44278 p hg
    simpa only [d366800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366799 p = 1 := by simpa only [d366800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44283 p hg
    simpa only [d366800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44285 (p : Pattern) (guard : d366801 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 119 with
  | false =>
    have hg : d366800 p = 1 := by simpa only [d366801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44284 p hg
    simpa only [d366801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43025 p hg
    simpa only [d366801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44286 (p : Pattern) (guard : d366802 p = 1) : d51540 p ≤ (8 : Int) + d338824 p := by
  cases selected : p 116 with
  | false =>
    have hg : d366801 p = 1 := by simpa only [d366802, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44285 p hg
    simpa only [d366802, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366802, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43029 p hg
    simpa only [d366802, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44287 (p : Pattern) (guard : d366803 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366803, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42898 p hg
    simpa only [d366803, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366802 p = 1 := by simpa only [d366803, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44286 p hg
    simpa only [d366803, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44288 (p : Pattern) (guard : d366804 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366798 p = 1 := by simpa only [d366804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44282 p hg
    simpa only [d366804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366803 p = 1 := by simpa only [d366804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44287 p hg
    simpa only [d366804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44289 (p : Pattern) (guard : d366805 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366804 p = 1 := by simpa only [d366805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44288 p hg
    simpa only [d366805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d366805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44290 (p : Pattern) (guard : d366806 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366805 p = 1 := by simpa only [d366806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44289 p hg
    simpa only [d366806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d366806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44291 (p : Pattern) (guard : d366807 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366806 p = 1 := by simpa only [d366807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44290 p hg
    simpa only [d366807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d366807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44292 (p : Pattern) (guard : d366808 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 135 with
  | false =>
    have hg : d366799 p = 1 := by simpa only [d366808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44283 p hg
    simpa only [d366808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43025 p hg
    simpa only [d366808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44293 (p : Pattern) (guard : d366809 p = 1) : d51538 p ≤ (8 : Int) + d338822 p := by
  cases selected : p 119 with
  | false =>
    have hg : d366808 p = 1 := by simpa only [d366809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44292 p hg
    simpa only [d366809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43025 p hg
    simpa only [d366809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44294 (p : Pattern) (guard : d366810 p = 1) : d51540 p ≤ (8 : Int) + d338824 p := by
  cases selected : p 116 with
  | false =>
    have hg : d366809 p = 1 := by simpa only [d366810, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44293 p hg
    simpa only [d366810, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366810, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43029 p hg
    simpa only [d366810, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44295 (p : Pattern) (guard : d366811 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366811, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42898 p hg
    simpa only [d366811, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366810 p = 1 := by simpa only [d366811, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44294 p hg
    simpa only [d366811, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44296 (p : Pattern) (guard : d366812 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366803 p = 1 := by simpa only [d366812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44287 p hg
    simpa only [d366812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366811 p = 1 := by simpa only [d366812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44295 p hg
    simpa only [d366812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44297 (p : Pattern) (guard : d366813 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366812 p = 1 := by simpa only [d366813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44296 p hg
    simpa only [d366813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d366813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44298 (p : Pattern) (guard : d366814 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366813 p = 1 := by simpa only [d366814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44297 p hg
    simpa only [d366814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d366814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44299 (p : Pattern) (guard : d366815 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366814 p = 1 := by simpa only [d366815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44298 p hg
    simpa only [d366815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d366815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44300 (p : Pattern) (guard : d366816 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366807 p = 1 := by simpa only [d366816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44291 p hg
    simpa only [d366816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366815 p = 1 := by simpa only [d366816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44299 p hg
    simpa only [d366816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44301 (p : Pattern) (guard : d366817 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 90 with
  | false =>
    have hg : d366816 p = 1 := by simpa only [d366817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44300 p hg
    simpa only [d366817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d366817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44302 (p : Pattern) (guard : d366818 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366803 p = 1 := by simpa only [d366818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44287 p hg
    simpa only [d366818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d366818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44303 (p : Pattern) (guard : d366819 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366818 p = 1 := by simpa only [d366819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44302 p hg
    simpa only [d366819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d366819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44304 (p : Pattern) (guard : d366820 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366819 p = 1 := by simpa only [d366820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44303 p hg
    simpa only [d366820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d366820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44305 (p : Pattern) (guard : d366821 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366820 p = 1 := by simpa only [d366821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44304 p hg
    simpa only [d366821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d366821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44306 (p : Pattern) (guard : d366822 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366821 p = 1 := by simpa only [d366822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44305 p hg
    simpa only [d366822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d366822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44307 (p : Pattern) (guard : d366823 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 90 with
  | false =>
    have hg : d366822 p = 1 := by simpa only [d366823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44306 p hg
    simpa only [d366823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d366823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44308 (p : Pattern) (guard : d366824 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366817 p = 1 := by simpa only [d366824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44301 p hg
    simpa only [d366824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366823 p = 1 := by simpa only [d366824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44307 p hg
    simpa only [d366824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44309 (p : Pattern) (guard : d366825 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d366825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366824 p = 1 := by simpa only [d366825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44308 p hg
    simpa only [d366825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44310 (p : Pattern) (guard : d366826 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d366826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366825 p = 1 := by simpa only [d366826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44309 p hg
    simpa only [d366826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44311 (p : Pattern) (guard : d366827 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366827, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366827, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366826 p = 1 := by simpa only [d366827, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44310 p hg
    simpa only [d366827, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44312 (p : Pattern) (guard : d366828 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42989 p hg
    simpa only [d366828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366827 p = 1 := by simpa only [d366828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44311 p hg
    simpa only [d366828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44313 (p : Pattern) (guard : d366829 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366811 p = 1 := by simpa only [d366829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44295 p hg
    simpa only [d366829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d366829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44314 (p : Pattern) (guard : d366830 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366829 p = 1 := by simpa only [d366830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44313 p hg
    simpa only [d366830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d366830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44315 (p : Pattern) (guard : d366831 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366830 p = 1 := by simpa only [d366831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44314 p hg
    simpa only [d366831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d366831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44316 (p : Pattern) (guard : d366832 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366831 p = 1 := by simpa only [d366832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44315 p hg
    simpa only [d366832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d366832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44317 (p : Pattern) (guard : d366833 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366832 p = 1 := by simpa only [d366833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44316 p hg
    simpa only [d366833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d366833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44318 (p : Pattern) (guard : d366834 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d366834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366833 p = 1 := by simpa only [d366834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44317 p hg
    simpa only [d366834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44319 (p : Pattern) (guard : d366835 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366834 p = 1 := by simpa only [d366835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44318 p hg
    simpa only [d366835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d366835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44320 (p : Pattern) (guard : d366836 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d366836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366835 p = 1 := by simpa only [d366836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44319 p hg
    simpa only [d366836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44321 (p : Pattern) (guard : d366837 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42990 p hg
    simpa only [d366837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366836 p = 1 := by simpa only [d366837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44320 p hg
    simpa only [d366837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44322 (p : Pattern) (guard : d366838 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366838, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366838, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366837 p = 1 := by simpa only [d366838, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44321 p hg
    simpa only [d366838, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44323 (p : Pattern) (guard : d366839 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42989 p hg
    simpa only [d366839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366838 p = 1 := by simpa only [d366839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44322 p hg
    simpa only [d366839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44324 (p : Pattern) (guard : d366840 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  cases selected : p 69 with
  | false =>
    have hg : d366828 p = 1 := by simpa only [d366840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44312 p hg
    simpa only [d366840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366839 p = 1 := by simpa only [d366840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44323 p hg
    simpa only [d366840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44325 (p : Pattern) (guard : d366841 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  cases selected : p 51 with
  | false =>
    have hg : d366840 p = 1 := by simpa only [d366841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44324 p hg
    simpa only [d366841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42989 p hg
    simpa only [d366841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44326 (p : Pattern) (guard : d366842 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  cases selected : p 50 with
  | false =>
    have hg : d366841 p = 1 := by simpa only [d366842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44325 p hg
    simpa only [d366842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42989 p hg
    simpa only [d366842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44327 (p : Pattern) (guard : d366843 p = 1) : d51634 p ≤ (8 : Int) + d338882 p := by
  cases selected : p 49 with
  | false =>
    have hg : d366842 p = 1 := by simpa only [d366843, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44326 p hg
    simpa only [d366843, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366843, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43046 p hg
    simpa only [d366843, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44328 (p : Pattern) (guard : d366844 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 48 with
  | false =>
    have hg : d366732 p = 1 := by simpa only [d366844, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44144 p hg
    simpa only [d366844, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366843 p = 1 := by simpa only [d366844, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44327 p hg
    simpa only [d366844, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44329 (p : Pattern) (guard : d366845 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d366845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366844 p = 1 := by simpa only [d366845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44328 p hg
    simpa only [d366845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44330 (p : Pattern) (guard : d366846 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d366846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366845 p = 1 := by simpa only [d366846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44329 p hg
    simpa only [d366846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44331 (p : Pattern) (guard : d366847 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d366847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366846 p = 1 := by simpa only [d366847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44330 p hg
    simpa only [d366847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44332 (p : Pattern) (guard : d366848 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d366848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366847 p = 1 := by simpa only [d366848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44331 p hg
    simpa only [d366848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44333 (p : Pattern) (guard : d366849 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d366849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366848 p = 1 := by simpa only [d366849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44332 p hg
    simpa only [d366849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44334 (p : Pattern) (guard : d366850 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d366850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366849 p = 1 := by simpa only [d366850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44333 p hg
    simpa only [d366850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44335 (p : Pattern) (guard : d366851 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d366851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366850 p = 1 := by simpa only [d366851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44334 p hg
    simpa only [d366851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44336 (p : Pattern) (guard : d366852 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42894 p hg
    simpa only [d366852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366851 p = 1 := by simpa only [d366852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44335 p hg
    simpa only [d366852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44337 (p : Pattern) (guard : d366853 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d366505 p = 1 := by simpa only [d366853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43825 p hg
    simpa only [d366853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366852 p = 1 := by simpa only [d366853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44336 p hg
    simpa only [d366853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44338 (p : Pattern) (guard : d366862 p = 1) : d51288 p ≤ (8 : Int) + d338690 p := by
  have ha := bounds51288 p
  have hb := bounds338690 p
  omega
theorem compare44339 (p : Pattern) (guard : d366863 p = 1) : d51289 p ≤ (8 : Int) + d338691 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366863, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42901 p hg
    simpa only [d366863, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366862 p = 1 := by simpa only [d366863, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44338 p hg
    simpa only [d366863, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44340 (p : Pattern) (guard : d366864 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366863 p = 1 := by simpa only [d366864, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44339 p hg
    simpa only [d366864, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366864, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42904 p hg
    simpa only [d366864, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44341 (p : Pattern) (guard : d366875 p = 1) : d51288 p ≤ (8 : Int) + d338690 p := by
  have ha := bounds51288 p
  have hb := bounds338690 p
  omega
theorem compare44342 (p : Pattern) (guard : d366876 p = 1) : d51289 p ≤ (8 : Int) + d338691 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366876, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42901 p hg
    simpa only [d366876, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366875 p = 1 := by simpa only [d366876, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44341 p hg
    simpa only [d366876, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44343 (p : Pattern) (guard : d366877 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366876 p = 1 := by simpa only [d366877, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44342 p hg
    simpa only [d366877, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366877, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42904 p hg
    simpa only [d366877, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44344 (p : Pattern) (guard : d366878 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366864 p = 1 := by simpa only [d366878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44340 p hg
    simpa only [d366878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366877 p = 1 := by simpa only [d366878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44343 p hg
    simpa only [d366878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44345 (p : Pattern) (guard : d366884 p = 1) : d51288 p ≤ (8 : Int) + d338690 p := by
  have ha := bounds51288 p
  have hb := bounds338690 p
  omega
theorem compare44346 (p : Pattern) (guard : d366885 p = 1) : d51289 p ≤ (8 : Int) + d338691 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366885, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42901 p hg
    simpa only [d366885, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366884 p = 1 := by simpa only [d366885, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44345 p hg
    simpa only [d366885, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44347 (p : Pattern) (guard : d366886 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366885 p = 1 := by simpa only [d366886, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44346 p hg
    simpa only [d366886, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366886, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42904 p hg
    simpa only [d366886, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44348 (p : Pattern) (guard : d366894 p = 1) : d51288 p ≤ (8 : Int) + d338690 p := by
  have ha := bounds51288 p
  have hb := bounds338690 p
  omega
theorem compare44349 (p : Pattern) (guard : d366895 p = 1) : d51289 p ≤ (8 : Int) + d338691 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366895, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42901 p hg
    simpa only [d366895, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366894 p = 1 := by simpa only [d366895, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44348 p hg
    simpa only [d366895, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44350 (p : Pattern) (guard : d366896 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366895 p = 1 := by simpa only [d366896, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44349 p hg
    simpa only [d366896, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366896, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42904 p hg
    simpa only [d366896, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44351 (p : Pattern) (guard : d366897 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366886 p = 1 := by simpa only [d366897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44347 p hg
    simpa only [d366897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366896 p = 1 := by simpa only [d366897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44350 p hg
    simpa only [d366897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44352 (p : Pattern) (guard : d366898 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366878 p = 1 := by simpa only [d366898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44344 p hg
    simpa only [d366898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366897 p = 1 := by simpa only [d366898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44351 p hg
    simpa only [d366898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44353 (p : Pattern) (guard : d366901 p = 1) : d51288 p ≤ (8 : Int) + d338690 p := by
  have ha := bounds51288 p
  have hb := bounds338690 p
  omega
theorem compare44354 (p : Pattern) (guard : d366902 p = 1) : d51289 p ≤ (8 : Int) + d338691 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366902, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42901 p hg
    simpa only [d366902, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366901 p = 1 := by simpa only [d366902, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44353 p hg
    simpa only [d366902, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44355 (p : Pattern) (guard : d366903 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366902 p = 1 := by simpa only [d366903, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44354 p hg
    simpa only [d366903, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366903, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42904 p hg
    simpa only [d366903, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44356 (p : Pattern) (guard : d366904 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366903 p = 1 := by simpa only [d366904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44355 p hg
    simpa only [d366904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366896 p = 1 := by simpa only [d366904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44350 p hg
    simpa only [d366904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44357 (p : Pattern) (guard : d366905 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366896 p = 1 := by simpa only [d366905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44350 p hg
    simpa only [d366905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42906 p hg
    simpa only [d366905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44358 (p : Pattern) (guard : d366906 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366904 p = 1 := by simpa only [d366906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44356 p hg
    simpa only [d366906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366905 p = 1 := by simpa only [d366906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44357 p hg
    simpa only [d366906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44359 (p : Pattern) (guard : d366907 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 157 with
  | false =>
    have hg : d366898 p = 1 := by simpa only [d366907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44352 p hg
    simpa only [d366907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366906 p = 1 := by simpa only [d366907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44358 p hg
    simpa only [d366907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44360 (p : Pattern) (guard : d366908 p = 1) : d51294 p ≤ (8 : Int) + d338713 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366908, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42900 p hg
    simpa only [d366908, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366907 p = 1 := by simpa only [d366908, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44359 p hg
    simpa only [d366908, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44361 (p : Pattern) (guard : d366909 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366909, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42899 p hg
    simpa only [d366909, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366908 p = 1 := by simpa only [d366909, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44360 p hg
    simpa only [d366909, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44362 (p : Pattern) (guard : d366910 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366905 p = 1 := by simpa only [d366910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44357 p hg
    simpa only [d366910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42906 p hg
    simpa only [d366910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44363 (p : Pattern) (guard : d366911 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 157 with
  | false =>
    have hg : d366906 p = 1 := by simpa only [d366911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44358 p hg
    simpa only [d366911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366910 p = 1 := by simpa only [d366911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44362 p hg
    simpa only [d366911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44364 (p : Pattern) (guard : d366912 p = 1) : d51294 p ≤ (8 : Int) + d338713 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366912, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42900 p hg
    simpa only [d366912, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366911 p = 1 := by simpa only [d366912, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44363 p hg
    simpa only [d366912, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44365 (p : Pattern) (guard : d366913 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366913, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42899 p hg
    simpa only [d366913, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366912 p = 1 := by simpa only [d366913, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44364 p hg
    simpa only [d366913, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44366 (p : Pattern) (guard : d366914 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 136 with
  | false =>
    have hg : d366909 p = 1 := by simpa only [d366914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44361 p hg
    simpa only [d366914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366913 p = 1 := by simpa only [d366914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44365 p hg
    simpa only [d366914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44367 (p : Pattern) (guard : d366915 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 136 with
  | false =>
    have hg : d366913 p = 1 := by simpa only [d366915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44365 p hg
    simpa only [d366915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42912 p hg
    simpa only [d366915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44368 (p : Pattern) (guard : d366916 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 135 with
  | false =>
    have hg : d366914 p = 1 := by simpa only [d366916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44366 p hg
    simpa only [d366916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366915 p = 1 := by simpa only [d366916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44367 p hg
    simpa only [d366916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44369 (p : Pattern) (guard : d366917 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 119 with
  | false =>
    have hg : d366916 p = 1 := by simpa only [d366917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44368 p hg
    simpa only [d366917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42912 p hg
    simpa only [d366917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44370 (p : Pattern) (guard : d366918 p = 1) : d51316 p ≤ (8 : Int) + d338726 p := by
  cases selected : p 116 with
  | false =>
    have hg : d366917 p = 1 := by simpa only [d366918, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44369 p hg
    simpa only [d366918, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366918, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42916 p hg
    simpa only [d366918, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44371 (p : Pattern) (guard : d366919 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366919, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42898 p hg
    simpa only [d366919, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366918 p = 1 := by simpa only [d366919, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44370 p hg
    simpa only [d366919, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44372 (p : Pattern) (guard : d366920 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 135 with
  | false =>
    have hg : d366915 p = 1 := by simpa only [d366920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44367 p hg
    simpa only [d366920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42912 p hg
    simpa only [d366920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44373 (p : Pattern) (guard : d366921 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 119 with
  | false =>
    have hg : d366920 p = 1 := by simpa only [d366921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44372 p hg
    simpa only [d366921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42912 p hg
    simpa only [d366921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44374 (p : Pattern) (guard : d366922 p = 1) : d51316 p ≤ (8 : Int) + d338726 p := by
  cases selected : p 116 with
  | false =>
    have hg : d366921 p = 1 := by simpa only [d366922, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44373 p hg
    simpa only [d366922, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366922, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42916 p hg
    simpa only [d366922, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44375 (p : Pattern) (guard : d366923 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366923, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42898 p hg
    simpa only [d366923, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366922 p = 1 := by simpa only [d366923, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44374 p hg
    simpa only [d366923, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44376 (p : Pattern) (guard : d366924 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366919 p = 1 := by simpa only [d366924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44371 p hg
    simpa only [d366924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366923 p = 1 := by simpa only [d366924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44375 p hg
    simpa only [d366924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44377 (p : Pattern) (guard : d366925 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366924 p = 1 := by simpa only [d366925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44376 p hg
    simpa only [d366925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44378 (p : Pattern) (guard : d366926 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366925 p = 1 := by simpa only [d366926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44377 p hg
    simpa only [d366926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44379 (p : Pattern) (guard : d366927 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366926 p = 1 := by simpa only [d366927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44378 p hg
    simpa only [d366927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44380 (p : Pattern) (guard : d366928 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366923 p = 1 := by simpa only [d366928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44375 p hg
    simpa only [d366928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44381 (p : Pattern) (guard : d366929 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366928 p = 1 := by simpa only [d366929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44380 p hg
    simpa only [d366929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44382 (p : Pattern) (guard : d366930 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366929 p = 1 := by simpa only [d366930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44381 p hg
    simpa only [d366930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44383 (p : Pattern) (guard : d366931 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366930 p = 1 := by simpa only [d366931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44382 p hg
    simpa only [d366931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44384 (p : Pattern) (guard : d366932 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366927 p = 1 := by simpa only [d366932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44379 p hg
    simpa only [d366932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366931 p = 1 := by simpa only [d366932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44383 p hg
    simpa only [d366932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44385 (p : Pattern) (guard : d366933 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366932 p = 1 := by simpa only [d366933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44384 p hg
    simpa only [d366933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44386 (p : Pattern) (guard : d366934 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366933 p = 1 := by simpa only [d366934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44385 p hg
    simpa only [d366934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44387 (p : Pattern) (guard : d366935 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366934 p = 1 := by simpa only [d366935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44386 p hg
    simpa only [d366935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44388 (p : Pattern) (guard : d366936 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366935 p = 1 := by simpa only [d366936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44387 p hg
    simpa only [d366936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44389 (p : Pattern) (guard : d366937 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366937, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366937, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366936 p = 1 := by simpa only [d366937, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44388 p hg
    simpa only [d366937, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44390 (p : Pattern) (guard : d366938 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42895 p hg
    simpa only [d366938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366937 p = 1 := by simpa only [d366938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44389 p hg
    simpa only [d366938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44391 (p : Pattern) (guard : d366939 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 69 with
  | false =>
    have hg : d366938 p = 1 := by simpa only [d366939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44390 p hg
    simpa only [d366939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42895 p hg
    simpa only [d366939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44392 (p : Pattern) (guard : d366919 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366919, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42929 p hg
    simpa only [d366919, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366918 p = 1 := by simpa only [d366919, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44370 p hg
    simpa only [d366919, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44393 (p : Pattern) (guard : d366923 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366923, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42929 p hg
    simpa only [d366923, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366922 p = 1 := by simpa only [d366923, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44374 p hg
    simpa only [d366923, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44394 (p : Pattern) (guard : d366924 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366919 p = 1 := by simpa only [d366924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44392 p hg
    simpa only [d366924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366923 p = 1 := by simpa only [d366924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44393 p hg
    simpa only [d366924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44395 (p : Pattern) (guard : d366925 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366924 p = 1 := by simpa only [d366925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44394 p hg
    simpa only [d366925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44396 (p : Pattern) (guard : d366926 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366925 p = 1 := by simpa only [d366926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44395 p hg
    simpa only [d366926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44397 (p : Pattern) (guard : d366927 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366926 p = 1 := by simpa only [d366927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44396 p hg
    simpa only [d366927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44398 (p : Pattern) (guard : d366928 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366923 p = 1 := by simpa only [d366928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44393 p hg
    simpa only [d366928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44399 (p : Pattern) (guard : d366929 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366928 p = 1 := by simpa only [d366929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44398 p hg
    simpa only [d366929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44400 (p : Pattern) (guard : d366930 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366929 p = 1 := by simpa only [d366930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44399 p hg
    simpa only [d366930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44401 (p : Pattern) (guard : d366931 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366930 p = 1 := by simpa only [d366931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44400 p hg
    simpa only [d366931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44402 (p : Pattern) (guard : d366932 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366927 p = 1 := by simpa only [d366932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44397 p hg
    simpa only [d366932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366931 p = 1 := by simpa only [d366932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44401 p hg
    simpa only [d366932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44403 (p : Pattern) (guard : d366933 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366932 p = 1 := by simpa only [d366933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44402 p hg
    simpa only [d366933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44404 (p : Pattern) (guard : d366934 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366933 p = 1 := by simpa only [d366934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44403 p hg
    simpa only [d366934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44405 (p : Pattern) (guard : d366935 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366934 p = 1 := by simpa only [d366935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44404 p hg
    simpa only [d366935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44406 (p : Pattern) (guard : d366936 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366935 p = 1 := by simpa only [d366936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44405 p hg
    simpa only [d366936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44407 (p : Pattern) (guard : d366940 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366926 p = 1 := by simpa only [d366940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44378 p hg
    simpa only [d366940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44408 (p : Pattern) (guard : d366941 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366930 p = 1 := by simpa only [d366941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44382 p hg
    simpa only [d366941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44409 (p : Pattern) (guard : d366942 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366940 p = 1 := by simpa only [d366942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44407 p hg
    simpa only [d366942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366941 p = 1 := by simpa only [d366942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44408 p hg
    simpa only [d366942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44410 (p : Pattern) (guard : d366943 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366942 p = 1 := by simpa only [d366943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44409 p hg
    simpa only [d366943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44411 (p : Pattern) (guard : d366944 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366943 p = 1 := by simpa only [d366944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44410 p hg
    simpa only [d366944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44412 (p : Pattern) (guard : d366945 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366944 p = 1 := by simpa only [d366945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44411 p hg
    simpa only [d366945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44413 (p : Pattern) (guard : d366946 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366945 p = 1 := by simpa only [d366946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44412 p hg
    simpa only [d366946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44414 (p : Pattern) (guard : d366947 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d366936 p = 1 := by simpa only [d366947, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44406 p hg
    simpa only [d366947, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366946 p = 1 := by simpa only [d366947, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44413 p hg
    simpa only [d366947, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44415 (p : Pattern) (guard : d366948 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 70 with
  | false =>
    have hg : d366937 p = 1 := by simpa only [d366948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44389 p hg
    simpa only [d366948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366947 p = 1 := by simpa only [d366948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44414 p hg
    simpa only [d366948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44416 (p : Pattern) (guard : d366949 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 69 with
  | false =>
    have hg : d366948 p = 1 := by simpa only [d366949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44415 p hg
    simpa only [d366949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42895 p hg
    simpa only [d366949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44417 (p : Pattern) (guard : d366950 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 51 with
  | false =>
    have hg : d366939 p = 1 := by simpa only [d366950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44391 p hg
    simpa only [d366950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366949 p = 1 := by simpa only [d366950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44416 p hg
    simpa only [d366950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44418 (p : Pattern) (guard : d366951 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366925 p = 1 := by simpa only [d366951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44377 p hg
    simpa only [d366951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44419 (p : Pattern) (guard : d366952 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366951 p = 1 := by simpa only [d366952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44418 p hg
    simpa only [d366952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44420 (p : Pattern) (guard : d366953 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366929 p = 1 := by simpa only [d366953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44381 p hg
    simpa only [d366953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44421 (p : Pattern) (guard : d366954 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366953 p = 1 := by simpa only [d366954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44420 p hg
    simpa only [d366954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44422 (p : Pattern) (guard : d366955 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366952 p = 1 := by simpa only [d366955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44419 p hg
    simpa only [d366955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366954 p = 1 := by simpa only [d366955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44421 p hg
    simpa only [d366955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44423 (p : Pattern) (guard : d366956 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366955 p = 1 := by simpa only [d366956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44422 p hg
    simpa only [d366956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44424 (p : Pattern) (guard : d366957 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366956 p = 1 := by simpa only [d366957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44423 p hg
    simpa only [d366957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44425 (p : Pattern) (guard : d366958 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366957 p = 1 := by simpa only [d366958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44424 p hg
    simpa only [d366958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44426 (p : Pattern) (guard : d366959 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366924 p = 1 := by simpa only [d366959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44376 p hg
    simpa only [d366959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44427 (p : Pattern) (guard : d366960 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366959 p = 1 := by simpa only [d366960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44426 p hg
    simpa only [d366960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44428 (p : Pattern) (guard : d366961 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366960 p = 1 := by simpa only [d366961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44427 p hg
    simpa only [d366961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44429 (p : Pattern) (guard : d366962 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366928 p = 1 := by simpa only [d366962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44380 p hg
    simpa only [d366962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44430 (p : Pattern) (guard : d366963 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366962 p = 1 := by simpa only [d366963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44429 p hg
    simpa only [d366963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44431 (p : Pattern) (guard : d366964 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366963 p = 1 := by simpa only [d366964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44430 p hg
    simpa only [d366964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44432 (p : Pattern) (guard : d366965 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366961 p = 1 := by simpa only [d366965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44428 p hg
    simpa only [d366965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366964 p = 1 := by simpa only [d366965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44431 p hg
    simpa only [d366965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44433 (p : Pattern) (guard : d366966 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366965 p = 1 := by simpa only [d366966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44432 p hg
    simpa only [d366966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44434 (p : Pattern) (guard : d366967 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366966 p = 1 := by simpa only [d366967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44433 p hg
    simpa only [d366967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d366967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44435 (p : Pattern) (guard : d312059 p = 1) : d51288 p ≤ (8 : Int) + d338690 p := by
  have ha := bounds51288 p
  have hb := bounds338690 p
  omega
theorem compare44436 (p : Pattern) (guard : d312060 p = 1) : d51289 p ≤ (8 : Int) + d338691 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d312060, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42901 p hg
    simpa only [d312060, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d312059 p = 1 := by simpa only [d312060, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44435 p hg
    simpa only [d312060, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44437 (p : Pattern) (guard : d312061 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 160 with
  | false =>
    have hg : d312060 p = 1 := by simpa only [d312061, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44436 p hg
    simpa only [d312061, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d312061, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42904 p hg
    simpa only [d312061, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44438 (p : Pattern) (guard : d366970 p = 1) : d51288 p ≤ (8 : Int) + d338690 p := by
  have ha := bounds51288 p
  have hb := bounds338690 p
  omega
theorem compare44439 (p : Pattern) (guard : d366971 p = 1) : d51289 p ≤ (8 : Int) + d338691 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366971, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42901 p hg
    simpa only [d366971, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366970 p = 1 := by simpa only [d366971, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44438 p hg
    simpa only [d366971, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44440 (p : Pattern) (guard : d366972 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366971 p = 1 := by simpa only [d366972, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44439 p hg
    simpa only [d366972, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366972, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42904 p hg
    simpa only [d366972, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44441 (p : Pattern) (guard : d366973 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 159 with
  | false =>
    have hg : d312061 p = 1 := by simpa only [d366973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44437 p hg
    simpa only [d366973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366972 p = 1 := by simpa only [d366973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44440 p hg
    simpa only [d366973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44442 (p : Pattern) (guard : d366976 p = 1) : d51288 p ≤ (8 : Int) + d338690 p := by
  have ha := bounds51288 p
  have hb := bounds338690 p
  omega
theorem compare44443 (p : Pattern) (guard : d366977 p = 1) : d51289 p ≤ (8 : Int) + d338691 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366977, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42901 p hg
    simpa only [d366977, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366976 p = 1 := by simpa only [d366977, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44442 p hg
    simpa only [d366977, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44444 (p : Pattern) (guard : d366978 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366977 p = 1 := by simpa only [d366978, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44443 p hg
    simpa only [d366978, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366978, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42904 p hg
    simpa only [d366978, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44445 (p : Pattern) (guard : d366979 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366978 p = 1 := by simpa only [d366979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44444 p hg
    simpa only [d366979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366886 p = 1 := by simpa only [d366979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44347 p hg
    simpa only [d366979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44446 (p : Pattern) (guard : d366980 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366973 p = 1 := by simpa only [d366980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44441 p hg
    simpa only [d366980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366979 p = 1 := by simpa only [d366980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44445 p hg
    simpa only [d366980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44447 (p : Pattern) (guard : d366981 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 157 with
  | false =>
    have hg : d366980 p = 1 := by simpa only [d366981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44446 p hg
    simpa only [d366981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366898 p = 1 := by simpa only [d366981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44352 p hg
    simpa only [d366981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44448 (p : Pattern) (guard : d366982 p = 1) : d51294 p ≤ (8 : Int) + d338713 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366982, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42900 p hg
    simpa only [d366982, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366981 p = 1 := by simpa only [d366982, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44447 p hg
    simpa only [d366982, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44449 (p : Pattern) (guard : d366983 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366983, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42899 p hg
    simpa only [d366983, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366982 p = 1 := by simpa only [d366983, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44448 p hg
    simpa only [d366983, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44450 (p : Pattern) (guard : d366991 p = 1) : d51288 p ≤ (8 : Int) + d338690 p := by
  have ha := bounds51288 p
  have hb := bounds338690 p
  omega
theorem compare44451 (p : Pattern) (guard : d366992 p = 1) : d51289 p ≤ (8 : Int) + d338691 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366992, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42901 p hg
    simpa only [d366992, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366991 p = 1 := by simpa only [d366992, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44450 p hg
    simpa only [d366992, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44452 (p : Pattern) (guard : d366993 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366992 p = 1 := by simpa only [d366993, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44451 p hg
    simpa only [d366993, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366993, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42904 p hg
    simpa only [d366993, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44453 (p : Pattern) (guard : d366994 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366993 p = 1 := by simpa only [d366994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44452 p hg
    simpa only [d366994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366896 p = 1 := by simpa only [d366994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44350 p hg
    simpa only [d366994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44454 (p : Pattern) (guard : d366995 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366994 p = 1 := by simpa only [d366995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44453 p hg
    simpa only [d366995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366905 p = 1 := by simpa only [d366995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44357 p hg
    simpa only [d366995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44455 (p : Pattern) (guard : d366996 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 157 with
  | false =>
    have hg : d366898 p = 1 := by simpa only [d366996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44352 p hg
    simpa only [d366996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366995 p = 1 := by simpa only [d366996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44454 p hg
    simpa only [d366996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44456 (p : Pattern) (guard : d366997 p = 1) : d51294 p ≤ (8 : Int) + d338713 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366997, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42900 p hg
    simpa only [d366997, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366996 p = 1 := by simpa only [d366997, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44455 p hg
    simpa only [d366997, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44457 (p : Pattern) (guard : d366998 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366998, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42899 p hg
    simpa only [d366998, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366997 p = 1 := by simpa only [d366998, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44456 p hg
    simpa only [d366998, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44458 (p : Pattern) (guard : d366999 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 136 with
  | false =>
    have hg : d366983 p = 1 := by simpa only [d366999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44449 p hg
    simpa only [d366999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366998 p = 1 := by simpa only [d366999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44457 p hg
    simpa only [d366999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44459 (p : Pattern) (guard : d367000 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 135 with
  | false =>
    have hg : d366999 p = 1 := by simpa only [d367000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44458 p hg
    simpa only [d367000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366914 p = 1 := by simpa only [d367000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44366 p hg
    simpa only [d367000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44460 (p : Pattern) (guard : d367001 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 119 with
  | false =>
    have hg : d367000 p = 1 := by simpa only [d367001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44459 p hg
    simpa only [d367001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42912 p hg
    simpa only [d367001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44461 (p : Pattern) (guard : d367002 p = 1) : d51316 p ≤ (8 : Int) + d338726 p := by
  cases selected : p 116 with
  | false =>
    have hg : d367001 p = 1 := by simpa only [d367002, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44460 p hg
    simpa only [d367002, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367002, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42916 p hg
    simpa only [d367002, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44462 (p : Pattern) (guard : d367003 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367003, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42898 p hg
    simpa only [d367003, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367002 p = 1 := by simpa only [d367003, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44461 p hg
    simpa only [d367003, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44463 (p : Pattern) (guard : d367004 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d367003 p = 1 := by simpa only [d367004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44462 p hg
    simpa only [d367004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366919 p = 1 := by simpa only [d367004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44371 p hg
    simpa only [d367004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44464 (p : Pattern) (guard : d367005 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d367004 p = 1 := by simpa only [d367005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44463 p hg
    simpa only [d367005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44465 (p : Pattern) (guard : d367006 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d367005 p = 1 := by simpa only [d367006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44464 p hg
    simpa only [d367006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44466 (p : Pattern) (guard : d367007 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367006 p = 1 := by simpa only [d367007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44465 p hg
    simpa only [d367007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44467 (p : Pattern) (guard : d367008 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d367007 p = 1 := by simpa only [d367008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44466 p hg
    simpa only [d367008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366927 p = 1 := by simpa only [d367008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44379 p hg
    simpa only [d367008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44468 (p : Pattern) (guard : d367009 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d367008 p = 1 := by simpa only [d367009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44467 p hg
    simpa only [d367009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44469 (p : Pattern) (guard : d367010 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366919 p = 1 := by simpa only [d367010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44371 p hg
    simpa only [d367010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44470 (p : Pattern) (guard : d367011 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d367010 p = 1 := by simpa only [d367011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44469 p hg
    simpa only [d367011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44471 (p : Pattern) (guard : d367012 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d367011 p = 1 := by simpa only [d367012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44470 p hg
    simpa only [d367012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44472 (p : Pattern) (guard : d367013 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367012 p = 1 := by simpa only [d367013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44471 p hg
    simpa only [d367013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44473 (p : Pattern) (guard : d367014 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d367013 p = 1 := by simpa only [d367014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44472 p hg
    simpa only [d367014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44474 (p : Pattern) (guard : d367015 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d367014 p = 1 := by simpa only [d367015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44473 p hg
    simpa only [d367015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d367015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44475 (p : Pattern) (guard : d367016 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d367009 p = 1 := by simpa only [d367016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44468 p hg
    simpa only [d367016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367015 p = 1 := by simpa only [d367016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44474 p hg
    simpa only [d367016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44476 (p : Pattern) (guard : d367017 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d366967 p = 1 := by simpa only [d367017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44434 p hg
    simpa only [d367017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367016 p = 1 := by simpa only [d367017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44475 p hg
    simpa only [d367017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44477 (p : Pattern) (guard : d367018 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d366958 p = 1 := by simpa only [d367018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44425 p hg
    simpa only [d367018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367017 p = 1 := by simpa only [d367018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44476 p hg
    simpa only [d367018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44478 (p : Pattern) (guard : d367019 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367019, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367019, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367018 p = 1 := by simpa only [d367019, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44477 p hg
    simpa only [d367019, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44479 (p : Pattern) (guard : d366951 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366925 p = 1 := by simpa only [d366951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44395 p hg
    simpa only [d366951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44480 (p : Pattern) (guard : d366952 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366951 p = 1 := by simpa only [d366952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44479 p hg
    simpa only [d366952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44481 (p : Pattern) (guard : d366953 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366929 p = 1 := by simpa only [d366953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44399 p hg
    simpa only [d366953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44482 (p : Pattern) (guard : d366954 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366953 p = 1 := by simpa only [d366954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44481 p hg
    simpa only [d366954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44483 (p : Pattern) (guard : d366955 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366952 p = 1 := by simpa only [d366955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44480 p hg
    simpa only [d366955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366954 p = 1 := by simpa only [d366955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44482 p hg
    simpa only [d366955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44484 (p : Pattern) (guard : d366956 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366955 p = 1 := by simpa only [d366956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44483 p hg
    simpa only [d366956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44485 (p : Pattern) (guard : d366957 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366956 p = 1 := by simpa only [d366957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44484 p hg
    simpa only [d366957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44486 (p : Pattern) (guard : d366958 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366957 p = 1 := by simpa only [d366958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44485 p hg
    simpa only [d366958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44487 (p : Pattern) (guard : d366959 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366924 p = 1 := by simpa only [d366959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44394 p hg
    simpa only [d366959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44488 (p : Pattern) (guard : d366960 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366959 p = 1 := by simpa only [d366960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44487 p hg
    simpa only [d366960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44489 (p : Pattern) (guard : d366961 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366960 p = 1 := by simpa only [d366961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44488 p hg
    simpa only [d366961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44490 (p : Pattern) (guard : d366962 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366928 p = 1 := by simpa only [d366962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44398 p hg
    simpa only [d366962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44491 (p : Pattern) (guard : d366963 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366962 p = 1 := by simpa only [d366963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44490 p hg
    simpa only [d366963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44492 (p : Pattern) (guard : d366964 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366963 p = 1 := by simpa only [d366964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44491 p hg
    simpa only [d366964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44493 (p : Pattern) (guard : d366965 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366961 p = 1 := by simpa only [d366965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44489 p hg
    simpa only [d366965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366964 p = 1 := by simpa only [d366965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44492 p hg
    simpa only [d366965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44494 (p : Pattern) (guard : d366966 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366965 p = 1 := by simpa only [d366966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44493 p hg
    simpa only [d366966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44495 (p : Pattern) (guard : d366967 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366966 p = 1 := by simpa only [d366967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44494 p hg
    simpa only [d366967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d366967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44496 (p : Pattern) (guard : d367003 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367003, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42929 p hg
    simpa only [d367003, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367002 p = 1 := by simpa only [d367003, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44461 p hg
    simpa only [d367003, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44497 (p : Pattern) (guard : d367004 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d367003 p = 1 := by simpa only [d367004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44496 p hg
    simpa only [d367004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366919 p = 1 := by simpa only [d367004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44392 p hg
    simpa only [d367004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44498 (p : Pattern) (guard : d367005 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d367004 p = 1 := by simpa only [d367005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44497 p hg
    simpa only [d367005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare44499 (p : Pattern) (guard : d367006 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d367005 p = 1 := by simpa only [d367006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44498 p hg
    simpa only [d367006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d367006, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
