import NetHack.Soko22Hazard87.Compare183
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare46000 (p : Pattern) (guard : d366542 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 202 with
  | false =>
    have hg : d366512 p = 1 := by simpa only [d366542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45959 p hg
    simpa only [d366542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342709 p = 1 := by simpa only [d366542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45391 p hg
    simpa only [d366542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46001 (p : Pattern) (guard : d366543 p = 1) : d51242 p ≤ (7 : Int) + d2 p := by
  cases selected : p 201 with
  | false =>
    have hg : d366542 p = 1 := by simpa only [d366543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46000 p hg
    simpa only [d366543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342710 p = 1 := by simpa only [d366543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45393 p hg
    simpa only [d366543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46002 (p : Pattern) (guard : d366544 p = 1) : d51277 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 182 with
  | false =>
    have hg : d366543 p = 1 := by simpa only [d366544, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46001 p hg
    simpa only [d366544, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366544, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45395 p hg
    simpa only [d366544, d51277, d338681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46003 (p : Pattern) (guard : d366545 p = 1) : d51277 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 180 with
  | false =>
    have hg : d366544 p = 1 := by simpa only [d366545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46002 p hg
    simpa only [d366545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45397 p hg
    simpa only [d366545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46004 (p : Pattern) (guard : d366761 p = 1) : d51529 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366761, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45380 p hg
    simpa only [d366761, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366545 p = 1 := by simpa only [d366761, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46003 p hg
    simpa only [d366761, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46005 (p : Pattern) (guard : d366546 p = 1) : d51530 p ≤ (7 : Int) + d338814 p := by
  cases selected : p 163 with
  | false =>
    have hg : d366545 p = 1 := by simpa only [d366546, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45818 p hg
    simpa only [d366546, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366546, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45400 p hg
    simpa only [d366546, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46006 (p : Pattern) (guard : d366762 p = 1) : d51531 p ≤ (7 : Int) + d338815 p := by
  cases selected : p 162 with
  | false =>
    have hg : d366761 p = 1 := by simpa only [d366762, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46004 p hg
    simpa only [d366762, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366546 p = 1 := by simpa only [d366762, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46005 p hg
    simpa only [d366762, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46007 (p : Pattern) (guard : d366547 p = 1) : d51291 p ≤ (7 : Int) + d338710 p := by
  have ha := bounds51291 p
  have hb := bounds338710 p
  omega
theorem compare46008 (p : Pattern) (guard : d366763 p = 1) : d51532 p ≤ (7 : Int) + d338816 p := by
  cases selected : p 161 with
  | false =>
    have hg : d366762 p = 1 := by simpa only [d366763, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46006 p hg
    simpa only [d366763, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366547 p = 1 := by simpa only [d366763, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46007 p hg
    simpa only [d366763, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46009 (p : Pattern) (guard : d366764 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366763 p = 1 := by simpa only [d366764, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46008 p hg
    simpa only [d366764, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366764, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45405 p hg
    simpa only [d366764, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46010 (p : Pattern) (guard : d366765 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366749 p = 1 := by simpa only [d366765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45999 p hg
    simpa only [d366765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366764 p = 1 := by simpa only [d366765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46009 p hg
    simpa only [d366765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46011 (p : Pattern) (guard : d366766 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366760 p = 1 := by simpa only [d366766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45987 p hg
    simpa only [d366766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366765 p = 1 := by simpa only [d366766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46010 p hg
    simpa only [d366766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46012 (p : Pattern) (guard : d366552 p = 1) : d51277 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 180 with
  | false =>
    have hg : d366522 p = 1 := by simpa only [d366552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45972 p hg
    simpa only [d366552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366544 p = 1 := by simpa only [d366552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46002 p hg
    simpa only [d366552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46013 (p : Pattern) (guard : d366781 p = 1) : d51529 p ≤ (7 : Int) + d338681 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366781, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45380 p hg
    simpa only [d366781, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366552 p = 1 := by simpa only [d366781, d51529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46012 p hg
    simpa only [d366781, d51529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46014 (p : Pattern) (guard : d366553 p = 1) : d51530 p ≤ (7 : Int) + d338814 p := by
  cases selected : p 163 with
  | false =>
    have hg : d366552 p = 1 := by simpa only [d366553, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45825 p hg
    simpa only [d366553, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366553, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45400 p hg
    simpa only [d366553, d51530, d338814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46015 (p : Pattern) (guard : d366782 p = 1) : d51531 p ≤ (7 : Int) + d338815 p := by
  cases selected : p 162 with
  | false =>
    have hg : d366781 p = 1 := by simpa only [d366782, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46013 p hg
    simpa only [d366782, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366553 p = 1 := by simpa only [d366782, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46014 p hg
    simpa only [d366782, d51531, d338815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46016 (p : Pattern) (guard : d366554 p = 1) : d51291 p ≤ (7 : Int) + d338710 p := by
  have ha := bounds51291 p
  have hb := bounds338710 p
  omega
theorem compare46017 (p : Pattern) (guard : d366783 p = 1) : d51532 p ≤ (7 : Int) + d338816 p := by
  cases selected : p 161 with
  | false =>
    have hg : d366782 p = 1 := by simpa only [d366783, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46015 p hg
    simpa only [d366783, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366554 p = 1 := by simpa only [d366783, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46016 p hg
    simpa only [d366783, d51532, d338816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46018 (p : Pattern) (guard : d366784 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366783 p = 1 := by simpa only [d366784, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46017 p hg
    simpa only [d366784, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366784, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45405 p hg
    simpa only [d366784, d51536, d338820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46019 (p : Pattern) (guard : d366785 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366784 p = 1 := by simpa only [d366785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46018 p hg
    simpa only [d366785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366764 p = 1 := by simpa only [d366785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46009 p hg
    simpa only [d366785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46020 (p : Pattern) (guard : d366775 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366764 p = 1 := by simpa only [d366775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46009 p hg
    simpa only [d366775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45407 p hg
    simpa only [d366775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46021 (p : Pattern) (guard : d366786 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366785 p = 1 := by simpa only [d366786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46019 p hg
    simpa only [d366786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366775 p = 1 := by simpa only [d366786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46020 p hg
    simpa only [d366786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46022 (p : Pattern) (guard : d366787 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 157 with
  | false =>
    have hg : d366766 p = 1 := by simpa only [d366787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46011 p hg
    simpa only [d366787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366786 p = 1 := by simpa only [d366787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46021 p hg
    simpa only [d366787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46023 (p : Pattern) (guard : d366788 p = 1) : d51537 p ≤ (7 : Int) + d338821 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366788, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45379 p hg
    simpa only [d366788, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366787 p = 1 := by simpa only [d366788, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46022 p hg
    simpa only [d366788, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46024 (p : Pattern) (guard : d366789 p = 1) : d51538 p ≤ (7 : Int) + d338822 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366789, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45378 p hg
    simpa only [d366789, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366788 p = 1 := by simpa only [d366789, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46023 p hg
    simpa only [d366789, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46025 (p : Pattern) (guard : d366790 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366775 p = 1 := by simpa only [d366790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46020 p hg
    simpa only [d366790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45407 p hg
    simpa only [d366790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46026 (p : Pattern) (guard : d366791 p = 1) : d51536 p ≤ (7 : Int) + d338820 p := by
  cases selected : p 157 with
  | false =>
    have hg : d366786 p = 1 := by simpa only [d366791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46021 p hg
    simpa only [d366791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366790 p = 1 := by simpa only [d366791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46025 p hg
    simpa only [d366791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46027 (p : Pattern) (guard : d366792 p = 1) : d51537 p ≤ (7 : Int) + d338821 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366792, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45379 p hg
    simpa only [d366792, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366791 p = 1 := by simpa only [d366792, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46026 p hg
    simpa only [d366792, d51537, d338821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46028 (p : Pattern) (guard : d366793 p = 1) : d51538 p ≤ (7 : Int) + d338822 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366793, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45378 p hg
    simpa only [d366793, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366792 p = 1 := by simpa only [d366793, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46027 p hg
    simpa only [d366793, d51538, d338822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46029 (p : Pattern) (guard : d366794 p = 1) : d51538 p ≤ (7 : Int) + d338822 p := by
  cases selected : p 136 with
  | false =>
    have hg : d366789 p = 1 := by simpa only [d366794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46024 p hg
    simpa only [d366794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366793 p = 1 := by simpa only [d366794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46028 p hg
    simpa only [d366794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46030 (p : Pattern) (guard : d366799 p = 1) : d51538 p ≤ (7 : Int) + d338822 p := by
  cases selected : p 136 with
  | false =>
    have hg : d366793 p = 1 := by simpa only [d366799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46028 p hg
    simpa only [d366799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45413 p hg
    simpa only [d366799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46031 (p : Pattern) (guard : d366800 p = 1) : d51538 p ≤ (7 : Int) + d338822 p := by
  cases selected : p 135 with
  | false =>
    have hg : d366794 p = 1 := by simpa only [d366800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46029 p hg
    simpa only [d366800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366799 p = 1 := by simpa only [d366800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46030 p hg
    simpa only [d366800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46032 (p : Pattern) (guard : d366801 p = 1) : d51538 p ≤ (7 : Int) + d338822 p := by
  cases selected : p 119 with
  | false =>
    have hg : d366800 p = 1 := by simpa only [d366801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46031 p hg
    simpa only [d366801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45413 p hg
    simpa only [d366801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46033 (p : Pattern) (guard : d366802 p = 1) : d51540 p ≤ (7 : Int) + d338824 p := by
  cases selected : p 116 with
  | false =>
    have hg : d366801 p = 1 := by simpa only [d366802, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46032 p hg
    simpa only [d366802, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366802, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45417 p hg
    simpa only [d366802, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46034 (p : Pattern) (guard : d366803 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366803, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45264 p hg
    simpa only [d366803, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366802 p = 1 := by simpa only [d366803, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46033 p hg
    simpa only [d366803, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46035 (p : Pattern) (guard : d366808 p = 1) : d51538 p ≤ (7 : Int) + d338822 p := by
  cases selected : p 135 with
  | false =>
    have hg : d366799 p = 1 := by simpa only [d366808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46030 p hg
    simpa only [d366808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45413 p hg
    simpa only [d366808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46036 (p : Pattern) (guard : d366809 p = 1) : d51538 p ≤ (7 : Int) + d338822 p := by
  cases selected : p 119 with
  | false =>
    have hg : d366808 p = 1 := by simpa only [d366809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46035 p hg
    simpa only [d366809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45413 p hg
    simpa only [d366809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46037 (p : Pattern) (guard : d366810 p = 1) : d51540 p ≤ (7 : Int) + d338824 p := by
  cases selected : p 116 with
  | false =>
    have hg : d366809 p = 1 := by simpa only [d366810, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46036 p hg
    simpa only [d366810, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366810, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45417 p hg
    simpa only [d366810, d51540, d338824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46038 (p : Pattern) (guard : d366811 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366811, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45264 p hg
    simpa only [d366811, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366810 p = 1 := by simpa only [d366811, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46037 p hg
    simpa only [d366811, d51541, d338825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46039 (p : Pattern) (guard : d366812 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366803 p = 1 := by simpa only [d366812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46034 p hg
    simpa only [d366812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366811 p = 1 := by simpa only [d366812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46038 p hg
    simpa only [d366812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46040 (p : Pattern) (guard : d366813 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366812 p = 1 := by simpa only [d366813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46039 p hg
    simpa only [d366813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d366813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46041 (p : Pattern) (guard : d366814 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366813 p = 1 := by simpa only [d366814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46040 p hg
    simpa only [d366814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d366814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46042 (p : Pattern) (guard : d366815 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366814 p = 1 := by simpa only [d366815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46041 p hg
    simpa only [d366815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d366815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46043 (p : Pattern) (guard : d366829 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366811 p = 1 := by simpa only [d366829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46038 p hg
    simpa only [d366829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d366829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46044 (p : Pattern) (guard : d366830 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366829 p = 1 := by simpa only [d366830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46043 p hg
    simpa only [d366830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d366830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46045 (p : Pattern) (guard : d366831 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366830 p = 1 := by simpa only [d366831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46044 p hg
    simpa only [d366831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d366831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46046 (p : Pattern) (guard : d366832 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366831 p = 1 := by simpa only [d366832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46045 p hg
    simpa only [d366832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d366832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46047 (p : Pattern) (guard : d367475 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366815 p = 1 := by simpa only [d367475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46042 p hg
    simpa only [d367475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366832 p = 1 := by simpa only [d367475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46046 p hg
    simpa only [d367475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46048 (p : Pattern) (guard : d367476 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d367476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367475 p = 1 := by simpa only [d367476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46047 p hg
    simpa only [d367476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46049 (p : Pattern) (guard : d367477 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 89 with
  | false =>
    have hg : d367476 p = 1 := by simpa only [d367477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46048 p hg
    simpa only [d367477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d367477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46050 (p : Pattern) (guard : d367478 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d367478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367477 p = 1 := by simpa only [d367478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46049 p hg
    simpa only [d367478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46051 (p : Pattern) (guard : d367479 p = 1) : d51541 p ≤ (7 : Int) + d338825 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45377 p hg
    simpa only [d367479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367478 p = 1 := by simpa only [d367479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46050 p hg
    simpa only [d367479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46052 (p : Pattern) (guard : d367480 p = 1) : d51542 p ≤ (7 : Int) + d338826 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367480, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d367480, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367479 p = 1 := by simpa only [d367480, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46051 p hg
    simpa only [d367480, d51542, d338826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46053 (p : Pattern) (guard : d367481 p = 1) : d51542 p ≤ (7 : Int) + d338826 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45376 p hg
    simpa only [d367481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367480 p = 1 := by simpa only [d367481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46052 p hg
    simpa only [d367481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46054 (p : Pattern) (guard : d367482 p = 1) : d51542 p ≤ (7 : Int) + d338826 p := by
  cases selected : p 69 with
  | false =>
    have hg : d367481 p = 1 := by simpa only [d367482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46053 p hg
    simpa only [d367482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45376 p hg
    simpa only [d367482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46055 (p : Pattern) (guard : d367483 p = 1) : d51542 p ≤ (7 : Int) + d338826 p := by
  cases selected : p 51 with
  | false =>
    have hg : d367482 p = 1 := by simpa only [d367483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46054 p hg
    simpa only [d367483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45376 p hg
    simpa only [d367483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46056 (p : Pattern) (guard : d367484 p = 1) : d51542 p ≤ (7 : Int) + d338826 p := by
  cases selected : p 50 with
  | false =>
    have hg : d367483 p = 1 := by simpa only [d367484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46055 p hg
    simpa only [d367484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45376 p hg
    simpa only [d367484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46057 (p : Pattern) (guard : d367485 p = 1) : d51634 p ≤ (7 : Int) + d338882 p := by
  cases selected : p 49 with
  | false =>
    have hg : d367484 p = 1 := by simpa only [d367485, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46056 p hg
    simpa only [d367485, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367485, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45434 p hg
    simpa only [d367485, d51634, d338882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46058 (p : Pattern) (guard : d367486 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 48 with
  | false =>
    have hg : d367474 p = 1 := by simpa only [d367486, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45947 p hg
    simpa only [d367486, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367485 p = 1 := by simpa only [d367486, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46057 p hg
    simpa only [d367486, d51635, d338883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46059 (p : Pattern) (guard : d367487 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367486 p = 1 := by simpa only [d367487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46058 p hg
    simpa only [d367487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46060 (p : Pattern) (guard : d367488 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367487 p = 1 := by simpa only [d367488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46059 p hg
    simpa only [d367488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46061 (p : Pattern) (guard : d367489 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367488 p = 1 := by simpa only [d367489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46060 p hg
    simpa only [d367489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46062 (p : Pattern) (guard : d367490 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367489 p = 1 := by simpa only [d367490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46061 p hg
    simpa only [d367490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46063 (p : Pattern) (guard : d367491 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367490 p = 1 := by simpa only [d367491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46062 p hg
    simpa only [d367491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46064 (p : Pattern) (guard : d367492 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367491 p = 1 := by simpa only [d367492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46063 p hg
    simpa only [d367492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46065 (p : Pattern) (guard : d367493 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367492 p = 1 := by simpa only [d367493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46064 p hg
    simpa only [d367493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46066 (p : Pattern) (guard : d367494 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45260 p hg
    simpa only [d367494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367493 p = 1 := by simpa only [d367494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46065 p hg
    simpa only [d367494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46067 (p : Pattern) (guard : d367495 p = 1) : d51635 p ≤ (7 : Int) + d338883 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d367466 p = 1 := by simpa only [d367495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45768 p hg
    simpa only [d367495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367494 p = 1 := by simpa only [d367495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46066 p hg
    simpa only [d367495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46068 (p : Pattern) (guard : d2006 p = 1) : d47616 p ≤ (7 : Int) + d4 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2005 p = 1 := by simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45581 p hg
    simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45268 p hg
    simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46069 (p : Pattern) (guard : d2007 p = 1) : d47616 p ≤ (7 : Int) + d4 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45268 p hg
    simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2006 p = 1 := by simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46068 p hg
    simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46070 (p : Pattern) (guard : d2008 p = 1) : d47616 p ≤ (7 : Int) + d4 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45268 p hg
    simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2007 p = 1 := by simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46069 p hg
    simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46071 (p : Pattern) (guard : d34782 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2008 p = 1 := by simpa only [d34782, d51204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46070 p hg
    simpa only [d34782, d51204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34782, d51204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45277 p hg
    simpa only [d34782, d51204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46072 (p : Pattern) (guard : d34783 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d34783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45279 p hg
    simpa only [d34783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34782 p = 1 := by simpa only [d34783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46071 p hg
    simpa only [d34783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46073 (p : Pattern) (guard : d43846 p = 1) : d47616 p ≤ (7 : Int) + d4 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2007 p = 1 := by simpa only [d43846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46069 p hg
    simpa only [d43846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d43846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45268 p hg
    simpa only [d43846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46074 (p : Pattern) (guard : d43847 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 204 with
  | false =>
    have hg : d43846 p = 1 := by simpa only [d43847, d51204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46073 p hg
    simpa only [d43847, d51204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d43847, d51204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45277 p hg
    simpa only [d43847, d51204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46075 (p : Pattern) (guard : d43848 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d43848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45279 p hg
    simpa only [d43848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d43847 p = 1 := by simpa only [d43848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46074 p hg
    simpa only [d43848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46076 (p : Pattern) (guard : d311925 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 201 with
  | false =>
    have hg : d34783 p = 1 := by simpa only [d311925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46072 p hg
    simpa only [d311925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d43848 p = 1 := by simpa only [d311925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46075 p hg
    simpa only [d311925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46077 (p : Pattern) (guard : d311926 p = 1) : d51269 p ≤ (7 : Int) + d338656 p := by
  cases selected : p 182 with
  | false =>
    have hg : d311925 p = 1 := by simpa only [d311926, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46076 p hg
    simpa only [d311926, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d311926, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45282 p hg
    simpa only [d311926, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46078 (p : Pattern) (guard : d43867 p = 1) : d47616 p ≤ (7 : Int) + d4 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2002 p = 1 := by simpa only [d43867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45580 p hg
    simpa only [d43867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2006 p = 1 := by simpa only [d43867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46068 p hg
    simpa only [d43867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46079 (p : Pattern) (guard : d10054 p = 1) : d47616 p ≤ (7 : Int) + d4 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2006 p = 1 := by simpa only [d10054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46068 p hg
    simpa only [d10054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45268 p hg
    simpa only [d10054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46080 (p : Pattern) (guard : d366854 p = 1) : d47616 p ≤ (7 : Int) + d4 p := by
  cases selected : p 223 with
  | false =>
    have hg : d43867 p = 1 := by simpa only [d366854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46078 p hg
    simpa only [d366854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10054 p = 1 := by simpa only [d366854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46079 p hg
    simpa only [d366854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46081 (p : Pattern) (guard : d366855 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 204 with
  | false =>
    have hg : d366854 p = 1 := by simpa only [d366855, d51204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46080 p hg
    simpa only [d366855, d51204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366855, d51204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45277 p hg
    simpa only [d366855, d51204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46082 (p : Pattern) (guard : d366856 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 202 with
  | false =>
    have hg : d34782 p = 1 := by simpa only [d366856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46071 p hg
    simpa only [d366856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366855 p = 1 := by simpa only [d366856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46081 p hg
    simpa only [d366856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46083 (p : Pattern) (guard : d343143 p = 1) : d47616 p ≤ (7 : Int) + d4 p := by
  cases selected : p 223 with
  | false =>
    have hg : d10054 p = 1 := by simpa only [d343143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46079 p hg
    simpa only [d343143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45268 p hg
    simpa only [d343143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46084 (p : Pattern) (guard : d343144 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 204 with
  | false =>
    have hg : d343143 p = 1 := by simpa only [d343144, d51204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46083 p hg
    simpa only [d343144, d51204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343144, d51204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45277 p hg
    simpa only [d343144, d51204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46085 (p : Pattern) (guard : d366857 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 202 with
  | false =>
    have hg : d43847 p = 1 := by simpa only [d366857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46074 p hg
    simpa only [d366857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343144 p = 1 := by simpa only [d366857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46084 p hg
    simpa only [d366857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46086 (p : Pattern) (guard : d366858 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 201 with
  | false =>
    have hg : d366856 p = 1 := by simpa only [d366858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46082 p hg
    simpa only [d366858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366857 p = 1 := by simpa only [d366858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46085 p hg
    simpa only [d366858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46087 (p : Pattern) (guard : d366859 p = 1) : d51269 p ≤ (7 : Int) + d338656 p := by
  cases selected : p 182 with
  | false =>
    have hg : d366858 p = 1 := by simpa only [d366859, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46086 p hg
    simpa only [d366859, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366859, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45282 p hg
    simpa only [d366859, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46088 (p : Pattern) (guard : d366860 p = 1) : d51269 p ≤ (7 : Int) + d338656 p := by
  cases selected : p 180 with
  | false =>
    have hg : d311926 p = 1 := by simpa only [d366860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46077 p hg
    simpa only [d366860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366859 p = 1 := by simpa only [d366860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46087 p hg
    simpa only [d366860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46089 (p : Pattern) (guard : d366861 p = 1) : d51287 p ≤ (7 : Int) + d338687 p := by
  cases selected : p 163 with
  | false =>
    have hg : d366860 p = 1 := by simpa only [d366861, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46088 p hg
    simpa only [d366861, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366861, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45286 p hg
    simpa only [d366861, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46090 (p : Pattern) (guard : d366862 p = 1) : d51288 p ≤ (7 : Int) + d338690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d366861 p = 1 := by simpa only [d366862, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46089 p hg
    simpa only [d366862, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366862, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45288 p hg
    simpa only [d366862, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46091 (p : Pattern) (guard : d366863 p = 1) : d51289 p ≤ (7 : Int) + d338691 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366863, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45267 p hg
    simpa only [d366863, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366862 p = 1 := by simpa only [d366863, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46090 p hg
    simpa only [d366863, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46092 (p : Pattern) (guard : d366864 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366863 p = 1 := by simpa only [d366864, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46091 p hg
    simpa only [d366864, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366864, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45291 p hg
    simpa only [d366864, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46093 (p : Pattern) (guard : d43868 p = 1) : d47616 p ≤ (7 : Int) + d4 p := by
  cases selected : p 223 with
  | false =>
    have hg : d43867 p = 1 := by simpa only [d43868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46078 p hg
    simpa only [d43868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d43868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45268 p hg
    simpa only [d43868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46094 (p : Pattern) (guard : d43869 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 204 with
  | false =>
    have hg : d43868 p = 1 := by simpa only [d43869, d51204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46093 p hg
    simpa only [d43869, d51204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d43869, d51204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45277 p hg
    simpa only [d43869, d51204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46095 (p : Pattern) (guard : d366865 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 202 with
  | false =>
    have hg : d43869 p = 1 := by simpa only [d366865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46094 p hg
    simpa only [d366865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343144 p = 1 := by simpa only [d366865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46084 p hg
    simpa only [d366865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46096 (p : Pattern) (guard : d366866 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 201 with
  | false =>
    have hg : d366856 p = 1 := by simpa only [d366866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46082 p hg
    simpa only [d366866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366865 p = 1 := by simpa only [d366866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46095 p hg
    simpa only [d366866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46097 (p : Pattern) (guard : d366867 p = 1) : d51269 p ≤ (7 : Int) + d338656 p := by
  cases selected : p 182 with
  | false =>
    have hg : d366866 p = 1 := by simpa only [d366867, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46096 p hg
    simpa only [d366867, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366867, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45282 p hg
    simpa only [d366867, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46098 (p : Pattern) (guard : d32698 p = 1) : d47616 p ≤ (7 : Int) + d4 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2002 p = 1 := by simpa only [d32698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45580 p hg
    simpa only [d32698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d32698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45268 p hg
    simpa only [d32698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46099 (p : Pattern) (guard : d366868 p = 1) : d47616 p ≤ (7 : Int) + d4 p := by
  cases selected : p 223 with
  | false =>
    have hg : d32698 p = 1 := by simpa only [d366868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46098 p hg
    simpa only [d366868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32153 p = 1 := by simpa only [d366868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45793 p hg
    simpa only [d366868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46100 (p : Pattern) (guard : d0 p = 1) : d51200 p ≤ (7 : Int) + d4 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46101 (p : Pattern) (guard : d1086 p = 1) : d51201 p ≤ (7 : Int) + d4 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1085 p = 1 := by simpa only [d1086, d51201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45273 p hg
    simpa only [d1086, d51201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1086, d51201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46100 p hg
    simpa only [d1086, d51201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46102 (p : Pattern) (guard : d0 p = 1) : d51202 p ≤ (7 : Int) + d4 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare46103 (p : Pattern) (guard : d9771 p = 1) : d51203 p ≤ (7 : Int) + d4 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1086 p = 1 := by simpa only [d9771, d51203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46101 p hg
    simpa only [d9771, d51203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9771, d51203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46102 p hg
    simpa only [d9771, d51203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46104 (p : Pattern) (guard : d32155 p = 1) : d51203 p ≤ (7 : Int) + d4 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d32155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45277 p hg
    simpa only [d32155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9771 p = 1 := by simpa only [d32155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46103 p hg
    simpa only [d32155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46105 (p : Pattern) (guard : d366869 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 204 with
  | false =>
    have hg : d366868 p = 1 := by simpa only [d366869, d51204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46099 p hg
    simpa only [d366869, d51204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32155 p = 1 := by simpa only [d366869, d51204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46104 p hg
    simpa only [d366869, d51204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46106 (p : Pattern) (guard : d366870 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 202 with
  | false =>
    have hg : d366869 p = 1 := by simpa only [d366870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46105 p hg
    simpa only [d366870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343144 p = 1 := by simpa only [d366870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46084 p hg
    simpa only [d366870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46107 (p : Pattern) (guard : d366871 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 201 with
  | false =>
    have hg : d366870 p = 1 := by simpa only [d366871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46106 p hg
    simpa only [d366871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45279 p hg
    simpa only [d366871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46108 (p : Pattern) (guard : d366872 p = 1) : d51269 p ≤ (7 : Int) + d338656 p := by
  cases selected : p 182 with
  | false =>
    have hg : d366871 p = 1 := by simpa only [d366872, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46107 p hg
    simpa only [d366872, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366872, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45282 p hg
    simpa only [d366872, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46109 (p : Pattern) (guard : d366873 p = 1) : d51269 p ≤ (7 : Int) + d338656 p := by
  cases selected : p 180 with
  | false =>
    have hg : d366867 p = 1 := by simpa only [d366873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46097 p hg
    simpa only [d366873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366872 p = 1 := by simpa only [d366873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46108 p hg
    simpa only [d366873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46110 (p : Pattern) (guard : d366874 p = 1) : d51287 p ≤ (7 : Int) + d338687 p := by
  cases selected : p 163 with
  | false =>
    have hg : d366873 p = 1 := by simpa only [d366874, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46109 p hg
    simpa only [d366874, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366874, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45286 p hg
    simpa only [d366874, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46111 (p : Pattern) (guard : d366875 p = 1) : d51288 p ≤ (7 : Int) + d338690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d366874 p = 1 := by simpa only [d366875, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46110 p hg
    simpa only [d366875, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366875, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45288 p hg
    simpa only [d366875, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46112 (p : Pattern) (guard : d366876 p = 1) : d51289 p ≤ (7 : Int) + d338691 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366876, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45267 p hg
    simpa only [d366876, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366875 p = 1 := by simpa only [d366876, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46111 p hg
    simpa only [d366876, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46113 (p : Pattern) (guard : d366877 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366876 p = 1 := by simpa only [d366877, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46112 p hg
    simpa only [d366877, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366877, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45291 p hg
    simpa only [d366877, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46114 (p : Pattern) (guard : d366878 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366864 p = 1 := by simpa only [d366878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46092 p hg
    simpa only [d366878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366877 p = 1 := by simpa only [d366878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46113 p hg
    simpa only [d366878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46115 (p : Pattern) (guard : d308523 p = 1) : d47616 p ≤ (7 : Int) + d4 p := by
  cases selected : p 223 with
  | false =>
    have hg : d32698 p = 1 := by simpa only [d308523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46098 p hg
    simpa only [d308523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d308523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45268 p hg
    simpa only [d308523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46116 (p : Pattern) (guard : d308524 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 204 with
  | false =>
    have hg : d308523 p = 1 := by simpa only [d308524, d51204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46115 p hg
    simpa only [d308524, d51204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d308524, d51204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45277 p hg
    simpa only [d308524, d51204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46117 (p : Pattern) (guard : d366879 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 202 with
  | false =>
    have hg : d34782 p = 1 := by simpa only [d366879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46071 p hg
    simpa only [d366879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d308524 p = 1 := by simpa only [d366879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46116 p hg
    simpa only [d366879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46118 (p : Pattern) (guard : d366880 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 201 with
  | false =>
    have hg : d366879 p = 1 := by simpa only [d366880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46117 p hg
    simpa only [d366880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45279 p hg
    simpa only [d366880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46119 (p : Pattern) (guard : d366881 p = 1) : d51269 p ≤ (7 : Int) + d338656 p := by
  cases selected : p 182 with
  | false =>
    have hg : d366880 p = 1 := by simpa only [d366881, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46118 p hg
    simpa only [d366881, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366881, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45282 p hg
    simpa only [d366881, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46120 (p : Pattern) (guard : d366882 p = 1) : d51269 p ≤ (7 : Int) + d338656 p := by
  cases selected : p 180 with
  | false =>
    have hg : d366881 p = 1 := by simpa only [d366882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46119 p hg
    simpa only [d366882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366872 p = 1 := by simpa only [d366882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46108 p hg
    simpa only [d366882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46121 (p : Pattern) (guard : d366883 p = 1) : d51287 p ≤ (7 : Int) + d338687 p := by
  cases selected : p 163 with
  | false =>
    have hg : d366882 p = 1 := by simpa only [d366883, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46120 p hg
    simpa only [d366883, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366883, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45286 p hg
    simpa only [d366883, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46122 (p : Pattern) (guard : d366884 p = 1) : d51288 p ≤ (7 : Int) + d338690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d366883 p = 1 := by simpa only [d366884, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46121 p hg
    simpa only [d366884, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366884, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45288 p hg
    simpa only [d366884, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46123 (p : Pattern) (guard : d366885 p = 1) : d51289 p ≤ (7 : Int) + d338691 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366885, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45267 p hg
    simpa only [d366885, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366884 p = 1 := by simpa only [d366885, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46122 p hg
    simpa only [d366885, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46124 (p : Pattern) (guard : d366886 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366885 p = 1 := by simpa only [d366886, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46123 p hg
    simpa only [d366886, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366886, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45291 p hg
    simpa only [d366886, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46125 (p : Pattern) (guard : d366887 p = 1) : d47616 p ≤ (7 : Int) + d4 p := by
  cases selected : p 223 with
  | false =>
    have hg : d43867 p = 1 := by simpa only [d366887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46078 p hg
    simpa only [d366887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32153 p = 1 := by simpa only [d366887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45793 p hg
    simpa only [d366887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46126 (p : Pattern) (guard : d366888 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 204 with
  | false =>
    have hg : d366887 p = 1 := by simpa only [d366888, d51204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46125 p hg
    simpa only [d366888, d51204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32155 p = 1 := by simpa only [d366888, d51204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46104 p hg
    simpa only [d366888, d51204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46127 (p : Pattern) (guard : d366889 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 202 with
  | false =>
    have hg : d366888 p = 1 := by simpa only [d366889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46126 p hg
    simpa only [d366889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343144 p = 1 := by simpa only [d366889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46084 p hg
    simpa only [d366889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46128 (p : Pattern) (guard : d343638 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 202 with
  | false =>
    have hg : d343144 p = 1 := by simpa only [d343638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46084 p hg
    simpa only [d343638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d343638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45279 p hg
    simpa only [d343638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46129 (p : Pattern) (guard : d366890 p = 1) : d51204 p ≤ (7 : Int) + d4 p := by
  cases selected : p 201 with
  | false =>
    have hg : d366889 p = 1 := by simpa only [d366890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46127 p hg
    simpa only [d366890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d343638 p = 1 := by simpa only [d366890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46128 p hg
    simpa only [d366890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46130 (p : Pattern) (guard : d366891 p = 1) : d51269 p ≤ (7 : Int) + d338656 p := by
  cases selected : p 182 with
  | false =>
    have hg : d366890 p = 1 := by simpa only [d366891, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46129 p hg
    simpa only [d366891, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366891, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45282 p hg
    simpa only [d366891, d51269, d338656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46131 (p : Pattern) (guard : d366892 p = 1) : d51269 p ≤ (7 : Int) + d338656 p := by
  cases selected : p 180 with
  | false =>
    have hg : d366891 p = 1 := by simpa only [d366892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46130 p hg
    simpa only [d366892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45284 p hg
    simpa only [d366892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46132 (p : Pattern) (guard : d366893 p = 1) : d51287 p ≤ (7 : Int) + d338687 p := by
  cases selected : p 163 with
  | false =>
    have hg : d366892 p = 1 := by simpa only [d366893, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46131 p hg
    simpa only [d366893, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366893, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45286 p hg
    simpa only [d366893, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46133 (p : Pattern) (guard : d366894 p = 1) : d51288 p ≤ (7 : Int) + d338690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d366893 p = 1 := by simpa only [d366894, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46132 p hg
    simpa only [d366894, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366894, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45288 p hg
    simpa only [d366894, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46134 (p : Pattern) (guard : d366895 p = 1) : d51289 p ≤ (7 : Int) + d338691 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366895, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45267 p hg
    simpa only [d366895, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366894 p = 1 := by simpa only [d366895, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46133 p hg
    simpa only [d366895, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46135 (p : Pattern) (guard : d366896 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366895 p = 1 := by simpa only [d366896, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46134 p hg
    simpa only [d366896, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366896, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45291 p hg
    simpa only [d366896, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46136 (p : Pattern) (guard : d366897 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366886 p = 1 := by simpa only [d366897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46124 p hg
    simpa only [d366897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366896 p = 1 := by simpa only [d366897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46135 p hg
    simpa only [d366897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46137 (p : Pattern) (guard : d366898 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366878 p = 1 := by simpa only [d366898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46114 p hg
    simpa only [d366898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366897 p = 1 := by simpa only [d366898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46136 p hg
    simpa only [d366898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46138 (p : Pattern) (guard : d366899 p = 1) : d51269 p ≤ (7 : Int) + d338656 p := by
  cases selected : p 180 with
  | false =>
    have hg : d366867 p = 1 := by simpa only [d366899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46097 p hg
    simpa only [d366899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366891 p = 1 := by simpa only [d366899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46130 p hg
    simpa only [d366899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46139 (p : Pattern) (guard : d366900 p = 1) : d51287 p ≤ (7 : Int) + d338687 p := by
  cases selected : p 163 with
  | false =>
    have hg : d366899 p = 1 := by simpa only [d366900, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46138 p hg
    simpa only [d366900, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366900, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45286 p hg
    simpa only [d366900, d51287, d338687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46140 (p : Pattern) (guard : d366901 p = 1) : d51288 p ≤ (7 : Int) + d338690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d366900 p = 1 := by simpa only [d366901, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46139 p hg
    simpa only [d366901, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366901, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45288 p hg
    simpa only [d366901, d51288, d338690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46141 (p : Pattern) (guard : d366902 p = 1) : d51289 p ≤ (7 : Int) + d338691 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366902, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45267 p hg
    simpa only [d366902, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366901 p = 1 := by simpa only [d366902, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46140 p hg
    simpa only [d366902, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46142 (p : Pattern) (guard : d366903 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366902 p = 1 := by simpa only [d366903, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46141 p hg
    simpa only [d366903, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366903, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45291 p hg
    simpa only [d366903, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46143 (p : Pattern) (guard : d366904 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366903 p = 1 := by simpa only [d366904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46142 p hg
    simpa only [d366904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366896 p = 1 := by simpa only [d366904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46135 p hg
    simpa only [d366904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46144 (p : Pattern) (guard : d366905 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366896 p = 1 := by simpa only [d366905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46135 p hg
    simpa only [d366905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45293 p hg
    simpa only [d366905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46145 (p : Pattern) (guard : d366906 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366904 p = 1 := by simpa only [d366906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46143 p hg
    simpa only [d366906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366905 p = 1 := by simpa only [d366906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46144 p hg
    simpa only [d366906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46146 (p : Pattern) (guard : d366907 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 157 with
  | false =>
    have hg : d366898 p = 1 := by simpa only [d366907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46137 p hg
    simpa only [d366907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366906 p = 1 := by simpa only [d366907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46145 p hg
    simpa only [d366907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46147 (p : Pattern) (guard : d366908 p = 1) : d51294 p ≤ (7 : Int) + d338713 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366908, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45266 p hg
    simpa only [d366908, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366907 p = 1 := by simpa only [d366908, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46146 p hg
    simpa only [d366908, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46148 (p : Pattern) (guard : d366909 p = 1) : d51314 p ≤ (7 : Int) + d338714 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366909, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45265 p hg
    simpa only [d366909, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366908 p = 1 := by simpa only [d366909, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46147 p hg
    simpa only [d366909, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46149 (p : Pattern) (guard : d366910 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366905 p = 1 := by simpa only [d366910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46144 p hg
    simpa only [d366910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45293 p hg
    simpa only [d366910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46150 (p : Pattern) (guard : d366911 p = 1) : d51293 p ≤ (7 : Int) + d338712 p := by
  cases selected : p 157 with
  | false =>
    have hg : d366906 p = 1 := by simpa only [d366911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46145 p hg
    simpa only [d366911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366910 p = 1 := by simpa only [d366911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46149 p hg
    simpa only [d366911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46151 (p : Pattern) (guard : d366912 p = 1) : d51294 p ≤ (7 : Int) + d338713 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366912, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45266 p hg
    simpa only [d366912, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366911 p = 1 := by simpa only [d366912, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46150 p hg
    simpa only [d366912, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46152 (p : Pattern) (guard : d366913 p = 1) : d51314 p ≤ (7 : Int) + d338714 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366913, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45265 p hg
    simpa only [d366913, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366912 p = 1 := by simpa only [d366913, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46151 p hg
    simpa only [d366913, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46153 (p : Pattern) (guard : d366914 p = 1) : d51314 p ≤ (7 : Int) + d338714 p := by
  cases selected : p 136 with
  | false =>
    have hg : d366909 p = 1 := by simpa only [d366914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46148 p hg
    simpa only [d366914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366913 p = 1 := by simpa only [d366914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46152 p hg
    simpa only [d366914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46154 (p : Pattern) (guard : d366915 p = 1) : d51314 p ≤ (7 : Int) + d338714 p := by
  cases selected : p 136 with
  | false =>
    have hg : d366913 p = 1 := by simpa only [d366915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46152 p hg
    simpa only [d366915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45299 p hg
    simpa only [d366915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46155 (p : Pattern) (guard : d366916 p = 1) : d51314 p ≤ (7 : Int) + d338714 p := by
  cases selected : p 135 with
  | false =>
    have hg : d366914 p = 1 := by simpa only [d366916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46153 p hg
    simpa only [d366916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366915 p = 1 := by simpa only [d366916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46154 p hg
    simpa only [d366916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46156 (p : Pattern) (guard : d366917 p = 1) : d51314 p ≤ (7 : Int) + d338714 p := by
  cases selected : p 119 with
  | false =>
    have hg : d366916 p = 1 := by simpa only [d366917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46155 p hg
    simpa only [d366917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45299 p hg
    simpa only [d366917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46157 (p : Pattern) (guard : d366918 p = 1) : d51316 p ≤ (7 : Int) + d338726 p := by
  cases selected : p 116 with
  | false =>
    have hg : d366917 p = 1 := by simpa only [d366918, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46156 p hg
    simpa only [d366918, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366918, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45303 p hg
    simpa only [d366918, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46158 (p : Pattern) (guard : d366919 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366919, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45264 p hg
    simpa only [d366919, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366918 p = 1 := by simpa only [d366919, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46157 p hg
    simpa only [d366919, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46159 (p : Pattern) (guard : d366920 p = 1) : d51314 p ≤ (7 : Int) + d338714 p := by
  cases selected : p 135 with
  | false =>
    have hg : d366915 p = 1 := by simpa only [d366920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46154 p hg
    simpa only [d366920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45299 p hg
    simpa only [d366920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46160 (p : Pattern) (guard : d366921 p = 1) : d51314 p ≤ (7 : Int) + d338714 p := by
  cases selected : p 119 with
  | false =>
    have hg : d366920 p = 1 := by simpa only [d366921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46159 p hg
    simpa only [d366921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45299 p hg
    simpa only [d366921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46161 (p : Pattern) (guard : d366922 p = 1) : d51316 p ≤ (7 : Int) + d338726 p := by
  cases selected : p 116 with
  | false =>
    have hg : d366921 p = 1 := by simpa only [d366922, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46160 p hg
    simpa only [d366922, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366922, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45303 p hg
    simpa only [d366922, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46162 (p : Pattern) (guard : d366923 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366923, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45264 p hg
    simpa only [d366923, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366922 p = 1 := by simpa only [d366923, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46161 p hg
    simpa only [d366923, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46163 (p : Pattern) (guard : d366924 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366919 p = 1 := by simpa only [d366924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46158 p hg
    simpa only [d366924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366923 p = 1 := by simpa only [d366924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46162 p hg
    simpa only [d366924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46164 (p : Pattern) (guard : d366925 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366924 p = 1 := by simpa only [d366925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46163 p hg
    simpa only [d366925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46165 (p : Pattern) (guard : d366926 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366925 p = 1 := by simpa only [d366926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46164 p hg
    simpa only [d366926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46166 (p : Pattern) (guard : d366927 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366926 p = 1 := by simpa only [d366927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46165 p hg
    simpa only [d366927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46167 (p : Pattern) (guard : d366928 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366923 p = 1 := by simpa only [d366928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46162 p hg
    simpa only [d366928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46168 (p : Pattern) (guard : d366929 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366928 p = 1 := by simpa only [d366929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46167 p hg
    simpa only [d366929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46169 (p : Pattern) (guard : d366930 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366929 p = 1 := by simpa only [d366930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46168 p hg
    simpa only [d366930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46170 (p : Pattern) (guard : d366931 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366930 p = 1 := by simpa only [d366931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46169 p hg
    simpa only [d366931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46171 (p : Pattern) (guard : d366932 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366927 p = 1 := by simpa only [d366932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46166 p hg
    simpa only [d366932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366931 p = 1 := by simpa only [d366932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46170 p hg
    simpa only [d366932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46172 (p : Pattern) (guard : d366933 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366932 p = 1 := by simpa only [d366933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46171 p hg
    simpa only [d366933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46173 (p : Pattern) (guard : d366934 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366933 p = 1 := by simpa only [d366934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46172 p hg
    simpa only [d366934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46174 (p : Pattern) (guard : d366935 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366934 p = 1 := by simpa only [d366935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46173 p hg
    simpa only [d366935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46175 (p : Pattern) (guard : d366936 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366935 p = 1 := by simpa only [d366936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46174 p hg
    simpa only [d366936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46176 (p : Pattern) (guard : d366937 p = 1) : d51331 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366937, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d366937, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366936 p = 1 := by simpa only [d366937, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46175 p hg
    simpa only [d366937, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46177 (p : Pattern) (guard : d366919 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366919, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45316 p hg
    simpa only [d366919, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366918 p = 1 := by simpa only [d366919, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46157 p hg
    simpa only [d366919, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46178 (p : Pattern) (guard : d366923 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366923, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45316 p hg
    simpa only [d366923, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366922 p = 1 := by simpa only [d366923, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46161 p hg
    simpa only [d366923, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46179 (p : Pattern) (guard : d366924 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366919 p = 1 := by simpa only [d366924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46177 p hg
    simpa only [d366924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366923 p = 1 := by simpa only [d366924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46178 p hg
    simpa only [d366924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46180 (p : Pattern) (guard : d366925 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366924 p = 1 := by simpa only [d366925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46179 p hg
    simpa only [d366925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d366925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46181 (p : Pattern) (guard : d366926 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366925 p = 1 := by simpa only [d366926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46180 p hg
    simpa only [d366926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d366926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46182 (p : Pattern) (guard : d366927 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d366927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366926 p = 1 := by simpa only [d366927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46181 p hg
    simpa only [d366927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46183 (p : Pattern) (guard : d366928 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366923 p = 1 := by simpa only [d366928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46178 p hg
    simpa only [d366928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d366928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46184 (p : Pattern) (guard : d366929 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366928 p = 1 := by simpa only [d366929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46183 p hg
    simpa only [d366929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d366929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46185 (p : Pattern) (guard : d366930 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366929 p = 1 := by simpa only [d366930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46184 p hg
    simpa only [d366930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d366930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46186 (p : Pattern) (guard : d366931 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d366931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366930 p = 1 := by simpa only [d366931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46185 p hg
    simpa only [d366931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46187 (p : Pattern) (guard : d366932 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366927 p = 1 := by simpa only [d366932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46182 p hg
    simpa only [d366932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366931 p = 1 := by simpa only [d366932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46186 p hg
    simpa only [d366932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46188 (p : Pattern) (guard : d366933 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d366933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366932 p = 1 := by simpa only [d366933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46187 p hg
    simpa only [d366933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46189 (p : Pattern) (guard : d366934 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366933 p = 1 := by simpa only [d366934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46188 p hg
    simpa only [d366934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d366934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46190 (p : Pattern) (guard : d366935 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d366935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366934 p = 1 := by simpa only [d366935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46189 p hg
    simpa only [d366935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46191 (p : Pattern) (guard : d366936 p = 1) : d51317 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45262 p hg
    simpa only [d366936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366935 p = 1 := by simpa only [d366936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46190 p hg
    simpa only [d366936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46192 (p : Pattern) (guard : d366940 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366926 p = 1 := by simpa only [d366940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46165 p hg
    simpa only [d366940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46193 (p : Pattern) (guard : d366941 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366930 p = 1 := by simpa only [d366941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46169 p hg
    simpa only [d366941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46194 (p : Pattern) (guard : d366942 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d366940 p = 1 := by simpa only [d366942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46192 p hg
    simpa only [d366942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366941 p = 1 := by simpa only [d366942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46193 p hg
    simpa only [d366942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46195 (p : Pattern) (guard : d366943 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366942 p = 1 := by simpa only [d366943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46194 p hg
    simpa only [d366943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46196 (p : Pattern) (guard : d366944 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d366943 p = 1 := by simpa only [d366944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46195 p hg
    simpa only [d366944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46197 (p : Pattern) (guard : d366945 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366944 p = 1 := by simpa only [d366945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46196 p hg
    simpa only [d366945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46198 (p : Pattern) (guard : d366946 p = 1) : d51330 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45263 p hg
    simpa only [d366946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366945 p = 1 := by simpa only [d366946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46197 p hg
    simpa only [d366946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46199 (p : Pattern) (guard : d366947 p = 1) : d51331 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d366936 p = 1 := by simpa only [d366947, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46191 p hg
    simpa only [d366947, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366946 p = 1 := by simpa only [d366947, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46198 p hg
    simpa only [d366947, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46200 (p : Pattern) (guard : d366948 p = 1) : d51331 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 70 with
  | false =>
    have hg : d366937 p = 1 := by simpa only [d366948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46176 p hg
    simpa only [d366948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366947 p = 1 := by simpa only [d366948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46199 p hg
    simpa only [d366948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46201 (p : Pattern) (guard : d366949 p = 1) : d51331 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 69 with
  | false =>
    have hg : d366948 p = 1 := by simpa only [d366949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46200 p hg
    simpa only [d366949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45261 p hg
    simpa only [d366949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46202 (p : Pattern) (guard : d367496 p = 1) : d51331 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 51 with
  | false =>
    have hg : d366949 p = 1 := by simpa only [d367496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46201 p hg
    simpa only [d367496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d367496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45261 p hg
    simpa only [d367496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46203 (p : Pattern) (guard : d367497 p = 1) : d51331 p ≤ (7 : Int) + d338727 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d367497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45261 p hg
    simpa only [d367497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d367496 p = 1 := by simpa only [d367497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46202 p hg
    simpa only [d367497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46204 (p : Pattern) (guard : d366862 p = 1) : d51447 p ≤ (7 : Int) + d338755 p := by
  have ha := bounds51447 p
  have hb := bounds338755 p
  omega
theorem compare46205 (p : Pattern) (guard : d366863 p = 1) : d51448 p ≤ (7 : Int) + d338756 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366863, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45343 p hg
    simpa only [d366863, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366862 p = 1 := by simpa only [d366863, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46204 p hg
    simpa only [d366863, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46206 (p : Pattern) (guard : d366864 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366863 p = 1 := by simpa only [d366864, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46205 p hg
    simpa only [d366864, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366864, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45346 p hg
    simpa only [d366864, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46207 (p : Pattern) (guard : d366875 p = 1) : d51447 p ≤ (7 : Int) + d338755 p := by
  have ha := bounds51447 p
  have hb := bounds338755 p
  omega
theorem compare46208 (p : Pattern) (guard : d366876 p = 1) : d51448 p ≤ (7 : Int) + d338756 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366876, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45343 p hg
    simpa only [d366876, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366875 p = 1 := by simpa only [d366876, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46207 p hg
    simpa only [d366876, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46209 (p : Pattern) (guard : d366877 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366876 p = 1 := by simpa only [d366877, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46208 p hg
    simpa only [d366877, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366877, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45346 p hg
    simpa only [d366877, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46210 (p : Pattern) (guard : d366878 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366864 p = 1 := by simpa only [d366878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46206 p hg
    simpa only [d366878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366877 p = 1 := by simpa only [d366878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46209 p hg
    simpa only [d366878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46211 (p : Pattern) (guard : d366884 p = 1) : d51447 p ≤ (7 : Int) + d338755 p := by
  have ha := bounds51447 p
  have hb := bounds338755 p
  omega
theorem compare46212 (p : Pattern) (guard : d366885 p = 1) : d51448 p ≤ (7 : Int) + d338756 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366885, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45343 p hg
    simpa only [d366885, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366884 p = 1 := by simpa only [d366885, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46211 p hg
    simpa only [d366885, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46213 (p : Pattern) (guard : d366886 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366885 p = 1 := by simpa only [d366886, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46212 p hg
    simpa only [d366886, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366886, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45346 p hg
    simpa only [d366886, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46214 (p : Pattern) (guard : d366894 p = 1) : d51447 p ≤ (7 : Int) + d338755 p := by
  have ha := bounds51447 p
  have hb := bounds338755 p
  omega
theorem compare46215 (p : Pattern) (guard : d366895 p = 1) : d51448 p ≤ (7 : Int) + d338756 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366895, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45343 p hg
    simpa only [d366895, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366894 p = 1 := by simpa only [d366895, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46214 p hg
    simpa only [d366895, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46216 (p : Pattern) (guard : d366896 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366895 p = 1 := by simpa only [d366896, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46215 p hg
    simpa only [d366896, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366896, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45346 p hg
    simpa only [d366896, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46217 (p : Pattern) (guard : d366897 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366886 p = 1 := by simpa only [d366897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46213 p hg
    simpa only [d366897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366896 p = 1 := by simpa only [d366897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46216 p hg
    simpa only [d366897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46218 (p : Pattern) (guard : d366898 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366878 p = 1 := by simpa only [d366898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46210 p hg
    simpa only [d366898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366897 p = 1 := by simpa only [d366898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46217 p hg
    simpa only [d366898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46219 (p : Pattern) (guard : d366901 p = 1) : d51447 p ≤ (7 : Int) + d338755 p := by
  have ha := bounds51447 p
  have hb := bounds338755 p
  omega
theorem compare46220 (p : Pattern) (guard : d366902 p = 1) : d51448 p ≤ (7 : Int) + d338756 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366902, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45343 p hg
    simpa only [d366902, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366901 p = 1 := by simpa only [d366902, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46219 p hg
    simpa only [d366902, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46221 (p : Pattern) (guard : d366903 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d366902 p = 1 := by simpa only [d366903, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46220 p hg
    simpa only [d366903, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366903, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45346 p hg
    simpa only [d366903, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46222 (p : Pattern) (guard : d366904 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366903 p = 1 := by simpa only [d366904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46221 p hg
    simpa only [d366904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366896 p = 1 := by simpa only [d366904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46216 p hg
    simpa only [d366904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46223 (p : Pattern) (guard : d366905 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 159 with
  | false =>
    have hg : d366896 p = 1 := by simpa only [d366905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46216 p hg
    simpa only [d366905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45348 p hg
    simpa only [d366905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46224 (p : Pattern) (guard : d366906 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366904 p = 1 := by simpa only [d366906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46222 p hg
    simpa only [d366906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366905 p = 1 := by simpa only [d366906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46223 p hg
    simpa only [d366906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46225 (p : Pattern) (guard : d366907 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 157 with
  | false =>
    have hg : d366898 p = 1 := by simpa only [d366907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46218 p hg
    simpa only [d366907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366906 p = 1 := by simpa only [d366907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46224 p hg
    simpa only [d366907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46226 (p : Pattern) (guard : d366908 p = 1) : d51453 p ≤ (7 : Int) + d338775 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366908, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45342 p hg
    simpa only [d366908, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366907 p = 1 := by simpa only [d366908, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46225 p hg
    simpa only [d366908, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46227 (p : Pattern) (guard : d366909 p = 1) : d51465 p ≤ (7 : Int) + d338776 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366909, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45341 p hg
    simpa only [d366909, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366908 p = 1 := by simpa only [d366909, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46226 p hg
    simpa only [d366909, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46228 (p : Pattern) (guard : d366910 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 158 with
  | false =>
    have hg : d366905 p = 1 := by simpa only [d366910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46223 p hg
    simpa only [d366910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45348 p hg
    simpa only [d366910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46229 (p : Pattern) (guard : d366911 p = 1) : d51452 p ≤ (7 : Int) + d338774 p := by
  cases selected : p 157 with
  | false =>
    have hg : d366906 p = 1 := by simpa only [d366911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46224 p hg
    simpa only [d366911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366910 p = 1 := by simpa only [d366911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46228 p hg
    simpa only [d366911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46230 (p : Pattern) (guard : d366912 p = 1) : d51453 p ≤ (7 : Int) + d338775 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366912, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45342 p hg
    simpa only [d366912, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366911 p = 1 := by simpa only [d366912, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46229 p hg
    simpa only [d366912, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46231 (p : Pattern) (guard : d366913 p = 1) : d51465 p ≤ (7 : Int) + d338776 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366913, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45341 p hg
    simpa only [d366913, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366912 p = 1 := by simpa only [d366913, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46230 p hg
    simpa only [d366913, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46232 (p : Pattern) (guard : d366914 p = 1) : d51465 p ≤ (7 : Int) + d338776 p := by
  cases selected : p 136 with
  | false =>
    have hg : d366909 p = 1 := by simpa only [d366914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46227 p hg
    simpa only [d366914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366913 p = 1 := by simpa only [d366914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46231 p hg
    simpa only [d366914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46233 (p : Pattern) (guard : d366915 p = 1) : d51465 p ≤ (7 : Int) + d338776 p := by
  cases selected : p 136 with
  | false =>
    have hg : d366913 p = 1 := by simpa only [d366915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46231 p hg
    simpa only [d366915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45354 p hg
    simpa only [d366915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46234 (p : Pattern) (guard : d366916 p = 1) : d51465 p ≤ (7 : Int) + d338776 p := by
  cases selected : p 135 with
  | false =>
    have hg : d366914 p = 1 := by simpa only [d366916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46232 p hg
    simpa only [d366916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366915 p = 1 := by simpa only [d366916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46233 p hg
    simpa only [d366916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46235 (p : Pattern) (guard : d366917 p = 1) : d51465 p ≤ (7 : Int) + d338776 p := by
  cases selected : p 119 with
  | false =>
    have hg : d366916 p = 1 := by simpa only [d366917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46234 p hg
    simpa only [d366917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45354 p hg
    simpa only [d366917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46236 (p : Pattern) (guard : d366918 p = 1) : d51467 p ≤ (7 : Int) + d338784 p := by
  cases selected : p 116 with
  | false =>
    have hg : d366917 p = 1 := by simpa only [d366918, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46235 p hg
    simpa only [d366918, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366918, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45358 p hg
    simpa only [d366918, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46237 (p : Pattern) (guard : d366919 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366919, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45340 p hg
    simpa only [d366919, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366918 p = 1 := by simpa only [d366919, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46236 p hg
    simpa only [d366919, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46238 (p : Pattern) (guard : d366920 p = 1) : d51465 p ≤ (7 : Int) + d338776 p := by
  cases selected : p 135 with
  | false =>
    have hg : d366915 p = 1 := by simpa only [d366920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46233 p hg
    simpa only [d366920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45354 p hg
    simpa only [d366920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46239 (p : Pattern) (guard : d366921 p = 1) : d51465 p ≤ (7 : Int) + d338776 p := by
  cases selected : p 119 with
  | false =>
    have hg : d366920 p = 1 := by simpa only [d366921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46238 p hg
    simpa only [d366921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45354 p hg
    simpa only [d366921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46240 (p : Pattern) (guard : d366922 p = 1) : d51467 p ≤ (7 : Int) + d338784 p := by
  cases selected : p 116 with
  | false =>
    have hg : d366921 p = 1 := by simpa only [d366922, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46239 p hg
    simpa only [d366922, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366922, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45358 p hg
    simpa only [d366922, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46241 (p : Pattern) (guard : d366923 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d366923, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45340 p hg
    simpa only [d366923, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366922 p = 1 := by simpa only [d366923, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46240 p hg
    simpa only [d366923, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46242 (p : Pattern) (guard : d366924 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366919 p = 1 := by simpa only [d366924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46237 p hg
    simpa only [d366924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d366923 p = 1 := by simpa only [d366924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46241 p hg
    simpa only [d366924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46243 (p : Pattern) (guard : d366925 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366924 p = 1 := by simpa only [d366925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46242 p hg
    simpa only [d366925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d366925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46244 (p : Pattern) (guard : d366926 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366925 p = 1 := by simpa only [d366926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46243 p hg
    simpa only [d366926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d366926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46245 (p : Pattern) (guard : d366940 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366926 p = 1 := by simpa only [d366940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46244 p hg
    simpa only [d366940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d366940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46246 (p : Pattern) (guard : d366928 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 113 with
  | false =>
    have hg : d366923 p = 1 := by simpa only [d366928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46241 p hg
    simpa only [d366928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d366928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46247 (p : Pattern) (guard : d366929 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 96 with
  | false =>
    have hg : d366928 p = 1 := by simpa only [d366929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46246 p hg
    simpa only [d366929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d366929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46248 (p : Pattern) (guard : d366930 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 95 with
  | false =>
    have hg : d366929 p = 1 := by simpa only [d366930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46247 p hg
    simpa only [d366930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d366930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare46249 (p : Pattern) (guard : d366941 p = 1) : d51468 p ≤ (7 : Int) + d338785 p := by
  cases selected : p 93 with
  | false =>
    have hg : d366930 p = 1 := by simpa only [d366941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare46248 p hg
    simpa only [d366941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d366941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45339 p hg
    simpa only [d366941, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
