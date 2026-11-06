import NetHack.Soko22Hazard87.Compare123
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare31000 (p : Pattern) (guard : d258909 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d258909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258908 p = 1 := by simpa only [d258909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30999 p hg
    simpa only [d258909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31001 (p : Pattern) (guard : d258910 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d258910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258909 p = 1 := by simpa only [d258910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31000 p hg
    simpa only [d258910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31002 (p : Pattern) (guard : d258848 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d258831 p = 1 := by simpa only [d258848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30994 p hg
    simpa only [d258848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d258848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31003 (p : Pattern) (guard : d258849 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d258848 p = 1 := by simpa only [d258849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31002 p hg
    simpa only [d258849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258726 p = 1 := by simpa only [d258849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30819 p hg
    simpa only [d258849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31004 (p : Pattern) (guard : d258913 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d258913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258849 p = 1 := by simpa only [d258913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31003 p hg
    simpa only [d258913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31005 (p : Pattern) (guard : d258914 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d258913 p = 1 := by simpa only [d258914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31004 p hg
    simpa only [d258914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d258914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31006 (p : Pattern) (guard : d258915 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d258915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258914 p = 1 := by simpa only [d258915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31005 p hg
    simpa only [d258915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31007 (p : Pattern) (guard : d258916 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d258916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258915 p = 1 := by simpa only [d258916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31006 p hg
    simpa only [d258916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31008 (p : Pattern) (guard : d258917 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 71 with
  | false =>
    have hg : d258909 p = 1 := by simpa only [d258917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31000 p hg
    simpa only [d258917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258916 p = 1 := by simpa only [d258917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31007 p hg
    simpa only [d258917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31009 (p : Pattern) (guard : d258918 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 70 with
  | false =>
    have hg : d258910 p = 1 := by simpa only [d258918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31001 p hg
    simpa only [d258918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258917 p = 1 := by simpa only [d258918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31008 p hg
    simpa only [d258918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31010 (p : Pattern) (guard : d258919 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 69 with
  | false =>
    have hg : d258918 p = 1 := by simpa only [d258919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31009 p hg
    simpa only [d258919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d258919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31011 (p : Pattern) (guard : d260105 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 51 with
  | false =>
    have hg : d258919 p = 1 := by simpa only [d260105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31010 p hg
    simpa only [d260105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d260105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31012 (p : Pattern) (guard : d260106 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d260106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260105 p = 1 := by simpa only [d260106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31011 p hg
    simpa only [d260106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31013 (p : Pattern) (guard : d307 p = 1) : d5 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d307, d47705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30837 p hg
    simpa only [d307, d47705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d127 p = 1 := by simpa only [d307, d47705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8343 p hg
    simpa only [d307, d47705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31014 (p : Pattern) (guard : d1997 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 246 with
  | false =>
    have hg : d307 p = 1 := by simpa only [d1997, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31013 p hg
    simpa only [d1997, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1997, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30839 p hg
    simpa only [d1997, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31015 (p : Pattern) (guard : d258806 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d258806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31014 p hg
    simpa only [d258806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46864 p = 1 := by simpa only [d258806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30840 p hg
    simpa only [d258806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31016 (p : Pattern) (guard : d258807 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 225 with
  | false =>
    have hg : d258806 p = 1 := by simpa only [d258807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31015 p hg
    simpa only [d258807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46865 p = 1 := by simpa only [d258807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30841 p hg
    simpa only [d258807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31017 (p : Pattern) (guard : d258808 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30836 p hg
    simpa only [d258808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258807 p = 1 := by simpa only [d258808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31016 p hg
    simpa only [d258808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31018 (p : Pattern) (guard : d258809 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 223 with
  | false =>
    have hg : d258808 p = 1 := by simpa only [d258809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31017 p hg
    simpa only [d258809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30836 p hg
    simpa only [d258809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31019 (p : Pattern) (guard : d258810 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258809 p = 1 := by simpa only [d258810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31018 p hg
    simpa only [d258810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30836 p hg
    simpa only [d258810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31020 (p : Pattern) (guard : d258811 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 202 with
  | false =>
    have hg : d258810 p = 1 := by simpa only [d258811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31019 p hg
    simpa only [d258811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30836 p hg
    simpa only [d258811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31021 (p : Pattern) (guard : d258812 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 201 with
  | false =>
    have hg : d258811 p = 1 := by simpa only [d258812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31020 p hg
    simpa only [d258812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258698 p = 1 := by simpa only [d258812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30846 p hg
    simpa only [d258812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31022 (p : Pattern) (guard : d258813 p = 1) : d47708 p ≤ (-2 : Int) + d253351 p := by
  cases selected : p 182 with
  | false =>
    have hg : d258812 p = 1 := by simpa only [d258813, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31021 p hg
    simpa only [d258813, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258813, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30848 p hg
    simpa only [d258813, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31023 (p : Pattern) (guard : d258814 p = 1) : d47708 p ≤ (-2 : Int) + d253351 p := by
  cases selected : p 180 with
  | false =>
    have hg : d258813 p = 1 := by simpa only [d258814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31022 p hg
    simpa only [d258814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258700 p = 1 := by simpa only [d258814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30849 p hg
    simpa only [d258814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31024 (p : Pattern) (guard : d258815 p = 1) : d47735 p ≤ (-2 : Int) + d253374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d258814 p = 1 := by simpa only [d258815, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31023 p hg
    simpa only [d258815, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258815, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30852 p hg
    simpa only [d258815, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31025 (p : Pattern) (guard : d258816 p = 1) : d47736 p ≤ (-2 : Int) + d253375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d258815 p = 1 := by simpa only [d258816, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31024 p hg
    simpa only [d258816, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258816, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d258816, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31026 (p : Pattern) (guard : d258817 p = 1) : d47737 p ≤ (-2 : Int) + d253376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258817, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30835 p hg
    simpa only [d258817, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258816 p = 1 := by simpa only [d258817, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31025 p hg
    simpa only [d258817, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31027 (p : Pattern) (guard : d258818 p = 1) : d47755 p ≤ (-2 : Int) + d253394 p := by
  cases selected : p 160 with
  | false =>
    have hg : d258817 p = 1 := by simpa only [d258818, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31026 p hg
    simpa only [d258818, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258818, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30856 p hg
    simpa only [d258818, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31028 (p : Pattern) (guard : d258819 p = 1) : d47755 p ≤ (-2 : Int) + d253394 p := by
  cases selected : p 159 with
  | false =>
    have hg : d258818 p = 1 := by simpa only [d258819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31027 p hg
    simpa only [d258819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258705 p = 1 := by simpa only [d258819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30857 p hg
    simpa only [d258819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31029 (p : Pattern) (guard : d258820 p = 1) : d47755 p ≤ (-2 : Int) + d253394 p := by
  cases selected : p 158 with
  | false =>
    have hg : d258819 p = 1 := by simpa only [d258820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31028 p hg
    simpa only [d258820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258706 p = 1 := by simpa only [d258820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30859 p hg
    simpa only [d258820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31030 (p : Pattern) (guard : d258821 p = 1) : d47755 p ≤ (-2 : Int) + d253394 p := by
  cases selected : p 157 with
  | false =>
    have hg : d258820 p = 1 := by simpa only [d258821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31029 p hg
    simpa only [d258821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258707 p = 1 := by simpa only [d258821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30860 p hg
    simpa only [d258821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31031 (p : Pattern) (guard : d258822 p = 1) : d47756 p ≤ (-2 : Int) + d253395 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258822, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30834 p hg
    simpa only [d258822, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258821 p = 1 := by simpa only [d258822, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31030 p hg
    simpa only [d258822, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31032 (p : Pattern) (guard : d258823 p = 1) : d47757 p ≤ (-2 : Int) + d253396 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258823, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30833 p hg
    simpa only [d258823, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258822 p = 1 := by simpa only [d258823, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31031 p hg
    simpa only [d258823, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31033 (p : Pattern) (guard : d258824 p = 1) : d47757 p ≤ (-2 : Int) + d253396 p := by
  cases selected : p 136 with
  | false =>
    have hg : d258823 p = 1 := by simpa only [d258824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31032 p hg
    simpa only [d258824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258710 p = 1 := by simpa only [d258824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30863 p hg
    simpa only [d258824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31034 (p : Pattern) (guard : d258825 p = 1) : d47757 p ≤ (-2 : Int) + d253396 p := by
  cases selected : p 135 with
  | false =>
    have hg : d258824 p = 1 := by simpa only [d258825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31033 p hg
    simpa only [d258825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258711 p = 1 := by simpa only [d258825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30865 p hg
    simpa only [d258825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31035 (p : Pattern) (guard : d258826 p = 1) : d47757 p ≤ (-2 : Int) + d253396 p := by
  cases selected : p 119 with
  | false =>
    have hg : d258825 p = 1 := by simpa only [d258826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31034 p hg
    simpa only [d258826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30864 p hg
    simpa only [d258826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31036 (p : Pattern) (guard : d258827 p = 1) : d47765 p ≤ (-2 : Int) + d253404 p := by
  cases selected : p 116 with
  | false =>
    have hg : d258826 p = 1 := by simpa only [d258827, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31035 p hg
    simpa only [d258827, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258827, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30868 p hg
    simpa only [d258827, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31037 (p : Pattern) (guard : d258828 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258828, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30832 p hg
    simpa only [d258828, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258827 p = 1 := by simpa only [d258828, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31036 p hg
    simpa only [d258828, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31038 (p : Pattern) (guard : d258829 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 113 with
  | false =>
    have hg : d258828 p = 1 := by simpa only [d258829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31037 p hg
    simpa only [d258829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258715 p = 1 := by simpa only [d258829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30870 p hg
    simpa only [d258829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31039 (p : Pattern) (guard : d258830 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 96 with
  | false =>
    have hg : d258829 p = 1 := by simpa only [d258830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31038 p hg
    simpa only [d258830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d258830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31040 (p : Pattern) (guard : d258831 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 95 with
  | false =>
    have hg : d258830 p = 1 := by simpa only [d258831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31039 p hg
    simpa only [d258831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d258831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31041 (p : Pattern) (guard : d258848 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 93 with
  | false =>
    have hg : d258831 p = 1 := by simpa only [d258848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31040 p hg
    simpa only [d258848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d258848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31042 (p : Pattern) (guard : d258849 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 91 with
  | false =>
    have hg : d258848 p = 1 := by simpa only [d258849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31041 p hg
    simpa only [d258849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258726 p = 1 := by simpa only [d258849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30874 p hg
    simpa only [d258849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31043 (p : Pattern) (guard : d258913 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d258913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258849 p = 1 := by simpa only [d258913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31042 p hg
    simpa only [d258913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31044 (p : Pattern) (guard : d258914 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 89 with
  | false =>
    have hg : d258913 p = 1 := by simpa only [d258914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31043 p hg
    simpa only [d258914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d258914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31045 (p : Pattern) (guard : d258915 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d258915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258914 p = 1 := by simpa only [d258915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31044 p hg
    simpa only [d258915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31046 (p : Pattern) (guard : d258916 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d258916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258915 p = 1 := by simpa only [d258916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31045 p hg
    simpa only [d258916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31047 (p : Pattern) (guard : d260107 p = 1) : d47767 p ≤ (-2 : Int) + d253406 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260107, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d260107, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258916 p = 1 := by simpa only [d260107, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31046 p hg
    simpa only [d260107, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31048 (p : Pattern) (guard : d260108 p = 1) : d47767 p ≤ (-2 : Int) + d253406 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30830 p hg
    simpa only [d260108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260107 p = 1 := by simpa only [d260108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31047 p hg
    simpa only [d260108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31049 (p : Pattern) (guard : d260109 p = 1) : d47767 p ≤ (-2 : Int) + d253406 p := by
  cases selected : p 69 with
  | false =>
    have hg : d260108 p = 1 := by simpa only [d260109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31048 p hg
    simpa only [d260109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30830 p hg
    simpa only [d260109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31050 (p : Pattern) (guard : d260110 p = 1) : d47767 p ≤ (-2 : Int) + d253406 p := by
  cases selected : p 51 with
  | false =>
    have hg : d260109 p = 1 := by simpa only [d260110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31049 p hg
    simpa only [d260110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30830 p hg
    simpa only [d260110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31051 (p : Pattern) (guard : d260111 p = 1) : d47767 p ≤ (-2 : Int) + d253406 p := by
  cases selected : p 50 with
  | false =>
    have hg : d260110 p = 1 := by simpa only [d260111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31050 p hg
    simpa only [d260111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30830 p hg
    simpa only [d260111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31052 (p : Pattern) (guard : d260112 p = 1) : d47768 p ≤ (-2 : Int) + d253407 p := by
  cases selected : p 49 with
  | false =>
    have hg : d260106 p = 1 := by simpa only [d260112, d47768, d253407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31012 p hg
    simpa only [d260112, d47768, d253407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260111 p = 1 := by simpa only [d260112, d47768, d253407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31051 p hg
    simpa only [d260112, d47768, d253407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31053 (p : Pattern) (guard : d307 p = 1) : d2 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d307, d47629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30892 p hg
    simpa only [d307, d47629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d127 p = 1 := by simpa only [d307, d47629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8394 p hg
    simpa only [d307, d47629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31054 (p : Pattern) (guard : d1997 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 246 with
  | false =>
    have hg : d307 p = 1 := by simpa only [d1997, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31053 p hg
    simpa only [d1997, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1997, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30894 p hg
    simpa only [d1997, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31055 (p : Pattern) (guard : d258806 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d258806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31054 p hg
    simpa only [d258806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46864 p = 1 := by simpa only [d258806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30895 p hg
    simpa only [d258806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31056 (p : Pattern) (guard : d258807 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 225 with
  | false =>
    have hg : d258806 p = 1 := by simpa only [d258807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31055 p hg
    simpa only [d258807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46865 p = 1 := by simpa only [d258807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30896 p hg
    simpa only [d258807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31057 (p : Pattern) (guard : d258808 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30891 p hg
    simpa only [d258808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258807 p = 1 := by simpa only [d258808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31056 p hg
    simpa only [d258808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31058 (p : Pattern) (guard : d258809 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 223 with
  | false =>
    have hg : d258808 p = 1 := by simpa only [d258809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31057 p hg
    simpa only [d258809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30891 p hg
    simpa only [d258809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31059 (p : Pattern) (guard : d258810 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258809 p = 1 := by simpa only [d258810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31058 p hg
    simpa only [d258810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30891 p hg
    simpa only [d258810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31060 (p : Pattern) (guard : d258811 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 202 with
  | false =>
    have hg : d258810 p = 1 := by simpa only [d258811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31059 p hg
    simpa only [d258811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30891 p hg
    simpa only [d258811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31061 (p : Pattern) (guard : d258812 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 201 with
  | false =>
    have hg : d258811 p = 1 := by simpa only [d258812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31060 p hg
    simpa only [d258812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258698 p = 1 := by simpa only [d258812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30901 p hg
    simpa only [d258812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31062 (p : Pattern) (guard : d258813 p = 1) : d47652 p ≤ (-2 : Int) + d253301 p := by
  cases selected : p 182 with
  | false =>
    have hg : d258812 p = 1 := by simpa only [d258813, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31061 p hg
    simpa only [d258813, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258813, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30903 p hg
    simpa only [d258813, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31063 (p : Pattern) (guard : d258814 p = 1) : d47652 p ≤ (-2 : Int) + d253301 p := by
  cases selected : p 180 with
  | false =>
    have hg : d258813 p = 1 := by simpa only [d258814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31062 p hg
    simpa only [d258814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258700 p = 1 := by simpa only [d258814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30904 p hg
    simpa only [d258814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31064 (p : Pattern) (guard : d258869 p = 1) : d47652 p ≤ (-2 : Int) + d253301 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30890 p hg
    simpa only [d258869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258814 p = 1 := by simpa only [d258869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31063 p hg
    simpa only [d258869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31065 (p : Pattern) (guard : d258815 p = 1) : d47797 p ≤ (-2 : Int) + d253434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d258814 p = 1 := by simpa only [d258815, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30977 p hg
    simpa only [d258815, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258815, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30852 p hg
    simpa only [d258815, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31066 (p : Pattern) (guard : d258870 p = 1) : d47798 p ≤ (-2 : Int) + d253435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d258869 p = 1 := by simpa only [d258870, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31064 p hg
    simpa only [d258870, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258815 p = 1 := by simpa only [d258870, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31065 p hg
    simpa only [d258870, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31067 (p : Pattern) (guard : d307 p = 1) : d6 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 247 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d307, d47633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30910 p hg
    simpa only [d307, d47633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d127 p = 1 := by simpa only [d307, d47633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8410 p hg
    simpa only [d307, d47633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31068 (p : Pattern) (guard : d1997 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 246 with
  | false =>
    have hg : d307 p = 1 := by simpa only [d1997, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31067 p hg
    simpa only [d1997, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1997, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30912 p hg
    simpa only [d1997, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31069 (p : Pattern) (guard : d258806 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d258806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31068 p hg
    simpa only [d258806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46864 p = 1 := by simpa only [d258806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30913 p hg
    simpa only [d258806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31070 (p : Pattern) (guard : d258807 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 225 with
  | false =>
    have hg : d258806 p = 1 := by simpa only [d258807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31069 p hg
    simpa only [d258807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46865 p = 1 := by simpa only [d258807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30914 p hg
    simpa only [d258807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31071 (p : Pattern) (guard : d258808 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30909 p hg
    simpa only [d258808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258807 p = 1 := by simpa only [d258808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31070 p hg
    simpa only [d258808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31072 (p : Pattern) (guard : d258809 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 223 with
  | false =>
    have hg : d258808 p = 1 := by simpa only [d258809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31071 p hg
    simpa only [d258809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30909 p hg
    simpa only [d258809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31073 (p : Pattern) (guard : d258810 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258809 p = 1 := by simpa only [d258810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31072 p hg
    simpa only [d258810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30909 p hg
    simpa only [d258810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31074 (p : Pattern) (guard : d258811 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 202 with
  | false =>
    have hg : d258810 p = 1 := by simpa only [d258811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31073 p hg
    simpa only [d258811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30909 p hg
    simpa only [d258811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31075 (p : Pattern) (guard : d258812 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 201 with
  | false =>
    have hg : d258811 p = 1 := by simpa only [d258812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31074 p hg
    simpa only [d258812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258698 p = 1 := by simpa only [d258812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30919 p hg
    simpa only [d258812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31076 (p : Pattern) (guard : d258813 p = 1) : d47677 p ≤ (-2 : Int) + d253324 p := by
  cases selected : p 182 with
  | false =>
    have hg : d258812 p = 1 := by simpa only [d258813, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31075 p hg
    simpa only [d258813, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258813, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30921 p hg
    simpa only [d258813, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31077 (p : Pattern) (guard : d258814 p = 1) : d47677 p ≤ (-2 : Int) + d253324 p := by
  cases selected : p 180 with
  | false =>
    have hg : d258813 p = 1 := by simpa only [d258814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31076 p hg
    simpa only [d258814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258700 p = 1 := by simpa only [d258814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30922 p hg
    simpa only [d258814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31078 (p : Pattern) (guard : d258815 p = 1) : d47682 p ≤ (-2 : Int) + d253329 p := by
  cases selected : p 163 with
  | false =>
    have hg : d258814 p = 1 := by simpa only [d258815, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31077 p hg
    simpa only [d258815, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258815, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d258815, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31079 (p : Pattern) (guard : d258816 p = 1) : d47683 p ≤ (-2 : Int) + d253330 p := by
  cases selected : p 162 with
  | false =>
    have hg : d258815 p = 1 := by simpa only [d258816, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31078 p hg
    simpa only [d258816, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258816, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d258816, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31080 (p : Pattern) (guard : d258871 p = 1) : d47799 p ≤ (-2 : Int) + d253436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d258870 p = 1 := by simpa only [d258871, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31066 p hg
    simpa only [d258871, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258816 p = 1 := by simpa only [d258871, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31079 p hg
    simpa only [d258871, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31081 (p : Pattern) (guard : d258872 p = 1) : d47803 p ≤ (-2 : Int) + d253440 p := by
  cases selected : p 160 with
  | false =>
    have hg : d258871 p = 1 := by simpa only [d258872, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31080 p hg
    simpa only [d258872, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258872, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30928 p hg
    simpa only [d258872, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31082 (p : Pattern) (guard : d258873 p = 1) : d47803 p ≤ (-2 : Int) + d253440 p := by
  cases selected : p 159 with
  | false =>
    have hg : d258872 p = 1 := by simpa only [d258873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31081 p hg
    simpa only [d258873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258746 p = 1 := by simpa only [d258873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30929 p hg
    simpa only [d258873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31083 (p : Pattern) (guard : d258874 p = 1) : d47803 p ≤ (-2 : Int) + d253440 p := by
  cases selected : p 158 with
  | false =>
    have hg : d258873 p = 1 := by simpa only [d258874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31082 p hg
    simpa only [d258874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258747 p = 1 := by simpa only [d258874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30931 p hg
    simpa only [d258874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31084 (p : Pattern) (guard : d258875 p = 1) : d47803 p ≤ (-2 : Int) + d253440 p := by
  cases selected : p 157 with
  | false =>
    have hg : d258874 p = 1 := by simpa only [d258875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31083 p hg
    simpa only [d258875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258748 p = 1 := by simpa only [d258875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30932 p hg
    simpa only [d258875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31085 (p : Pattern) (guard : d258876 p = 1) : d47804 p ≤ (-2 : Int) + d253441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258876, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30889 p hg
    simpa only [d258876, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258875 p = 1 := by simpa only [d258876, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31084 p hg
    simpa only [d258876, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31086 (p : Pattern) (guard : d258877 p = 1) : d47805 p ≤ (-2 : Int) + d253442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258877, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30888 p hg
    simpa only [d258877, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258876 p = 1 := by simpa only [d258877, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31085 p hg
    simpa only [d258877, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31087 (p : Pattern) (guard : d258878 p = 1) : d47805 p ≤ (-2 : Int) + d253442 p := by
  cases selected : p 136 with
  | false =>
    have hg : d258877 p = 1 := by simpa only [d258878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31086 p hg
    simpa only [d258878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258751 p = 1 := by simpa only [d258878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30935 p hg
    simpa only [d258878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31088 (p : Pattern) (guard : d258879 p = 1) : d47805 p ≤ (-2 : Int) + d253442 p := by
  cases selected : p 135 with
  | false =>
    have hg : d258878 p = 1 := by simpa only [d258879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31087 p hg
    simpa only [d258879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258752 p = 1 := by simpa only [d258879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30937 p hg
    simpa only [d258879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31089 (p : Pattern) (guard : d258880 p = 1) : d47805 p ≤ (-2 : Int) + d253442 p := by
  cases selected : p 119 with
  | false =>
    have hg : d258879 p = 1 := by simpa only [d258880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31088 p hg
    simpa only [d258880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30936 p hg
    simpa only [d258880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31090 (p : Pattern) (guard : d258881 p = 1) : d47807 p ≤ (-2 : Int) + d253444 p := by
  cases selected : p 116 with
  | false =>
    have hg : d258880 p = 1 := by simpa only [d258881, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31089 p hg
    simpa only [d258881, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258881, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30940 p hg
    simpa only [d258881, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31091 (p : Pattern) (guard : d258882 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258882, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30769 p hg
    simpa only [d258882, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258881 p = 1 := by simpa only [d258882, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31090 p hg
    simpa only [d258882, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31092 (p : Pattern) (guard : d258883 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 113 with
  | false =>
    have hg : d258882 p = 1 := by simpa only [d258883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31091 p hg
    simpa only [d258883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258756 p = 1 := by simpa only [d258883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30942 p hg
    simpa only [d258883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31093 (p : Pattern) (guard : d258884 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 96 with
  | false =>
    have hg : d258883 p = 1 := by simpa only [d258884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31092 p hg
    simpa only [d258884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d258884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31094 (p : Pattern) (guard : d258885 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 95 with
  | false =>
    have hg : d258884 p = 1 := by simpa only [d258885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31093 p hg
    simpa only [d258885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d258885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31095 (p : Pattern) (guard : d258886 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 93 with
  | false =>
    have hg : d258885 p = 1 := by simpa only [d258886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31094 p hg
    simpa only [d258886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d258886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31096 (p : Pattern) (guard : d258887 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 91 with
  | false =>
    have hg : d258886 p = 1 := by simpa only [d258887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31095 p hg
    simpa only [d258887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258760 p = 1 := by simpa only [d258887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30946 p hg
    simpa only [d258887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31097 (p : Pattern) (guard : d260113 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d260113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258887 p = 1 := by simpa only [d260113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31096 p hg
    simpa only [d260113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31098 (p : Pattern) (guard : d260114 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 89 with
  | false =>
    have hg : d260113 p = 1 := by simpa only [d260114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31097 p hg
    simpa only [d260114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d260114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31099 (p : Pattern) (guard : d260115 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d260115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260114 p = 1 := by simpa only [d260115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31098 p hg
    simpa only [d260115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31100 (p : Pattern) (guard : d260116 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d260116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260115 p = 1 := by simpa only [d260116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31099 p hg
    simpa only [d260116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31101 (p : Pattern) (guard : d260117 p = 1) : d47809 p ≤ (-2 : Int) + d253446 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260117, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d260117, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260116 p = 1 := by simpa only [d260117, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31100 p hg
    simpa only [d260117, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31102 (p : Pattern) (guard : d260118 p = 1) : d47809 p ≤ (-2 : Int) + d253446 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30886 p hg
    simpa only [d260118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260117 p = 1 := by simpa only [d260118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31101 p hg
    simpa only [d260118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31103 (p : Pattern) (guard : d260119 p = 1) : d47809 p ≤ (-2 : Int) + d253446 p := by
  cases selected : p 69 with
  | false =>
    have hg : d260118 p = 1 := by simpa only [d260119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31102 p hg
    simpa only [d260119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30886 p hg
    simpa only [d260119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31104 (p : Pattern) (guard : d260120 p = 1) : d47809 p ≤ (-2 : Int) + d253446 p := by
  cases selected : p 51 with
  | false =>
    have hg : d260119 p = 1 := by simpa only [d260120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31103 p hg
    simpa only [d260120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30886 p hg
    simpa only [d260120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31105 (p : Pattern) (guard : d260121 p = 1) : d47809 p ≤ (-2 : Int) + d253446 p := by
  cases selected : p 50 with
  | false =>
    have hg : d260120 p = 1 := by simpa only [d260121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31104 p hg
    simpa only [d260121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30886 p hg
    simpa only [d260121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31106 (p : Pattern) (guard : d260122 p = 1) : d47865 p ≤ (-2 : Int) + d253502 p := by
  cases selected : p 49 with
  | false =>
    have hg : d260121 p = 1 := by simpa only [d260122, d47865, d253502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31105 p hg
    simpa only [d260122, d47865, d253502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260122, d47865, d253502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30957 p hg
    simpa only [d260122, d47865, d253502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31107 (p : Pattern) (guard : d260123 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 48 with
  | false =>
    have hg : d260112 p = 1 := by simpa only [d260123, d47866, d253503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31052 p hg
    simpa only [d260123, d47866, d253503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260122 p = 1 := by simpa only [d260123, d47866, d253503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31106 p hg
    simpa only [d260123, d47866, d253503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31108 (p : Pattern) (guard : d260124 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260123 p = 1 := by simpa only [d260124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31107 p hg
    simpa only [d260124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31109 (p : Pattern) (guard : d260125 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260124 p = 1 := by simpa only [d260125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31108 p hg
    simpa only [d260125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31110 (p : Pattern) (guard : d260126 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260125 p = 1 := by simpa only [d260126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31109 p hg
    simpa only [d260126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31111 (p : Pattern) (guard : d260127 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260126 p = 1 := by simpa only [d260127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31110 p hg
    simpa only [d260127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31112 (p : Pattern) (guard : d260128 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260127 p = 1 := by simpa only [d260128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31111 p hg
    simpa only [d260128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31113 (p : Pattern) (guard : d260129 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260128 p = 1 := by simpa only [d260129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31112 p hg
    simpa only [d260129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31114 (p : Pattern) (guard : d260130 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260129 p = 1 := by simpa only [d260130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31113 p hg
    simpa only [d260130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31115 (p : Pattern) (guard : d260131 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d260104 p = 1 := by simpa only [d260131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30966 p hg
    simpa only [d260131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260130 p = 1 := by simpa only [d260131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31114 p hg
    simpa only [d260131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31116 (p : Pattern) (guard : d1998 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30773 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1997 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30968 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31117 (p : Pattern) (guard : d258933 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1998 p = 1 := by simpa only [d258933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31116 p hg
    simpa only [d258933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258806 p = 1 := by simpa only [d258933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30969 p hg
    simpa only [d258933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31118 (p : Pattern) (guard : d258934 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30773 p hg
    simpa only [d258934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258933 p = 1 := by simpa only [d258934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31117 p hg
    simpa only [d258934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31119 (p : Pattern) (guard : d258935 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 223 with
  | false =>
    have hg : d258934 p = 1 := by simpa only [d258935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31118 p hg
    simpa only [d258935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30773 p hg
    simpa only [d258935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31120 (p : Pattern) (guard : d258936 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258935 p = 1 := by simpa only [d258936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31119 p hg
    simpa only [d258936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30773 p hg
    simpa only [d258936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31121 (p : Pattern) (guard : d258937 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 202 with
  | false =>
    have hg : d258936 p = 1 := by simpa only [d258937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31120 p hg
    simpa only [d258937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30773 p hg
    simpa only [d258937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31122 (p : Pattern) (guard : d258938 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 201 with
  | false =>
    have hg : d258937 p = 1 := by simpa only [d258938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31121 p hg
    simpa only [d258938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258811 p = 1 := by simpa only [d258938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30974 p hg
    simpa only [d258938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31123 (p : Pattern) (guard : d258939 p = 1) : d47619 p ≤ (-2 : Int) + d253276 p := by
  cases selected : p 182 with
  | false =>
    have hg : d258938 p = 1 := by simpa only [d258939, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31122 p hg
    simpa only [d258939, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258939, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30785 p hg
    simpa only [d258939, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31124 (p : Pattern) (guard : d258940 p = 1) : d47617 p ≤ (-2 : Int) + d47616 p := by
  cases selected : p 201 with
  | false =>
    have hg : d258811 p = 1 := by simpa only [d258940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30974 p hg
    simpa only [d258940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30773 p hg
    simpa only [d258940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31125 (p : Pattern) (guard : d258941 p = 1) : d47619 p ≤ (-2 : Int) + d253276 p := by
  cases selected : p 182 with
  | false =>
    have hg : d258940 p = 1 := by simpa only [d258941, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31124 p hg
    simpa only [d258941, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258941, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30785 p hg
    simpa only [d258941, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31126 (p : Pattern) (guard : d258942 p = 1) : d47619 p ≤ (-2 : Int) + d253276 p := by
  cases selected : p 180 with
  | false =>
    have hg : d258939 p = 1 := by simpa only [d258942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31123 p hg
    simpa only [d258942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258941 p = 1 := by simpa only [d258942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31125 p hg
    simpa only [d258942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31127 (p : Pattern) (guard : d258943 p = 1) : d47660 p ≤ (-2 : Int) + d253307 p := by
  cases selected : p 163 with
  | false =>
    have hg : d258942 p = 1 := by simpa only [d258943, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31126 p hg
    simpa only [d258943, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258943, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30789 p hg
    simpa only [d258943, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31128 (p : Pattern) (guard : d258944 p = 1) : d47663 p ≤ (-2 : Int) + d253310 p := by
  cases selected : p 162 with
  | false =>
    have hg : d258943 p = 1 := by simpa only [d258944, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31127 p hg
    simpa only [d258944, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258944, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30791 p hg
    simpa only [d258944, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31129 (p : Pattern) (guard : d258945 p = 1) : d47664 p ≤ (-2 : Int) + d253311 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258945, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30772 p hg
    simpa only [d258945, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258944 p = 1 := by simpa only [d258945, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31128 p hg
    simpa only [d258945, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31130 (p : Pattern) (guard : d258946 p = 1) : d47685 p ≤ (-2 : Int) + d253332 p := by
  cases selected : p 160 with
  | false =>
    have hg : d258945 p = 1 := by simpa only [d258946, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31129 p hg
    simpa only [d258946, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258946, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30794 p hg
    simpa only [d258946, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31131 (p : Pattern) (guard : d258947 p = 1) : d47685 p ≤ (-2 : Int) + d253332 p := by
  cases selected : p 159 with
  | false =>
    have hg : d258946 p = 1 := by simpa only [d258947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31130 p hg
    simpa only [d258947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258818 p = 1 := by simpa only [d258947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30981 p hg
    simpa only [d258947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31132 (p : Pattern) (guard : d258948 p = 1) : d47619 p ≤ (-2 : Int) + d253276 p := by
  cases selected : p 180 with
  | false =>
    have hg : d258941 p = 1 := by simpa only [d258948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31125 p hg
    simpa only [d258948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258700 p = 1 := by simpa only [d258948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30786 p hg
    simpa only [d258948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31133 (p : Pattern) (guard : d258949 p = 1) : d47660 p ≤ (-2 : Int) + d253307 p := by
  cases selected : p 163 with
  | false =>
    have hg : d258948 p = 1 := by simpa only [d258949, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31132 p hg
    simpa only [d258949, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258949, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30789 p hg
    simpa only [d258949, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31134 (p : Pattern) (guard : d258950 p = 1) : d47663 p ≤ (-2 : Int) + d253310 p := by
  cases selected : p 162 with
  | false =>
    have hg : d258949 p = 1 := by simpa only [d258950, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31133 p hg
    simpa only [d258950, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258950, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30791 p hg
    simpa only [d258950, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31135 (p : Pattern) (guard : d258951 p = 1) : d47664 p ≤ (-2 : Int) + d253311 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258951, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30772 p hg
    simpa only [d258951, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258950 p = 1 := by simpa only [d258951, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31134 p hg
    simpa only [d258951, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31136 (p : Pattern) (guard : d258952 p = 1) : d47685 p ≤ (-2 : Int) + d253332 p := by
  cases selected : p 160 with
  | false =>
    have hg : d258951 p = 1 := by simpa only [d258952, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31135 p hg
    simpa only [d258952, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258952, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30794 p hg
    simpa only [d258952, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31137 (p : Pattern) (guard : d258953 p = 1) : d47685 p ≤ (-2 : Int) + d253332 p := by
  cases selected : p 159 with
  | false =>
    have hg : d258952 p = 1 := by simpa only [d258953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31136 p hg
    simpa only [d258953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258705 p = 1 := by simpa only [d258953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30795 p hg
    simpa only [d258953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31138 (p : Pattern) (guard : d258954 p = 1) : d47685 p ≤ (-2 : Int) + d253332 p := by
  cases selected : p 158 with
  | false =>
    have hg : d258947 p = 1 := by simpa only [d258954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31131 p hg
    simpa only [d258954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258953 p = 1 := by simpa only [d258954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31137 p hg
    simpa only [d258954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31139 (p : Pattern) (guard : d258955 p = 1) : d47685 p ≤ (-2 : Int) + d253332 p := by
  cases selected : p 157 with
  | false =>
    have hg : d258954 p = 1 := by simpa only [d258955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31138 p hg
    simpa only [d258955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258820 p = 1 := by simpa only [d258955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30983 p hg
    simpa only [d258955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31140 (p : Pattern) (guard : d258956 p = 1) : d47686 p ≤ (-2 : Int) + d253333 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258956, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30771 p hg
    simpa only [d258956, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258955 p = 1 := by simpa only [d258956, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31139 p hg
    simpa only [d258956, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31141 (p : Pattern) (guard : d258957 p = 1) : d47687 p ≤ (-2 : Int) + d253334 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258957, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30770 p hg
    simpa only [d258957, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258956 p = 1 := by simpa only [d258957, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31140 p hg
    simpa only [d258957, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31142 (p : Pattern) (guard : d258958 p = 1) : d47687 p ≤ (-2 : Int) + d253334 p := by
  cases selected : p 136 with
  | false =>
    have hg : d258957 p = 1 := by simpa only [d258958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31141 p hg
    simpa only [d258958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258823 p = 1 := by simpa only [d258958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30986 p hg
    simpa only [d258958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31143 (p : Pattern) (guard : d259069 p = 1) : d47687 p ≤ (-2 : Int) + d253334 p := by
  cases selected : p 136 with
  | false =>
    have hg : d258823 p = 1 := by simpa only [d259069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30986 p hg
    simpa only [d259069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30802 p hg
    simpa only [d259069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31144 (p : Pattern) (guard : d259070 p = 1) : d47687 p ≤ (-2 : Int) + d253334 p := by
  cases selected : p 135 with
  | false =>
    have hg : d258958 p = 1 := by simpa only [d259070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31142 p hg
    simpa only [d259070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259069 p = 1 := by simpa only [d259070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31143 p hg
    simpa only [d259070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31145 (p : Pattern) (guard : d259071 p = 1) : d47687 p ≤ (-2 : Int) + d253334 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259070 p = 1 := by simpa only [d259071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31144 p hg
    simpa only [d259071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30802 p hg
    simpa only [d259071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31146 (p : Pattern) (guard : d259072 p = 1) : d47699 p ≤ (-2 : Int) + d253346 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259071 p = 1 := by simpa only [d259072, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31145 p hg
    simpa only [d259072, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259072, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30806 p hg
    simpa only [d259072, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31147 (p : Pattern) (guard : d259073 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259073, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30769 p hg
    simpa only [d259073, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259072 p = 1 := by simpa only [d259073, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31146 p hg
    simpa only [d259073, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31148 (p : Pattern) (guard : d259074 p = 1) : d47687 p ≤ (-2 : Int) + d253334 p := by
  cases selected : p 135 with
  | false =>
    have hg : d259069 p = 1 := by simpa only [d259074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31143 p hg
    simpa only [d259074, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30802 p hg
    simpa only [d259074, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31149 (p : Pattern) (guard : d259075 p = 1) : d47687 p ≤ (-2 : Int) + d253334 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259074 p = 1 := by simpa only [d259075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31148 p hg
    simpa only [d259075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30802 p hg
    simpa only [d259075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31150 (p : Pattern) (guard : d259076 p = 1) : d47699 p ≤ (-2 : Int) + d253346 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259075 p = 1 := by simpa only [d259076, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31149 p hg
    simpa only [d259076, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259076, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30806 p hg
    simpa only [d259076, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31151 (p : Pattern) (guard : d259077 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259077, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30769 p hg
    simpa only [d259077, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259076 p = 1 := by simpa only [d259077, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31150 p hg
    simpa only [d259077, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31152 (p : Pattern) (guard : d259078 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259073 p = 1 := by simpa only [d259078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31147 p hg
    simpa only [d259078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259077 p = 1 := by simpa only [d259078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31151 p hg
    simpa only [d259078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31153 (p : Pattern) (guard : d259079 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259078 p = 1 := by simpa only [d259079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31152 p hg
    simpa only [d259079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31154 (p : Pattern) (guard : d259080 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259079 p = 1 := by simpa only [d259080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31153 p hg
    simpa only [d259080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31155 (p : Pattern) (guard : d259081 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259080 p = 1 := by simpa only [d259081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31154 p hg
    simpa only [d259081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31156 (p : Pattern) (guard : d259082 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259077 p = 1 := by simpa only [d259082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31151 p hg
    simpa only [d259082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31157 (p : Pattern) (guard : d259083 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259082 p = 1 := by simpa only [d259083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31156 p hg
    simpa only [d259083, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259083, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31158 (p : Pattern) (guard : d259084 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259083 p = 1 := by simpa only [d259084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31157 p hg
    simpa only [d259084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31159 (p : Pattern) (guard : d259085 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259084 p = 1 := by simpa only [d259085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31158 p hg
    simpa only [d259085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31160 (p : Pattern) (guard : d259086 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259081 p = 1 := by simpa only [d259086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31155 p hg
    simpa only [d259086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259085 p = 1 := by simpa only [d259086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31159 p hg
    simpa only [d259086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31161 (p : Pattern) (guard : d259087 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259086 p = 1 := by simpa only [d259087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31160 p hg
    simpa only [d259087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31162 (p : Pattern) (guard : d259088 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259087 p = 1 := by simpa only [d259088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31161 p hg
    simpa only [d259088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31163 (p : Pattern) (guard : d259089 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259088 p = 1 := by simpa only [d259089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31162 p hg
    simpa only [d259089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31164 (p : Pattern) (guard : d259090 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259089 p = 1 := by simpa only [d259090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31163 p hg
    simpa only [d259090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31165 (p : Pattern) (guard : d259091 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259090 p = 1 := by simpa only [d259091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31164 p hg
    simpa only [d259091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31166 (p : Pattern) (guard : d259094 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259080 p = 1 := by simpa only [d259094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31154 p hg
    simpa only [d259094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31167 (p : Pattern) (guard : d259095 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259084 p = 1 := by simpa only [d259095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31158 p hg
    simpa only [d259095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31168 (p : Pattern) (guard : d259096 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259094 p = 1 := by simpa only [d259096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31166 p hg
    simpa only [d259096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259095 p = 1 := by simpa only [d259096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31167 p hg
    simpa only [d259096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31169 (p : Pattern) (guard : d259097 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259096 p = 1 := by simpa only [d259097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31168 p hg
    simpa only [d259097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31170 (p : Pattern) (guard : d259098 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259097 p = 1 := by simpa only [d259098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31169 p hg
    simpa only [d259098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31171 (p : Pattern) (guard : d259099 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259098 p = 1 := by simpa only [d259099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31170 p hg
    simpa only [d259099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31172 (p : Pattern) (guard : d259100 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259099 p = 1 := by simpa only [d259100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31171 p hg
    simpa only [d259100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31173 (p : Pattern) (guard : d259101 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 71 with
  | false =>
    have hg : d259090 p = 1 := by simpa only [d259101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31164 p hg
    simpa only [d259101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259100 p = 1 := by simpa only [d259101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31172 p hg
    simpa only [d259101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31174 (p : Pattern) (guard : d259102 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 70 with
  | false =>
    have hg : d259091 p = 1 := by simpa only [d259102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31165 p hg
    simpa only [d259102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259101 p = 1 := by simpa only [d259102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31173 p hg
    simpa only [d259102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31175 (p : Pattern) (guard : d259103 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 69 with
  | false =>
    have hg : d259102 p = 1 := by simpa only [d259103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31174 p hg
    simpa only [d259103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d259103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31176 (p : Pattern) (guard : d260132 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 51 with
  | false =>
    have hg : d259103 p = 1 := by simpa only [d260132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31175 p hg
    simpa only [d260132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d260132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31177 (p : Pattern) (guard : d260133 p = 1) : d47700 p ≤ (-2 : Int) + d253347 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d260133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260132 p = 1 := by simpa only [d260133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31176 p hg
    simpa only [d260133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31178 (p : Pattern) (guard : d1998 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30836 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1997 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31014 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31179 (p : Pattern) (guard : d258933 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1998 p = 1 := by simpa only [d258933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31178 p hg
    simpa only [d258933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258806 p = 1 := by simpa only [d258933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31015 p hg
    simpa only [d258933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31180 (p : Pattern) (guard : d258934 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30836 p hg
    simpa only [d258934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258933 p = 1 := by simpa only [d258934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31179 p hg
    simpa only [d258934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31181 (p : Pattern) (guard : d258935 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 223 with
  | false =>
    have hg : d258934 p = 1 := by simpa only [d258935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31180 p hg
    simpa only [d258935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30836 p hg
    simpa only [d258935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31182 (p : Pattern) (guard : d258936 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258935 p = 1 := by simpa only [d258936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31181 p hg
    simpa only [d258936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30836 p hg
    simpa only [d258936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31183 (p : Pattern) (guard : d258937 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 202 with
  | false =>
    have hg : d258936 p = 1 := by simpa only [d258937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31182 p hg
    simpa only [d258937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30836 p hg
    simpa only [d258937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31184 (p : Pattern) (guard : d258938 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 201 with
  | false =>
    have hg : d258937 p = 1 := by simpa only [d258938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31183 p hg
    simpa only [d258938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258811 p = 1 := by simpa only [d258938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31020 p hg
    simpa only [d258938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31185 (p : Pattern) (guard : d258939 p = 1) : d47708 p ≤ (-2 : Int) + d253351 p := by
  cases selected : p 182 with
  | false =>
    have hg : d258938 p = 1 := by simpa only [d258939, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31184 p hg
    simpa only [d258939, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258939, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30848 p hg
    simpa only [d258939, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31186 (p : Pattern) (guard : d258940 p = 1) : d47706 p ≤ (-2 : Int) + d47705 p := by
  cases selected : p 201 with
  | false =>
    have hg : d258811 p = 1 := by simpa only [d258940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31020 p hg
    simpa only [d258940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30836 p hg
    simpa only [d258940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31187 (p : Pattern) (guard : d258941 p = 1) : d47708 p ≤ (-2 : Int) + d253351 p := by
  cases selected : p 182 with
  | false =>
    have hg : d258940 p = 1 := by simpa only [d258941, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31186 p hg
    simpa only [d258941, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258941, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30848 p hg
    simpa only [d258941, d47708, d253351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31188 (p : Pattern) (guard : d258942 p = 1) : d47708 p ≤ (-2 : Int) + d253351 p := by
  cases selected : p 180 with
  | false =>
    have hg : d258939 p = 1 := by simpa only [d258942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31185 p hg
    simpa only [d258942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258941 p = 1 := by simpa only [d258942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31187 p hg
    simpa only [d258942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31189 (p : Pattern) (guard : d258943 p = 1) : d47735 p ≤ (-2 : Int) + d253374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d258942 p = 1 := by simpa only [d258943, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31188 p hg
    simpa only [d258943, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258943, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30852 p hg
    simpa only [d258943, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31190 (p : Pattern) (guard : d258944 p = 1) : d47736 p ≤ (-2 : Int) + d253375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d258943 p = 1 := by simpa only [d258944, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31189 p hg
    simpa only [d258944, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258944, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d258944, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31191 (p : Pattern) (guard : d258945 p = 1) : d47737 p ≤ (-2 : Int) + d253376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258945, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30835 p hg
    simpa only [d258945, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258944 p = 1 := by simpa only [d258945, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31190 p hg
    simpa only [d258945, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31192 (p : Pattern) (guard : d258946 p = 1) : d47755 p ≤ (-2 : Int) + d253394 p := by
  cases selected : p 160 with
  | false =>
    have hg : d258945 p = 1 := by simpa only [d258946, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31191 p hg
    simpa only [d258946, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258946, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30856 p hg
    simpa only [d258946, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31193 (p : Pattern) (guard : d258947 p = 1) : d47755 p ≤ (-2 : Int) + d253394 p := by
  cases selected : p 159 with
  | false =>
    have hg : d258946 p = 1 := by simpa only [d258947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31192 p hg
    simpa only [d258947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258818 p = 1 := by simpa only [d258947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31027 p hg
    simpa only [d258947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31194 (p : Pattern) (guard : d258948 p = 1) : d47708 p ≤ (-2 : Int) + d253351 p := by
  cases selected : p 180 with
  | false =>
    have hg : d258941 p = 1 := by simpa only [d258948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31187 p hg
    simpa only [d258948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258700 p = 1 := by simpa only [d258948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30849 p hg
    simpa only [d258948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31195 (p : Pattern) (guard : d258949 p = 1) : d47735 p ≤ (-2 : Int) + d253374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d258948 p = 1 := by simpa only [d258949, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31194 p hg
    simpa only [d258949, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258949, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30852 p hg
    simpa only [d258949, d47735, d253374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31196 (p : Pattern) (guard : d258950 p = 1) : d47736 p ≤ (-2 : Int) + d253375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d258949 p = 1 := by simpa only [d258950, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31195 p hg
    simpa only [d258950, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258950, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d258950, d47736, d253375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31197 (p : Pattern) (guard : d258951 p = 1) : d47737 p ≤ (-2 : Int) + d253376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258951, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30835 p hg
    simpa only [d258951, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258950 p = 1 := by simpa only [d258951, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31196 p hg
    simpa only [d258951, d47737, d253376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31198 (p : Pattern) (guard : d258952 p = 1) : d47755 p ≤ (-2 : Int) + d253394 p := by
  cases selected : p 160 with
  | false =>
    have hg : d258951 p = 1 := by simpa only [d258952, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31197 p hg
    simpa only [d258952, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258952, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30856 p hg
    simpa only [d258952, d47755, d253394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31199 (p : Pattern) (guard : d258953 p = 1) : d47755 p ≤ (-2 : Int) + d253394 p := by
  cases selected : p 159 with
  | false =>
    have hg : d258952 p = 1 := by simpa only [d258953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31198 p hg
    simpa only [d258953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258705 p = 1 := by simpa only [d258953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30857 p hg
    simpa only [d258953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31200 (p : Pattern) (guard : d258954 p = 1) : d47755 p ≤ (-2 : Int) + d253394 p := by
  cases selected : p 158 with
  | false =>
    have hg : d258947 p = 1 := by simpa only [d258954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31193 p hg
    simpa only [d258954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258953 p = 1 := by simpa only [d258954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31199 p hg
    simpa only [d258954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31201 (p : Pattern) (guard : d258955 p = 1) : d47755 p ≤ (-2 : Int) + d253394 p := by
  cases selected : p 157 with
  | false =>
    have hg : d258954 p = 1 := by simpa only [d258955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31200 p hg
    simpa only [d258955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258820 p = 1 := by simpa only [d258955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31029 p hg
    simpa only [d258955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31202 (p : Pattern) (guard : d258956 p = 1) : d47756 p ≤ (-2 : Int) + d253395 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258956, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30834 p hg
    simpa only [d258956, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258955 p = 1 := by simpa only [d258956, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31201 p hg
    simpa only [d258956, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31203 (p : Pattern) (guard : d258957 p = 1) : d47757 p ≤ (-2 : Int) + d253396 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258957, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30833 p hg
    simpa only [d258957, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258956 p = 1 := by simpa only [d258957, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31202 p hg
    simpa only [d258957, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31204 (p : Pattern) (guard : d258958 p = 1) : d47757 p ≤ (-2 : Int) + d253396 p := by
  cases selected : p 136 with
  | false =>
    have hg : d258957 p = 1 := by simpa only [d258958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31203 p hg
    simpa only [d258958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258823 p = 1 := by simpa only [d258958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31032 p hg
    simpa only [d258958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31205 (p : Pattern) (guard : d259069 p = 1) : d47757 p ≤ (-2 : Int) + d253396 p := by
  cases selected : p 136 with
  | false =>
    have hg : d258823 p = 1 := by simpa only [d259069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31032 p hg
    simpa only [d259069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30864 p hg
    simpa only [d259069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31206 (p : Pattern) (guard : d259070 p = 1) : d47757 p ≤ (-2 : Int) + d253396 p := by
  cases selected : p 135 with
  | false =>
    have hg : d258958 p = 1 := by simpa only [d259070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31204 p hg
    simpa only [d259070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259069 p = 1 := by simpa only [d259070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31205 p hg
    simpa only [d259070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31207 (p : Pattern) (guard : d259071 p = 1) : d47757 p ≤ (-2 : Int) + d253396 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259070 p = 1 := by simpa only [d259071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31206 p hg
    simpa only [d259071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30864 p hg
    simpa only [d259071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31208 (p : Pattern) (guard : d259072 p = 1) : d47765 p ≤ (-2 : Int) + d253404 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259071 p = 1 := by simpa only [d259072, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31207 p hg
    simpa only [d259072, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259072, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30868 p hg
    simpa only [d259072, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31209 (p : Pattern) (guard : d259073 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259073, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30832 p hg
    simpa only [d259073, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259072 p = 1 := by simpa only [d259073, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31208 p hg
    simpa only [d259073, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31210 (p : Pattern) (guard : d259074 p = 1) : d47757 p ≤ (-2 : Int) + d253396 p := by
  cases selected : p 135 with
  | false =>
    have hg : d259069 p = 1 := by simpa only [d259074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31205 p hg
    simpa only [d259074, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30864 p hg
    simpa only [d259074, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31211 (p : Pattern) (guard : d259075 p = 1) : d47757 p ≤ (-2 : Int) + d253396 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259074 p = 1 := by simpa only [d259075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31210 p hg
    simpa only [d259075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30864 p hg
    simpa only [d259075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31212 (p : Pattern) (guard : d259076 p = 1) : d47765 p ≤ (-2 : Int) + d253404 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259075 p = 1 := by simpa only [d259076, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31211 p hg
    simpa only [d259076, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259076, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30868 p hg
    simpa only [d259076, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31213 (p : Pattern) (guard : d259077 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259077, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30832 p hg
    simpa only [d259077, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259076 p = 1 := by simpa only [d259077, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31212 p hg
    simpa only [d259077, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31214 (p : Pattern) (guard : d259078 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259073 p = 1 := by simpa only [d259078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31209 p hg
    simpa only [d259078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259077 p = 1 := by simpa only [d259078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31213 p hg
    simpa only [d259078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31215 (p : Pattern) (guard : d259079 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259078 p = 1 := by simpa only [d259079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31214 p hg
    simpa only [d259079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d259079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31216 (p : Pattern) (guard : d259080 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259079 p = 1 := by simpa only [d259080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31215 p hg
    simpa only [d259080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d259080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31217 (p : Pattern) (guard : d259094 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259080 p = 1 := by simpa only [d259094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31216 p hg
    simpa only [d259094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d259094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31218 (p : Pattern) (guard : d259082 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259077 p = 1 := by simpa only [d259082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31213 p hg
    simpa only [d259082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d259082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31219 (p : Pattern) (guard : d259083 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259082 p = 1 := by simpa only [d259083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31218 p hg
    simpa only [d259083, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d259083, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31220 (p : Pattern) (guard : d259084 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259083 p = 1 := by simpa only [d259084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31219 p hg
    simpa only [d259084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d259084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31221 (p : Pattern) (guard : d259095 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259084 p = 1 := by simpa only [d259095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31220 p hg
    simpa only [d259095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d259095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31222 (p : Pattern) (guard : d259096 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259094 p = 1 := by simpa only [d259096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31217 p hg
    simpa only [d259096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259095 p = 1 := by simpa only [d259096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31221 p hg
    simpa only [d259096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31223 (p : Pattern) (guard : d259097 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d259097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259096 p = 1 := by simpa only [d259097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31222 p hg
    simpa only [d259097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31224 (p : Pattern) (guard : d259098 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259097 p = 1 := by simpa only [d259098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31223 p hg
    simpa only [d259098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d259098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31225 (p : Pattern) (guard : d259099 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d259099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259098 p = 1 := by simpa only [d259099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31224 p hg
    simpa only [d259099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31226 (p : Pattern) (guard : d259100 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d259100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259099 p = 1 := by simpa only [d259100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31225 p hg
    simpa only [d259100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31227 (p : Pattern) (guard : d260134 p = 1) : d47767 p ≤ (-2 : Int) + d253406 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260134, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d260134, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259100 p = 1 := by simpa only [d260134, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31226 p hg
    simpa only [d260134, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31228 (p : Pattern) (guard : d260135 p = 1) : d47767 p ≤ (-2 : Int) + d253406 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30830 p hg
    simpa only [d260135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260134 p = 1 := by simpa only [d260135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31227 p hg
    simpa only [d260135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31229 (p : Pattern) (guard : d260136 p = 1) : d47767 p ≤ (-2 : Int) + d253406 p := by
  cases selected : p 69 with
  | false =>
    have hg : d260135 p = 1 := by simpa only [d260136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31228 p hg
    simpa only [d260136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30830 p hg
    simpa only [d260136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31230 (p : Pattern) (guard : d260137 p = 1) : d47767 p ≤ (-2 : Int) + d253406 p := by
  cases selected : p 51 with
  | false =>
    have hg : d260136 p = 1 := by simpa only [d260137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31229 p hg
    simpa only [d260137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30830 p hg
    simpa only [d260137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31231 (p : Pattern) (guard : d260138 p = 1) : d47767 p ≤ (-2 : Int) + d253406 p := by
  cases selected : p 50 with
  | false =>
    have hg : d260137 p = 1 := by simpa only [d260138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31230 p hg
    simpa only [d260138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30830 p hg
    simpa only [d260138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31232 (p : Pattern) (guard : d260139 p = 1) : d47768 p ≤ (-2 : Int) + d253407 p := by
  cases selected : p 49 with
  | false =>
    have hg : d260133 p = 1 := by simpa only [d260139, d47768, d253407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31177 p hg
    simpa only [d260139, d47768, d253407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260138 p = 1 := by simpa only [d260139, d47768, d253407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31231 p hg
    simpa only [d260139, d47768, d253407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31233 (p : Pattern) (guard : d1998 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30891 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1997 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31054 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31234 (p : Pattern) (guard : d258933 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1998 p = 1 := by simpa only [d258933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31233 p hg
    simpa only [d258933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258806 p = 1 := by simpa only [d258933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31055 p hg
    simpa only [d258933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31235 (p : Pattern) (guard : d258934 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30891 p hg
    simpa only [d258934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258933 p = 1 := by simpa only [d258934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31234 p hg
    simpa only [d258934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31236 (p : Pattern) (guard : d258935 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 223 with
  | false =>
    have hg : d258934 p = 1 := by simpa only [d258935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31235 p hg
    simpa only [d258935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30891 p hg
    simpa only [d258935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31237 (p : Pattern) (guard : d258936 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258935 p = 1 := by simpa only [d258936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31236 p hg
    simpa only [d258936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30891 p hg
    simpa only [d258936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31238 (p : Pattern) (guard : d258937 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 202 with
  | false =>
    have hg : d258936 p = 1 := by simpa only [d258937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31237 p hg
    simpa only [d258937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30891 p hg
    simpa only [d258937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31239 (p : Pattern) (guard : d258938 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 201 with
  | false =>
    have hg : d258937 p = 1 := by simpa only [d258938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31238 p hg
    simpa only [d258938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258811 p = 1 := by simpa only [d258938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31060 p hg
    simpa only [d258938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31240 (p : Pattern) (guard : d258939 p = 1) : d47652 p ≤ (-2 : Int) + d253301 p := by
  cases selected : p 182 with
  | false =>
    have hg : d258938 p = 1 := by simpa only [d258939, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31239 p hg
    simpa only [d258939, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258939, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30903 p hg
    simpa only [d258939, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31241 (p : Pattern) (guard : d258940 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 201 with
  | false =>
    have hg : d258811 p = 1 := by simpa only [d258940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31060 p hg
    simpa only [d258940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30891 p hg
    simpa only [d258940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31242 (p : Pattern) (guard : d258941 p = 1) : d47652 p ≤ (-2 : Int) + d253301 p := by
  cases selected : p 182 with
  | false =>
    have hg : d258940 p = 1 := by simpa only [d258941, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31241 p hg
    simpa only [d258941, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258941, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30903 p hg
    simpa only [d258941, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31243 (p : Pattern) (guard : d258942 p = 1) : d47652 p ≤ (-2 : Int) + d253301 p := by
  cases selected : p 180 with
  | false =>
    have hg : d258939 p = 1 := by simpa only [d258942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31240 p hg
    simpa only [d258942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258941 p = 1 := by simpa only [d258942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31242 p hg
    simpa only [d258942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31244 (p : Pattern) (guard : d259014 p = 1) : d47652 p ≤ (-2 : Int) + d253301 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30890 p hg
    simpa only [d259014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258942 p = 1 := by simpa only [d259014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31243 p hg
    simpa only [d259014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31245 (p : Pattern) (guard : d258943 p = 1) : d47797 p ≤ (-2 : Int) + d253434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d258942 p = 1 := by simpa only [d258943, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31126 p hg
    simpa only [d258943, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258943, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30852 p hg
    simpa only [d258943, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31246 (p : Pattern) (guard : d259015 p = 1) : d47798 p ≤ (-2 : Int) + d253435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259014 p = 1 := by simpa only [d259015, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31244 p hg
    simpa only [d259015, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258943 p = 1 := by simpa only [d259015, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31245 p hg
    simpa only [d259015, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31247 (p : Pattern) (guard : d1998 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30909 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1997 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31068 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31248 (p : Pattern) (guard : d258933 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1998 p = 1 := by simpa only [d258933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31247 p hg
    simpa only [d258933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258806 p = 1 := by simpa only [d258933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31069 p hg
    simpa only [d258933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31249 (p : Pattern) (guard : d258934 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30909 p hg
    simpa only [d258934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258933 p = 1 := by simpa only [d258934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31248 p hg
    simpa only [d258934, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
