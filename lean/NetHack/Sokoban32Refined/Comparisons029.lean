/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons028
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare4060 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d795 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4061 (p : Pattern) (guard : d1249 p = 1) : d361 p ≤ (0 : Int) + d795 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1249, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4059 p hg
    simpa only [d1249, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1249, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4060 p hg
    simpa only [d1249, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4062 (p : Pattern) (guard : d1249 p = 1) : d361 p ≤ (0 : Int) + d796 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1249, d361, d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4059 p hg
    simpa only [d1249, d361, d796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1249, d361, d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4031 p hg
    simpa only [d1249, d361, d796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4063 (p : Pattern) (guard : d1249 p = 1) : d361 p ≤ (0 : Int) + d797 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4061 p hg
    simpa only [d797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4062 p hg
    simpa only [d797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4064 (p : Pattern) (guard : d1249 p = 1) : d362 p ≤ (0 : Int) + d798 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d362, d798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4062 p hg
    simpa only [d362, d798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d362, d798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4032 p hg
    simpa only [d362, d798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4065 (p : Pattern) (guard : d1249 p = 1) : d363 p ≤ (0 : Int) + d799 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d363, d799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4063 p hg
    simpa only [d363, d799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d363, d799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4064 p hg
    simpa only [d363, d799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4066 (p : Pattern) (guard : d1249 p = 1) : d364 p ≤ (0 : Int) + d800 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d364, d800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4057 p hg
    simpa only [d364, d800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d364, d800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4065 p hg
    simpa only [d364, d800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4067 (p : Pattern) (guard : d1249 p = 1) : d365 p ≤ (0 : Int) + d801 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d365, d801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4051 p hg
    simpa only [d365, d801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d365, d801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4036 p hg
    simpa only [d365, d801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4068 (p : Pattern) (guard : d1249 p = 1) : d366 p ≤ (0 : Int) + d802 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d366, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4052 p hg
    simpa only [d366, d802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d366, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4067 p hg
    simpa only [d366, d802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4069 (p : Pattern) (guard : d1249 p = 1) : d367 p ≤ (0 : Int) + d803 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d367, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4038 p hg
    simpa only [d367, d803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d367, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4068 p hg
    simpa only [d367, d803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4070 (p : Pattern) (guard : d1249 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare4071 (p : Pattern) (guard : d1249 p = 1) : d368 p ≤ (0 : Int) + d804 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d368, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4062 p hg
    simpa only [d368, d804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d368, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4070 p hg
    simpa only [d368, d804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4072 (p : Pattern) (guard : d1249 p = 1) : d369 p ≤ (0 : Int) + d805 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d369, d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4063 p hg
    simpa only [d369, d805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d369, d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4071 p hg
    simpa only [d369, d805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4073 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d794 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4074 (p : Pattern) (guard : d1249 p = 1) : d370 p ≤ (0 : Int) + d794 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1249, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4058 p hg
    simpa only [d1249, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1249, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4073 p hg
    simpa only [d1249, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4075 (p : Pattern) (guard : d1249 p = 1) : d370 p ≤ (0 : Int) + d806 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1249, d370, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4058 p hg
    simpa only [d1249, d370, d806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1249, d370, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4035 p hg
    simpa only [d1249, d370, d806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4076 (p : Pattern) (guard : d1249 p = 1) : d370 p ≤ (0 : Int) + d807 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4074 p hg
    simpa only [d807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4075 p hg
    simpa only [d807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4077 (p : Pattern) (guard : d1249 p = 1) : d371 p ≤ (0 : Int) + d808 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d371, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4075 p hg
    simpa only [d371, d808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d371, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4070 p hg
    simpa only [d371, d808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4078 (p : Pattern) (guard : d1249 p = 1) : d372 p ≤ (0 : Int) + d809 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d372, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4076 p hg
    simpa only [d372, d809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d372, d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4077 p hg
    simpa only [d372, d809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4079 (p : Pattern) (guard : d1249 p = 1) : d373 p ≤ (0 : Int) + d810 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d373, d810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4072 p hg
    simpa only [d373, d810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d373, d810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4078 p hg
    simpa only [d373, d810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4080 (p : Pattern) (guard : d1249 p = 1) : d374 p ≤ (0 : Int) + d811 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d374, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4069 p hg
    simpa only [d374, d811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d374, d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4079 p hg
    simpa only [d374, d811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4081 (p : Pattern) (guard : d1249 p = 1) : d375 p ≤ (0 : Int) + d812 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d375, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4066 p hg
    simpa only [d375, d812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d375, d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4080 p hg
    simpa only [d375, d812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4082 (p : Pattern) (guard : d1249 p = 1) : d376 p ≤ (0 : Int) + d813 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d376, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4046 p hg
    simpa only [d376, d813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d376, d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4081 p hg
    simpa only [d376, d813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4083 (p : Pattern) (guard : d1249 p = 1) : d377 p ≤ (0 : Int) + d814 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d377, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4038 p hg
    simpa only [d377, d814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d377, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4044 p hg
    simpa only [d377, d814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4084 (p : Pattern) (guard : d1249 p = 1) : d378 p ≤ (0 : Int) + d815 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d378, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4028 p hg
    simpa only [d378, d815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d378, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4083 p hg
    simpa only [d378, d815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4085 (p : Pattern) (guard : d1249 p = 1) : d379 p ≤ (0 : Int) + d816 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d379, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4075 p hg
    simpa only [d379, d816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d379, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4036 p hg
    simpa only [d379, d816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4086 (p : Pattern) (guard : d1249 p = 1) : d380 p ≤ (0 : Int) + d817 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d380, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4076 p hg
    simpa only [d380, d817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d380, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4085 p hg
    simpa only [d380, d817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4087 (p : Pattern) (guard : d1249 p = 1) : d381 p ≤ (0 : Int) + d818 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d381, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4065 p hg
    simpa only [d381, d818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d381, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4086 p hg
    simpa only [d381, d818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4088 (p : Pattern) (guard : d1249 p = 1) : d382 p ≤ (0 : Int) + d819 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d382, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4057 p hg
    simpa only [d382, d819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d382, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4087 p hg
    simpa only [d382, d819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4089 (p : Pattern) (guard : d1249 p = 1) : d383 p ≤ (0 : Int) + d820 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d383, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4038 p hg
    simpa only [d383, d820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d383, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4043 p hg
    simpa only [d383, d820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4090 (p : Pattern) (guard : d1249 p = 1) : d384 p ≤ (0 : Int) + d821 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d384, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4078 p hg
    simpa only [d384, d821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d384, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4070 p hg
    simpa only [d384, d821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4091 (p : Pattern) (guard : d1249 p = 1) : d385 p ≤ (0 : Int) + d822 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d385, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4089 p hg
    simpa only [d385, d822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d385, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4090 p hg
    simpa only [d385, d822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4092 (p : Pattern) (guard : d1249 p = 1) : d386 p ≤ (0 : Int) + d823 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d386, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4088 p hg
    simpa only [d386, d823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d386, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4091 p hg
    simpa only [d386, d823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4093 (p : Pattern) (guard : d1249 p = 1) : d387 p ≤ (0 : Int) + d824 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d387, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4084 p hg
    simpa only [d387, d824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d387, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4092 p hg
    simpa only [d387, d824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4094 (p : Pattern) (guard : d1249 p = 1) : d388 p ≤ (0 : Int) + d825 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d388, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4082 p hg
    simpa only [d388, d825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d388, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4093 p hg
    simpa only [d388, d825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4095 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d654 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4096 (p : Pattern) (guard : d1250 p = 1) : d328 p ≤ (0 : Int) + d654 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1250, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2795 p hg
    simpa only [d1250, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1250, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4095 p hg
    simpa only [d1250, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4097 (p : Pattern) (guard : d917 p = 1) : d4 p ≤ (0 : Int) + d4 p := by
  omega
theorem compare4098 (p : Pattern) (guard : d1240 p = 1) : d6 p ≤ (0 : Int) + d7 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1240, d6, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4097 p hg
    simpa only [d1240, d6, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1240, d6, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2786 p hg
    simpa only [d1240, d6, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4099 (p : Pattern) (guard : d1240 p = 1) : d7 p ≤ (0 : Int) + d7 p := by
  omega
theorem compare4100 (p : Pattern) (guard : d1240 p = 1) : d8 p ≤ (0 : Int) + d7 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4098 p hg
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4099 p hg
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4101 (p : Pattern) (guard : d917 p = 1) : d10 p ≤ (0 : Int) + d10 p := by
  omega
theorem compare4102 (p : Pattern) (guard : d1240 p = 1) : d12 p ≤ (0 : Int) + d13 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1240, d12, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4101 p hg
    simpa only [d1240, d12, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1240, d12, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2790 p hg
    simpa only [d1240, d12, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4103 (p : Pattern) (guard : d1240 p = 1) : d13 p ≤ (0 : Int) + d13 p := by
  omega
theorem compare4104 (p : Pattern) (guard : d1240 p = 1) : d14 p ≤ (0 : Int) + d13 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4102 p hg
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4103 p hg
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4105 (p : Pattern) (guard : d1240 p = 1) : d15 p ≤ (0 : Int) + d653 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d15, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4100 p hg
    simpa only [d15, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d15, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4104 p hg
    simpa only [d15, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4106 (p : Pattern) (guard : d1240 p = 1) : d16 p ≤ (0 : Int) + d654 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d16, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4100 p hg
    simpa only [d16, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d16, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4105 p hg
    simpa only [d16, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4107 (p : Pattern) (guard : d1253 p = 1) : d328 p ≤ (0 : Int) + d654 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d1253, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4106 p hg
    simpa only [d1253, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1253, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4095 p hg
    simpa only [d1253, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4108 (p : Pattern) (guard : d1254 p = 1) : d328 p ≤ (0 : Int) + d654 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1250 p = 1 := by simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4096 p hg
    simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1253 p = 1 := by simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4107 p hg
    simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4109 (p : Pattern) (guard : d917 p = 1) : d5 p ≤ (0 : Int) + d4 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d5, d4, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare103 p hg
    simpa only [d917, d5, d4, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d5, d4, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare967 p hg
    simpa only [d917, d5, d4, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4110 (p : Pattern) (guard : d1240 p = 1) : d37 p ≤ (0 : Int) + d7 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1240, d37, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4109 p hg
    simpa only [d1240, d37, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1240, d37, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1240, d37, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4111 (p : Pattern) (guard : d1240 p = 1) : d38 p ≤ (0 : Int) + d7 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4098 p hg
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4110 p hg
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4112 (p : Pattern) (guard : d917 p = 1) : d11 p ≤ (0 : Int) + d10 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d11, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare698 p hg
    simpa only [d917, d11, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d11, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare974 p hg
    simpa only [d917, d11, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4113 (p : Pattern) (guard : d1240 p = 1) : d39 p ≤ (0 : Int) + d13 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1240, d39, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4112 p hg
    simpa only [d1240, d39, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1240, d39, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1240, d39, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4114 (p : Pattern) (guard : d1240 p = 1) : d40 p ≤ (0 : Int) + d13 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4102 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4113 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4115 (p : Pattern) (guard : d1240 p = 1) : d41 p ≤ (0 : Int) + d653 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d41, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4111 p hg
    simpa only [d41, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d41, d653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4114 p hg
    simpa only [d41, d653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4116 (p : Pattern) (guard : d1240 p = 1) : d42 p ≤ (0 : Int) + d654 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d42, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4111 p hg
    simpa only [d42, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d42, d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4115 p hg
    simpa only [d42, d654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4117 (p : Pattern) (guard : d1253 p = 1) : d329 p ≤ (0 : Int) + d654 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d1253, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4116 p hg
    simpa only [d1253, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1253, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4095 p hg
    simpa only [d1253, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4118 (p : Pattern) (guard : d1254 p = 1) : d330 p ≤ (0 : Int) + d654 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1250 p = 1 := by simpa only [d1254, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4096 p hg
    simpa only [d1254, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1253 p = 1 := by simpa only [d1254, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4117 p hg
    simpa only [d1254, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4119 (p : Pattern) (guard : d1254 p = 1) : d331 p ≤ (0 : Int) + d654 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4108 p hg
    simpa only [d331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4118 p hg
    simpa only [d331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4120 (p : Pattern) (guard : d1250 p = 1) : d332 p ≤ (0 : Int) + d653 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1250, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2794 p hg
    simpa only [d1250, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1250, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2910 p hg
    simpa only [d1250, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4121 (p : Pattern) (guard : d1253 p = 1) : d332 p ≤ (0 : Int) + d653 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d1253, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4105 p hg
    simpa only [d1253, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1253, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2910 p hg
    simpa only [d1253, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4122 (p : Pattern) (guard : d1254 p = 1) : d332 p ≤ (0 : Int) + d653 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1250 p = 1 := by simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4120 p hg
    simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1253 p = 1 := by simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4121 p hg
    simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4123 (p : Pattern) (guard : d1253 p = 1) : d333 p ≤ (0 : Int) + d653 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d1253, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4115 p hg
    simpa only [d1253, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1253, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2910 p hg
    simpa only [d1253, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4124 (p : Pattern) (guard : d1254 p = 1) : d334 p ≤ (0 : Int) + d653 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1250 p = 1 := by simpa only [d1254, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4120 p hg
    simpa only [d1254, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1253 p = 1 := by simpa only [d1254, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4123 p hg
    simpa only [d1254, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4125 (p : Pattern) (guard : d1254 p = 1) : d335 p ≤ (0 : Int) + d653 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4122 p hg
    simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4124 p hg
    simpa only [d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4126 (p : Pattern) (guard : d1250 p = 1) : d336 p ≤ (0 : Int) + d656 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1250, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2818 p hg
    simpa only [d1250, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1250, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2912 p hg
    simpa only [d1250, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4127 (p : Pattern) (guard : d1240 p = 1) : d52 p ≤ (0 : Int) + d655 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d52, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4100 p hg
    simpa only [d52, d655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d52, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3436 p hg
    simpa only [d52, d655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4128 (p : Pattern) (guard : d1240 p = 1) : d53 p ≤ (0 : Int) + d656 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d53, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4105 p hg
    simpa only [d53, d656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d53, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4127 p hg
    simpa only [d53, d656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4129 (p : Pattern) (guard : d1253 p = 1) : d336 p ≤ (0 : Int) + d656 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d1253, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4128 p hg
    simpa only [d1253, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1253, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2912 p hg
    simpa only [d1253, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4130 (p : Pattern) (guard : d1254 p = 1) : d336 p ≤ (0 : Int) + d656 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1250 p = 1 := by simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4126 p hg
    simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1253 p = 1 := by simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4129 p hg
    simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4131 (p : Pattern) (guard : d1240 p = 1) : d61 p ≤ (0 : Int) + d655 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d61, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4111 p hg
    simpa only [d61, d655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d61, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3436 p hg
    simpa only [d61, d655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4132 (p : Pattern) (guard : d1240 p = 1) : d62 p ≤ (0 : Int) + d656 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d62, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4115 p hg
    simpa only [d62, d656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d62, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4131 p hg
    simpa only [d62, d656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4133 (p : Pattern) (guard : d1253 p = 1) : d337 p ≤ (0 : Int) + d656 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d1253, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4132 p hg
    simpa only [d1253, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1253, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2912 p hg
    simpa only [d1253, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4134 (p : Pattern) (guard : d1254 p = 1) : d338 p ≤ (0 : Int) + d656 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1250 p = 1 := by simpa only [d1254, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4126 p hg
    simpa only [d1254, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1253 p = 1 := by simpa only [d1254, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4133 p hg
    simpa only [d1254, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4135 (p : Pattern) (guard : d1254 p = 1) : d339 p ≤ (0 : Int) + d656 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4130 p hg
    simpa only [d339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4134 p hg
    simpa only [d339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4136 (p : Pattern) (guard : d1254 p = 1) : d340 p ≤ (0 : Int) + d657 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d340, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4125 p hg
    simpa only [d340, d657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d340, d657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4135 p hg
    simpa only [d340, d657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4137 (p : Pattern) (guard : d1254 p = 1) : d341 p ≤ (0 : Int) + d658 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d341, d658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4119 p hg
    simpa only [d341, d658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d341, d658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4136 p hg
    simpa only [d341, d658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4138 (p : Pattern) (guard : d1240 p = 1) : d68 p ≤ (0 : Int) + d659 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d68, d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4114 p hg
    simpa only [d68, d659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d68, d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3436 p hg
    simpa only [d68, d659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4139 (p : Pattern) (guard : d1240 p = 1) : d69 p ≤ (0 : Int) + d660 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d69, d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4114 p hg
    simpa only [d69, d660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d69, d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4138 p hg
    simpa only [d69, d660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4140 (p : Pattern) (guard : d1253 p = 1) : d342 p ≤ (0 : Int) + d660 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d1253, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4139 p hg
    simpa only [d1253, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1253, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2936 p hg
    simpa only [d1253, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4141 (p : Pattern) (guard : d1254 p = 1) : d343 p ≤ (0 : Int) + d661 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1250 p = 1 := by simpa only [d1254, d343, d661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4096 p hg
    simpa only [d1254, d343, d661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1253 p = 1 := by simpa only [d1254, d343, d661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4140 p hg
    simpa only [d1254, d343, d661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4142 (p : Pattern) (guard : d1254 p = 1) : d344 p ≤ (0 : Int) + d662 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d344, d662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4108 p hg
    simpa only [d344, d662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d344, d662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4141 p hg
    simpa only [d344, d662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4143 (p : Pattern) (guard : d1253 p = 1) : d345 p ≤ (0 : Int) + d659 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d1253, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4138 p hg
    simpa only [d1253, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1253, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2897 p hg
    simpa only [d1253, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4144 (p : Pattern) (guard : d1254 p = 1) : d346 p ≤ (0 : Int) + d663 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1250 p = 1 := by simpa only [d1254, d346, d663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4096 p hg
    simpa only [d1254, d346, d663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1253 p = 1 := by simpa only [d1254, d346, d663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4143 p hg
    simpa only [d1254, d346, d663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4145 (p : Pattern) (guard : d1254 p = 1) : d347 p ≤ (0 : Int) + d664 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d347, d664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4108 p hg
    simpa only [d347, d664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d347, d664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4144 p hg
    simpa only [d347, d664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4146 (p : Pattern) (guard : d1254 p = 1) : d348 p ≤ (0 : Int) + d665 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d348, d665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4142 p hg
    simpa only [d348, d665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d348, d665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4145 p hg
    simpa only [d348, d665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4147 (p : Pattern) (guard : d1254 p = 1) : d349 p ≤ (0 : Int) + d666 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1250 p = 1 := by simpa only [d1254, d349, d666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4120 p hg
    simpa only [d1254, d349, d666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1253 p = 1 := by simpa only [d1254, d349, d666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4143 p hg
    simpa only [d1254, d349, d666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4148 (p : Pattern) (guard : d1254 p = 1) : d350 p ≤ (0 : Int) + d667 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d350, d667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4122 p hg
    simpa only [d350, d667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d350, d667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4147 p hg
    simpa only [d350, d667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4149 (p : Pattern) (guard : d1254 p = 1) : d351 p ≤ (0 : Int) + d668 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1250 p = 1 := by simpa only [d1254, d351, d668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4126 p hg
    simpa only [d1254, d351, d668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1253 p = 1 := by simpa only [d1254, d351, d668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4143 p hg
    simpa only [d1254, d351, d668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4150 (p : Pattern) (guard : d1254 p = 1) : d352 p ≤ (0 : Int) + d669 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d352, d669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4130 p hg
    simpa only [d352, d669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d352, d669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4149 p hg
    simpa only [d352, d669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4151 (p : Pattern) (guard : d1254 p = 1) : d353 p ≤ (0 : Int) + d670 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d353, d670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4148 p hg
    simpa only [d353, d670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d353, d670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4150 p hg
    simpa only [d353, d670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4152 (p : Pattern) (guard : d1254 p = 1) : d354 p ≤ (0 : Int) + d671 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d354, d671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4146 p hg
    simpa only [d354, d671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d354, d671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4151 p hg
    simpa only [d354, d671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4153 (p : Pattern) (guard : d1254 p = 1) : d355 p ≤ (0 : Int) + d672 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d355, d672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4137 p hg
    simpa only [d355, d672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d355, d672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4152 p hg
    simpa only [d355, d672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4154 (p : Pattern) (guard : d1250 p = 1) : d356 p ≤ (0 : Int) + d673 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1250, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2842 p hg
    simpa only [d1250, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1250, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2961 p hg
    simpa only [d1250, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4155 (p : Pattern) (guard : d1240 p = 1) : d86 p ≤ (0 : Int) + d673 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d86, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4100 p hg
    simpa only [d86, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d86, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4127 p hg
    simpa only [d86, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4156 (p : Pattern) (guard : d1253 p = 1) : d356 p ≤ (0 : Int) + d673 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d1253, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4155 p hg
    simpa only [d1253, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1253, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2961 p hg
    simpa only [d1253, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4157 (p : Pattern) (guard : d1254 p = 1) : d356 p ≤ (0 : Int) + d673 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1250 p = 1 := by simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4154 p hg
    simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1253 p = 1 := by simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4156 p hg
    simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4158 (p : Pattern) (guard : d1240 p = 1) : d92 p ≤ (0 : Int) + d673 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d92, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4111 p hg
    simpa only [d92, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d92, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4131 p hg
    simpa only [d92, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4159 (p : Pattern) (guard : d1253 p = 1) : d357 p ≤ (0 : Int) + d673 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d1253, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4158 p hg
    simpa only [d1253, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1253, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2961 p hg
    simpa only [d1253, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4160 (p : Pattern) (guard : d1254 p = 1) : d358 p ≤ (0 : Int) + d673 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1250 p = 1 := by simpa only [d1254, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4154 p hg
    simpa only [d1254, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1253 p = 1 := by simpa only [d1254, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4159 p hg
    simpa only [d1254, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4161 (p : Pattern) (guard : d1254 p = 1) : d359 p ≤ (0 : Int) + d673 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4157 p hg
    simpa only [d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4160 p hg
    simpa only [d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4162 (p : Pattern) (guard : d1254 p = 1) : d360 p ≤ (0 : Int) + d674 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d360, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4119 p hg
    simpa only [d360, d674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d360, d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4161 p hg
    simpa only [d360, d674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4163 (p : Pattern) (guard : d1250 p = 1) : d361 p ≤ (0 : Int) + d660 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1250, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2851 p hg
    simpa only [d1250, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1250, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2936 p hg
    simpa only [d1250, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4164 (p : Pattern) (guard : d1240 p = 1) : d97 p ≤ (0 : Int) + d659 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d97, d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4104 p hg
    simpa only [d97, d659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d97, d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3436 p hg
    simpa only [d97, d659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4165 (p : Pattern) (guard : d1240 p = 1) : d98 p ≤ (0 : Int) + d660 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d98, d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4104 p hg
    simpa only [d98, d660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1240 p = 1 := by simpa only [d98, d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4164 p hg
    simpa only [d98, d660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4166 (p : Pattern) (guard : d1253 p = 1) : d361 p ≤ (0 : Int) + d660 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d1253, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4165 p hg
    simpa only [d1253, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1253, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2936 p hg
    simpa only [d1253, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4167 (p : Pattern) (guard : d1254 p = 1) : d361 p ≤ (0 : Int) + d660 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1250 p = 1 := by simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4163 p hg
    simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1253 p = 1 := by simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4166 p hg
    simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4168 (p : Pattern) (guard : d1254 p = 1) : d362 p ≤ (0 : Int) + d660 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1250 p = 1 := by simpa only [d1254, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4163 p hg
    simpa only [d1254, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1253 p = 1 := by simpa only [d1254, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4140 p hg
    simpa only [d1254, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4169 (p : Pattern) (guard : d1254 p = 1) : d363 p ≤ (0 : Int) + d660 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4167 p hg
    simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4168 p hg
    simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4170 (p : Pattern) (guard : d1254 p = 1) : d364 p ≤ (0 : Int) + d675 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d364, d675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4162 p hg
    simpa only [d364, d675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d364, d675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4169 p hg
    simpa only [d364, d675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4171 (p : Pattern) (guard : d1254 p = 1) : d365 p ≤ (0 : Int) + d676 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1250 p = 1 := by simpa only [d1254, d365, d676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4154 p hg
    simpa only [d1254, d365, d676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1253 p = 1 := by simpa only [d1254, d365, d676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4143 p hg
    simpa only [d1254, d365, d676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4172 (p : Pattern) (guard : d1254 p = 1) : d366 p ≤ (0 : Int) + d677 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d366, d677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4157 p hg
    simpa only [d366, d677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d366, d677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4171 p hg
    simpa only [d366, d677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4173 (p : Pattern) (guard : d1254 p = 1) : d367 p ≤ (0 : Int) + d678 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d367, d678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4145 p hg
    simpa only [d367, d678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d367, d678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4172 p hg
    simpa only [d367, d678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4174 (p : Pattern) (guard : d1253 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare4175 (p : Pattern) (guard : d1254 p = 1) : d368 p ≤ (0 : Int) + d679 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1250 p = 1 := by simpa only [d1254, d368, d679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4163 p hg
    simpa only [d1254, d368, d679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1253 p = 1 := by simpa only [d1254, d368, d679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4174 p hg
    simpa only [d1254, d368, d679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4176 (p : Pattern) (guard : d1254 p = 1) : d369 p ≤ (0 : Int) + d680 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d369, d680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4167 p hg
    simpa only [d369, d680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d369, d680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4175 p hg
    simpa only [d369, d680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4177 (p : Pattern) (guard : d1250 p = 1) : d370 p ≤ (0 : Int) + d659 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1250, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2850 p hg
    simpa only [d1250, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1250, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2897 p hg
    simpa only [d1250, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4178 (p : Pattern) (guard : d1253 p = 1) : d370 p ≤ (0 : Int) + d659 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1240 p = 1 := by simpa only [d1253, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4164 p hg
    simpa only [d1253, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1253, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2897 p hg
    simpa only [d1253, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4179 (p : Pattern) (guard : d1254 p = 1) : d370 p ≤ (0 : Int) + d659 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1250 p = 1 := by simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4177 p hg
    simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1253 p = 1 := by simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4178 p hg
    simpa only [d1254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4180 (p : Pattern) (guard : d1254 p = 1) : d371 p ≤ (0 : Int) + d681 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1250 p = 1 := by simpa only [d1254, d371, d681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4177 p hg
    simpa only [d1254, d371, d681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1253 p = 1 := by simpa only [d1254, d371, d681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4174 p hg
    simpa only [d1254, d371, d681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4181 (p : Pattern) (guard : d1254 p = 1) : d372 p ≤ (0 : Int) + d682 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d372, d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4179 p hg
    simpa only [d372, d682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d372, d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4180 p hg
    simpa only [d372, d682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4182 (p : Pattern) (guard : d1254 p = 1) : d373 p ≤ (0 : Int) + d683 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d373, d683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4176 p hg
    simpa only [d373, d683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d373, d683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4181 p hg
    simpa only [d373, d683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4183 (p : Pattern) (guard : d1254 p = 1) : d374 p ≤ (0 : Int) + d684 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d374, d684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4173 p hg
    simpa only [d374, d684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d374, d684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4182 p hg
    simpa only [d374, d684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4184 (p : Pattern) (guard : d1254 p = 1) : d375 p ≤ (0 : Int) + d685 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d375, d685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4170 p hg
    simpa only [d375, d685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d375, d685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4183 p hg
    simpa only [d375, d685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4185 (p : Pattern) (guard : d1254 p = 1) : d376 p ≤ (0 : Int) + d686 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d376, d686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4153 p hg
    simpa only [d376, d686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d376, d686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4184 p hg
    simpa only [d376, d686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4186 (p : Pattern) (guard : d1254 p = 1) : d377 p ≤ (0 : Int) + d687 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d377, d687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4145 p hg
    simpa only [d377, d687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d377, d687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4151 p hg
    simpa only [d377, d687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4187 (p : Pattern) (guard : d1254 p = 1) : d378 p ≤ (0 : Int) + d688 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d378, d688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4137 p hg
    simpa only [d378, d688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d378, d688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4186 p hg
    simpa only [d378, d688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4188 (p : Pattern) (guard : d1254 p = 1) : d379 p ≤ (0 : Int) + d659 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1250 p = 1 := by simpa only [d1254, d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4177 p hg
    simpa only [d1254, d379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1253 p = 1 := by simpa only [d1254, d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4143 p hg
    simpa only [d1254, d379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4189 (p : Pattern) (guard : d1254 p = 1) : d380 p ≤ (0 : Int) + d659 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4179 p hg
    simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4188 p hg
    simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4190 (p : Pattern) (guard : d1254 p = 1) : d381 p ≤ (0 : Int) + d689 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d381, d689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4169 p hg
    simpa only [d381, d689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d381, d689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4189 p hg
    simpa only [d381, d689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4191 (p : Pattern) (guard : d1254 p = 1) : d382 p ≤ (0 : Int) + d690 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d382, d690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4162 p hg
    simpa only [d382, d690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d382, d690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4190 p hg
    simpa only [d382, d690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4192 (p : Pattern) (guard : d1254 p = 1) : d383 p ≤ (0 : Int) + d691 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d383, d691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4145 p hg
    simpa only [d383, d691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d383, d691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4150 p hg
    simpa only [d383, d691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4193 (p : Pattern) (guard : d1254 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare4194 (p : Pattern) (guard : d1254 p = 1) : d384 p ≤ (0 : Int) + d692 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d384, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4181 p hg
    simpa only [d384, d692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d384, d692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4193 p hg
    simpa only [d384, d692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4195 (p : Pattern) (guard : d1254 p = 1) : d385 p ≤ (0 : Int) + d693 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d385, d693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4192 p hg
    simpa only [d385, d693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d385, d693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4194 p hg
    simpa only [d385, d693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4196 (p : Pattern) (guard : d1254 p = 1) : d386 p ≤ (0 : Int) + d694 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d386, d694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4191 p hg
    simpa only [d386, d694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d386, d694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4195 p hg
    simpa only [d386, d694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4197 (p : Pattern) (guard : d1254 p = 1) : d387 p ≤ (0 : Int) + d695 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d387, d695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4187 p hg
    simpa only [d387, d695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d387, d695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4196 p hg
    simpa only [d387, d695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4198 (p : Pattern) (guard : d1254 p = 1) : d388 p ≤ (0 : Int) + d696 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1254 p = 1 := by simpa only [d388, d696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4185 p hg
    simpa only [d388, d696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1254 p = 1 := by simpa only [d388, d696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4197 p hg
    simpa only [d388, d696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4199 (p : Pattern) (guard : d985 p = 1) : d17 p ≤ (0 : Int) + d17 p := by
  omega
end NetHack.Sokoban32Refined
