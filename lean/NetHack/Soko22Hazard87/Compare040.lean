import NetHack.Soko22Hazard87.Compare039
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare10000 (p : Pattern) (guard : d53826 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 257 with
  | false =>
    have hg : d53825 p = 1 := by simpa only [d53826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9999 p hg
    simpa only [d53826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10001 (p : Pattern) (guard : d53827 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 256 with
  | false =>
    have hg : d53826 p = 1 := by simpa only [d53827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10000 p hg
    simpa only [d53827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10002 (p : Pattern) (guard : d53828 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 255 with
  | false =>
    have hg : d53827 p = 1 := by simpa only [d53828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10001 p hg
    simpa only [d53828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10003 (p : Pattern) (guard : d53829 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 254 with
  | false =>
    have hg : d53828 p = 1 := by simpa only [d53829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10002 p hg
    simpa only [d53829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10004 (p : Pattern) (guard : d53830 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 253 with
  | false =>
    have hg : d53829 p = 1 := by simpa only [d53830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10003 p hg
    simpa only [d53830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10005 (p : Pattern) (guard : d53831 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 252 with
  | false =>
    have hg : d53830 p = 1 := by simpa only [d53831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10004 p hg
    simpa only [d53831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10006 (p : Pattern) (guard : d53832 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 251 with
  | false =>
    have hg : d53831 p = 1 := by simpa only [d53832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10005 p hg
    simpa only [d53832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10007 (p : Pattern) (guard : d53833 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 250 with
  | false =>
    have hg : d53832 p = 1 := by simpa only [d53833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10006 p hg
    simpa only [d53833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10008 (p : Pattern) (guard : d53834 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 249 with
  | false =>
    have hg : d53833 p = 1 := by simpa only [d53834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10007 p hg
    simpa only [d53834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10009 (p : Pattern) (guard : d53835 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 245 with
  | false =>
    have hg : d53834 p = 1 := by simpa only [d53835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10008 p hg
    simpa only [d53835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10010 (p : Pattern) (guard : d53836 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 200 with
  | false =>
    have hg : d53835 p = 1 := by simpa only [d53836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10009 p hg
    simpa only [d53836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10011 (p : Pattern) (guard : d53837 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 199 with
  | false =>
    have hg : d53836 p = 1 := by simpa only [d53837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10010 p hg
    simpa only [d53837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10012 (p : Pattern) (guard : d53838 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 186 with
  | false =>
    have hg : d53837 p = 1 := by simpa only [d53838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10011 p hg
    simpa only [d53838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10013 (p : Pattern) (guard : d53839 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 185 with
  | false =>
    have hg : d53838 p = 1 := by simpa only [d53839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10012 p hg
    simpa only [d53839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10014 (p : Pattern) (guard : d53840 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 184 with
  | false =>
    have hg : d53839 p = 1 := by simpa only [d53840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10013 p hg
    simpa only [d53840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10015 (p : Pattern) (guard : d53841 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 181 with
  | false =>
    have hg : d53840 p = 1 := by simpa only [d53841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10014 p hg
    simpa only [d53841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10016 (p : Pattern) (guard : d53842 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 177 with
  | false =>
    have hg : d53841 p = 1 := by simpa only [d53842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10015 p hg
    simpa only [d53842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10017 (p : Pattern) (guard : d53843 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 164 with
  | false =>
    have hg : d53842 p = 1 := by simpa only [d53843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10016 p hg
    simpa only [d53843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10018 (p : Pattern) (guard : d53844 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 156 with
  | false =>
    have hg : d53843 p = 1 := by simpa only [d53844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10017 p hg
    simpa only [d53844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10019 (p : Pattern) (guard : d53845 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 155 with
  | false =>
    have hg : d53844 p = 1 := by simpa only [d53845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10018 p hg
    simpa only [d53845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10020 (p : Pattern) (guard : d53846 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 134 with
  | false =>
    have hg : d53845 p = 1 := by simpa only [d53846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10019 p hg
    simpa only [d53846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10021 (p : Pattern) (guard : d53847 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 133 with
  | false =>
    have hg : d53846 p = 1 := by simpa only [d53847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10020 p hg
    simpa only [d53847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10022 (p : Pattern) (guard : d53848 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 120 with
  | false =>
    have hg : d53847 p = 1 := by simpa only [d53848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10021 p hg
    simpa only [d53848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10023 (p : Pattern) (guard : d53849 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 118 with
  | false =>
    have hg : d53848 p = 1 := by simpa only [d53849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10022 p hg
    simpa only [d53849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10024 (p : Pattern) (guard : d53850 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 114 with
  | false =>
    have hg : d53849 p = 1 := by simpa only [d53850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10023 p hg
    simpa only [d53850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10025 (p : Pattern) (guard : d53851 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 111 with
  | false =>
    have hg : d53850 p = 1 := by simpa only [d53851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10024 p hg
    simpa only [d53851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10026 (p : Pattern) (guard : d53852 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 98 with
  | false =>
    have hg : d53851 p = 1 := by simpa only [d53852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10025 p hg
    simpa only [d53852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10027 (p : Pattern) (guard : d53853 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 97 with
  | false =>
    have hg : d53852 p = 1 := by simpa only [d53853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10026 p hg
    simpa only [d53853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10028 (p : Pattern) (guard : d53854 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 94 with
  | false =>
    have hg : d53853 p = 1 := by simpa only [d53854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10027 p hg
    simpa only [d53854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10029 (p : Pattern) (guard : d53855 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 76 with
  | false =>
    have hg : d53854 p = 1 := by simpa only [d53855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10028 p hg
    simpa only [d53855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10030 (p : Pattern) (guard : d53856 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 67 with
  | false =>
    have hg : d53855 p = 1 := by simpa only [d53856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10029 p hg
    simpa only [d53856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10031 (p : Pattern) (guard : d53857 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 52 with
  | false =>
    have hg : d53856 p = 1 := by simpa only [d53857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10030 p hg
    simpa only [d53857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10032 (p : Pattern) (guard : d53858 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 47 with
  | false =>
    have hg : d53857 p = 1 := by simpa only [d53858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10031 p hg
    simpa only [d53858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10033 (p : Pattern) (guard : d53859 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 46 with
  | false =>
    have hg : d53858 p = 1 := by simpa only [d53859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10032 p hg
    simpa only [d53859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10034 (p : Pattern) (guard : d53860 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 45 with
  | false =>
    have hg : d53859 p = 1 := by simpa only [d53860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10033 p hg
    simpa only [d53860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10035 (p : Pattern) (guard : d53861 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 30 with
  | false =>
    have hg : d53860 p = 1 := by simpa only [d53861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10034 p hg
    simpa only [d53861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10036 (p : Pattern) (guard : d53862 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 29 with
  | false =>
    have hg : d53861 p = 1 := by simpa only [d53862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10035 p hg
    simpa only [d53862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10037 (p : Pattern) (guard : d53863 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 28 with
  | false =>
    have hg : d53862 p = 1 := by simpa only [d53863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10036 p hg
    simpa only [d53863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10038 (p : Pattern) (guard : d53864 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 27 with
  | false =>
    have hg : d53863 p = 1 := by simpa only [d53864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10037 p hg
    simpa only [d53864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10039 (p : Pattern) (guard : d53865 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 25 with
  | false =>
    have hg : d53864 p = 1 := by simpa only [d53865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10038 p hg
    simpa only [d53865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10040 (p : Pattern) (guard : d0 p = 1) : d48097 p ≤ (-1 : Int) + d47911 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10041 (p : Pattern) (guard : d0 p = 1) : d48097 p ≤ (-2 : Int) + d47911 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10042 (p : Pattern) (guard : d0 p = 1) : d48097 p ≤ (1 : Int) + d99411 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10043 (p : Pattern) (guard : d0 p = 1) : d48097 p ≤ (0 : Int) + d99411 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10044 (p : Pattern) (guard : d0 p = 1) : d48097 p ≤ (-1 : Int) + d48115 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10045 (p : Pattern) (guard : d0 p = 1) : d48097 p ≤ (-2 : Int) + d48115 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10046 (p : Pattern) (guard : d0 p = 1) : d48097 p ≤ (-1 : Int) + d47866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10047 (p : Pattern) (guard : d0 p = 1) : d48097 p ≤ (-2 : Int) + d47866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10048 (p : Pattern) (guard : d0 p = 1) : d48097 p ≤ (1 : Int) + d47866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10049 (p : Pattern) (guard : d0 p = 1) : d48097 p ≤ (0 : Int) + d47866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10050 (p : Pattern) (guard : d0 p = 1) : d48097 p ≤ (-1 : Int) + d48251 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10051 (p : Pattern) (guard : d0 p = 1) : d48097 p ≤ (-2 : Int) + d48251 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10052 (p : Pattern) (guard : d0 p = 1) : d48115 p ≤ (-1 : Int) + d47911 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10053 (p : Pattern) (guard : d0 p = 1) : d48115 p ≤ (-2 : Int) + d47911 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10054 (p : Pattern) (guard : d0 p = 1) : d48115 p ≤ (-1 : Int) + d48251 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10055 (p : Pattern) (guard : d0 p = 1) : d48115 p ≤ (-2 : Int) + d48251 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10056 (p : Pattern) (guard : d0 p = 1) : d48115 p ≤ (-1 : Int) + d100929 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10057 (p : Pattern) (guard : d0 p = 1) : d48115 p ≤ (-2 : Int) + d100929 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10058 (p : Pattern) (guard : d0 p = 1) : d48115 p ≤ (-1 : Int) + d48097 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10059 (p : Pattern) (guard : d0 p = 1) : d48115 p ≤ (-2 : Int) + d48097 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10060 (p : Pattern) (guard : d0 p = 1) : d48115 p ≤ (1 : Int) + d100934 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10061 (p : Pattern) (guard : d0 p = 1) : d48115 p ≤ (0 : Int) + d100934 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10062 (p : Pattern) (guard : d0 p = 1) : d47911 p ≤ (-1 : Int) + d48308 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10063 (p : Pattern) (guard : d0 p = 1) : d47911 p ≤ (-2 : Int) + d48308 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10064 (p : Pattern) (guard : d0 p = 1) : d47911 p ≤ (-1 : Int) + d102102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10065 (p : Pattern) (guard : d0 p = 1) : d47911 p ≤ (-2 : Int) + d102102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10066 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (1 : Int) + d47866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10067 (p : Pattern) (guard : d122301 p = 1) : d47866 p ≤ (1 : Int) + d47866 p := by
  omega
theorem compare10068 (p : Pattern) (guard : d107187 p = 1) : d47866 p ≤ (0 : Int) + d47866 p := by
  omega
theorem compare10069 (p : Pattern) (guard : d0 p = 1) : d48251 p ≤ (-1 : Int) + d48115 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10070 (p : Pattern) (guard : d0 p = 1) : d48251 p ≤ (-2 : Int) + d48115 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10071 (p : Pattern) (guard : d0 p = 1) : d48251 p ≤ (3 : Int) + d126872 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10072 (p : Pattern) (guard : d0 p = 1) : d48251 p ≤ (2 : Int) + d126872 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10073 (p : Pattern) (guard : d0 p = 1) : d48251 p ≤ (-1 : Int) + d48388 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10074 (p : Pattern) (guard : d0 p = 1) : d48251 p ≤ (-2 : Int) + d48388 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10075 (p : Pattern) (guard : d0 p = 1) : d48251 p ≤ (-1 : Int) + d128576 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10076 (p : Pattern) (guard : d0 p = 1) : d48251 p ≤ (-2 : Int) + d128576 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10077 (p : Pattern) (guard : d0 p = 1) : d48251 p ≤ (-1 : Int) + d48097 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10078 (p : Pattern) (guard : d0 p = 1) : d48251 p ≤ (-2 : Int) + d48097 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10079 (p : Pattern) (guard : d0 p = 1) : d48251 p ≤ (-1 : Int) + d48547 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10080 (p : Pattern) (guard : d0 p = 1) : d48251 p ≤ (-2 : Int) + d48547 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10081 (p : Pattern) (guard : d0 p = 1) : d48251 p ≤ (-1 : Int) + d47866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10082 (p : Pattern) (guard : d0 p = 1) : d48251 p ≤ (-2 : Int) + d47866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10083 (p : Pattern) (guard : d0 p = 1) : d48308 p ≤ (-1 : Int) + d47911 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10084 (p : Pattern) (guard : d0 p = 1) : d48308 p ≤ (-2 : Int) + d47911 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10085 (p : Pattern) (guard : d0 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10086 (p : Pattern) (guard : d0 p = 1) : d48293 p ≤ (1 : Int) + d47768 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10087 (p : Pattern) (guard : d0 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10088 (p : Pattern) (guard : d0 p = 1) : d48265 p ≤ (1 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10089 (p : Pattern) (guard : d0 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10090 (p : Pattern) (guard : d0 p = 1) : d48271 p ≤ (1 : Int) + d47697 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10091 (p : Pattern) (guard : d0 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10092 (p : Pattern) (guard : d0 p = 1) : d48272 p ≤ (1 : Int) + d47676 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10093 (p : Pattern) (guard : d9297 p = 1) : d47681 p ≤ (1 : Int) + d47681 p := by
  omega
theorem compare10094 (p : Pattern) (guard : d0 p = 1) : d48010 p ≤ (1 : Int) + d47685 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10095 (p : Pattern) (guard : d9298 p = 1) : d48273 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d9297 p = 1 := by simpa only [d9298, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10093 p hg
    simpa only [d9298, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9298, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10094 p hg
    simpa only [d9298, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10096 (p : Pattern) (guard : d9299 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9299, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10092 p hg
    simpa only [d9299, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9298 p = 1 := by simpa only [d9299, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10095 p hg
    simpa only [d9299, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10097 (p : Pattern) (guard : d9300 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d9299 p = 1 := by simpa only [d9300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10096 p hg
    simpa only [d9300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d9300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10098 (p : Pattern) (guard : d9301 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d9300 p = 1 := by simpa only [d9301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10097 p hg
    simpa only [d9301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d9301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10099 (p : Pattern) (guard : d9302 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d9302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9301 p = 1 := by simpa only [d9302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10098 p hg
    simpa only [d9302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10100 (p : Pattern) (guard : d0 p = 1) : d48275 p ≤ (1 : Int) + d47698 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10101 (p : Pattern) (guard : d9303 p = 1) : d48276 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d9302 p = 1 := by simpa only [d9303, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10099 p hg
    simpa only [d9303, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9303, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10100 p hg
    simpa only [d9303, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10102 (p : Pattern) (guard : d9304 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9304, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10090 p hg
    simpa only [d9304, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9303 p = 1 := by simpa only [d9304, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10101 p hg
    simpa only [d9304, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10103 (p : Pattern) (guard : d9305 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d9304 p = 1 := by simpa only [d9305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10102 p hg
    simpa only [d9305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10104 (p : Pattern) (guard : d9306 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d9305 p = 1 := by simpa only [d9306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10103 p hg
    simpa only [d9306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10105 (p : Pattern) (guard : d9307 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d9306 p = 1 := by simpa only [d9307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10104 p hg
    simpa only [d9307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10106 (p : Pattern) (guard : d9308 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d9307 p = 1 := by simpa only [d9308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10105 p hg
    simpa only [d9308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10107 (p : Pattern) (guard : d9309 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d9308 p = 1 := by simpa only [d9309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10106 p hg
    simpa only [d9309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10108 (p : Pattern) (guard : d9310 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d9309 p = 1 := by simpa only [d9310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10107 p hg
    simpa only [d9310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10109 (p : Pattern) (guard : d9311 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d9310 p = 1 := by simpa only [d9311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10108 p hg
    simpa only [d9311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10110 (p : Pattern) (guard : d9312 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9311 p = 1 := by simpa only [d9312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10109 p hg
    simpa only [d9312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10111 (p : Pattern) (guard : d9313 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9312 p = 1 := by simpa only [d9313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10110 p hg
    simpa only [d9313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10112 (p : Pattern) (guard : d9314 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9314, d48278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10088 p hg
    simpa only [d9314, d48278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9313 p = 1 := by simpa only [d9314, d48278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10111 p hg
    simpa only [d9314, d48278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10113 (p : Pattern) (guard : d9315 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10087 p hg
    simpa only [d9315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9314 p = 1 := by simpa only [d9315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10112 p hg
    simpa only [d9315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10114 (p : Pattern) (guard : d9316 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d9315 p = 1 := by simpa only [d9316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10113 p hg
    simpa only [d9316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10087 p hg
    simpa only [d9316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10115 (p : Pattern) (guard : d9317 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d9316 p = 1 := by simpa only [d9317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10114 p hg
    simpa only [d9317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10087 p hg
    simpa only [d9317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10116 (p : Pattern) (guard : d9318 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d9317 p = 1 := by simpa only [d9318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10115 p hg
    simpa only [d9318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10087 p hg
    simpa only [d9318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10117 (p : Pattern) (guard : d0 p = 1) : d48306 p ≤ (1 : Int) + d47909 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10118 (p : Pattern) (guard : d9319 p = 1) : d48307 p ≤ (1 : Int) + d47910 p := by
  cases selected : p 49 with
  | false =>
    have hg : d9318 p = 1 := by simpa only [d9319, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10116 p hg
    simpa only [d9319, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9319, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10117 p hg
    simpa only [d9319, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10119 (p : Pattern) (guard : d9320 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9320, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10086 p hg
    simpa only [d9320, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9319 p = 1 := by simpa only [d9320, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10118 p hg
    simpa only [d9320, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10120 (p : Pattern) (guard : d9321 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d9321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9320 p = 1 := by simpa only [d9321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10119 p hg
    simpa only [d9321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10121 (p : Pattern) (guard : d9322 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d9322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9321 p = 1 := by simpa only [d9322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10120 p hg
    simpa only [d9322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10122 (p : Pattern) (guard : d9323 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d9323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9322 p = 1 := by simpa only [d9323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10121 p hg
    simpa only [d9323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10123 (p : Pattern) (guard : d9324 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d9324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9323 p = 1 := by simpa only [d9324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10122 p hg
    simpa only [d9324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10124 (p : Pattern) (guard : d9330 p = 1) : d47681 p ≤ (1 : Int) + d47681 p := by
  omega
theorem compare10125 (p : Pattern) (guard : d9331 p = 1) : d48273 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d9330 p = 1 := by simpa only [d9331, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10124 p hg
    simpa only [d9331, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9331, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10094 p hg
    simpa only [d9331, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10126 (p : Pattern) (guard : d9332 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9332, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10092 p hg
    simpa only [d9332, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9331 p = 1 := by simpa only [d9332, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10125 p hg
    simpa only [d9332, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10127 (p : Pattern) (guard : d9333 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d9332 p = 1 := by simpa only [d9333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10126 p hg
    simpa only [d9333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9299 p = 1 := by simpa only [d9333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10096 p hg
    simpa only [d9333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10128 (p : Pattern) (guard : d9334 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d9333 p = 1 := by simpa only [d9334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10127 p hg
    simpa only [d9334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9300 p = 1 := by simpa only [d9334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10097 p hg
    simpa only [d9334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10129 (p : Pattern) (guard : d9335 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d9335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9334 p = 1 := by simpa only [d9335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10128 p hg
    simpa only [d9335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10130 (p : Pattern) (guard : d9336 p = 1) : d48276 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d9335 p = 1 := by simpa only [d9336, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10129 p hg
    simpa only [d9336, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9336, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10100 p hg
    simpa only [d9336, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10131 (p : Pattern) (guard : d9337 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9337, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10090 p hg
    simpa only [d9337, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9336 p = 1 := by simpa only [d9337, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10130 p hg
    simpa only [d9337, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10132 (p : Pattern) (guard : d9338 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d9337 p = 1 := by simpa only [d9338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10131 p hg
    simpa only [d9338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9304 p = 1 := by simpa only [d9338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10102 p hg
    simpa only [d9338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10133 (p : Pattern) (guard : d9339 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d9338 p = 1 := by simpa only [d9339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10132 p hg
    simpa only [d9339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10134 (p : Pattern) (guard : d9340 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d9339 p = 1 := by simpa only [d9340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10133 p hg
    simpa only [d9340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10135 (p : Pattern) (guard : d9341 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d9340 p = 1 := by simpa only [d9341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10134 p hg
    simpa only [d9341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10136 (p : Pattern) (guard : d9342 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d9341 p = 1 := by simpa only [d9342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10135 p hg
    simpa only [d9342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9308 p = 1 := by simpa only [d9342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10106 p hg
    simpa only [d9342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10137 (p : Pattern) (guard : d101875 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d9342 p = 1 := by simpa only [d101875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10136 p hg
    simpa only [d101875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d101875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d101875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10138 (p : Pattern) (guard : d101876 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d101875 p = 1 := by simpa only [d101876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10137 p hg
    simpa only [d101876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9310 p = 1 := by simpa only [d101876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10108 p hg
    simpa only [d101876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10139 (p : Pattern) (guard : d101877 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d101877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101876 p = 1 := by simpa only [d101877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10138 p hg
    simpa only [d101877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10140 (p : Pattern) (guard : d101878 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d101878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101877 p = 1 := by simpa only [d101878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10139 p hg
    simpa only [d101878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10141 (p : Pattern) (guard : d101879 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101879, d48278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10088 p hg
    simpa only [d101879, d48278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101878 p = 1 := by simpa only [d101879, d48278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10140 p hg
    simpa only [d101879, d48278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10142 (p : Pattern) (guard : d101880 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10087 p hg
    simpa only [d101880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101879 p = 1 := by simpa only [d101880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10141 p hg
    simpa only [d101880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10143 (p : Pattern) (guard : d101881 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d101880 p = 1 := by simpa only [d101881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10142 p hg
    simpa only [d101881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d101881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10087 p hg
    simpa only [d101881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10144 (p : Pattern) (guard : d101882 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d101881 p = 1 := by simpa only [d101882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10143 p hg
    simpa only [d101882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d101882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10087 p hg
    simpa only [d101882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10145 (p : Pattern) (guard : d101883 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d101882 p = 1 := by simpa only [d101883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10144 p hg
    simpa only [d101883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d101883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10087 p hg
    simpa only [d101883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10146 (p : Pattern) (guard : d101884 p = 1) : d48307 p ≤ (1 : Int) + d47910 p := by
  cases selected : p 49 with
  | false =>
    have hg : d101883 p = 1 := by simpa only [d101884, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10145 p hg
    simpa only [d101884, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d101884, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10117 p hg
    simpa only [d101884, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10147 (p : Pattern) (guard : d101885 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101885, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10086 p hg
    simpa only [d101885, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101884 p = 1 := by simpa only [d101885, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10146 p hg
    simpa only [d101885, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10148 (p : Pattern) (guard : d101886 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d101886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101885 p = 1 := by simpa only [d101886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10147 p hg
    simpa only [d101886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10149 (p : Pattern) (guard : d101887 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d101887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101886 p = 1 := by simpa only [d101887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10148 p hg
    simpa only [d101887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10150 (p : Pattern) (guard : d101888 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d101888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101887 p = 1 := by simpa only [d101888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10149 p hg
    simpa only [d101888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10151 (p : Pattern) (guard : d101889 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d101889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101888 p = 1 := by simpa only [d101889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10150 p hg
    simpa only [d101889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10152 (p : Pattern) (guard : d101890 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d9324 p = 1 := by simpa only [d101890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10123 p hg
    simpa only [d101890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101889 p = 1 := by simpa only [d101890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10151 p hg
    simpa only [d101890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10153 (p : Pattern) (guard : d9389 p = 1) : d47681 p ≤ (1 : Int) + d47681 p := by
  omega
theorem compare10154 (p : Pattern) (guard : d9390 p = 1) : d48273 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d9389 p = 1 := by simpa only [d9390, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10153 p hg
    simpa only [d9390, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9390, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10094 p hg
    simpa only [d9390, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10155 (p : Pattern) (guard : d9391 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9391, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10092 p hg
    simpa only [d9391, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9390 p = 1 := by simpa only [d9391, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10154 p hg
    simpa only [d9391, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10156 (p : Pattern) (guard : d9392 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d9391 p = 1 := by simpa only [d9392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10155 p hg
    simpa only [d9392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9332 p = 1 := by simpa only [d9392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10126 p hg
    simpa only [d9392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10157 (p : Pattern) (guard : d9393 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d9392 p = 1 := by simpa only [d9393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10156 p hg
    simpa only [d9393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9333 p = 1 := by simpa only [d9393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10127 p hg
    simpa only [d9393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10158 (p : Pattern) (guard : d9394 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d9394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9393 p = 1 := by simpa only [d9394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10157 p hg
    simpa only [d9394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10159 (p : Pattern) (guard : d9395 p = 1) : d48276 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d9394 p = 1 := by simpa only [d9395, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10158 p hg
    simpa only [d9395, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9395, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10100 p hg
    simpa only [d9395, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10160 (p : Pattern) (guard : d9396 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9396, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10090 p hg
    simpa only [d9396, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9395 p = 1 := by simpa only [d9396, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10159 p hg
    simpa only [d9396, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10161 (p : Pattern) (guard : d9397 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d9396 p = 1 := by simpa only [d9397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10160 p hg
    simpa only [d9397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9337 p = 1 := by simpa only [d9397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10131 p hg
    simpa only [d9397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10162 (p : Pattern) (guard : d9398 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d9397 p = 1 := by simpa only [d9398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10161 p hg
    simpa only [d9398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10163 (p : Pattern) (guard : d9399 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d9398 p = 1 := by simpa only [d9399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10162 p hg
    simpa only [d9399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10164 (p : Pattern) (guard : d9400 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d9399 p = 1 := by simpa only [d9400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10163 p hg
    simpa only [d9400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10165 (p : Pattern) (guard : d9401 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d9400 p = 1 := by simpa only [d9401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10164 p hg
    simpa only [d9401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9341 p = 1 := by simpa only [d9401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10135 p hg
    simpa only [d9401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10166 (p : Pattern) (guard : d101891 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d9401 p = 1 := by simpa only [d101891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10165 p hg
    simpa only [d101891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d101891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d101891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10167 (p : Pattern) (guard : d9421 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d9337 p = 1 := by simpa only [d9421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10131 p hg
    simpa only [d9421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10168 (p : Pattern) (guard : d9422 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d9421 p = 1 := by simpa only [d9422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10167 p hg
    simpa only [d9422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10169 (p : Pattern) (guard : d9423 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d9422 p = 1 := by simpa only [d9423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10168 p hg
    simpa only [d9423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10170 (p : Pattern) (guard : d9424 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d9423 p = 1 := by simpa only [d9424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10169 p hg
    simpa only [d9424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10171 (p : Pattern) (guard : d9425 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d9424 p = 1 := by simpa only [d9425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10170 p hg
    simpa only [d9425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10172 (p : Pattern) (guard : d9426 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d9425 p = 1 := by simpa only [d9426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10171 p hg
    simpa only [d9426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10173 (p : Pattern) (guard : d101892 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d101891 p = 1 := by simpa only [d101892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10166 p hg
    simpa only [d101892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9426 p = 1 := by simpa only [d101892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10172 p hg
    simpa only [d101892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10174 (p : Pattern) (guard : d101893 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d101893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101892 p = 1 := by simpa only [d101893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10173 p hg
    simpa only [d101893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10175 (p : Pattern) (guard : d101894 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d101894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101893 p = 1 := by simpa only [d101894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10174 p hg
    simpa only [d101894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10176 (p : Pattern) (guard : d101895 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101895, d48278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10088 p hg
    simpa only [d101895, d48278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101894 p = 1 := by simpa only [d101895, d48278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10175 p hg
    simpa only [d101895, d48278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10177 (p : Pattern) (guard : d101896 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10087 p hg
    simpa only [d101896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101895 p = 1 := by simpa only [d101896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10176 p hg
    simpa only [d101896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10178 (p : Pattern) (guard : d9432 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9309 p = 1 := by simpa only [d9432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10107 p hg
    simpa only [d9432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10179 (p : Pattern) (guard : d9433 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d9432 p = 1 := by simpa only [d9433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10178 p hg
    simpa only [d9433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10180 (p : Pattern) (guard : d9434 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9433 p = 1 := by simpa only [d9434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10179 p hg
    simpa only [d9434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10181 (p : Pattern) (guard : d9435 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9434 p = 1 := by simpa only [d9435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10180 p hg
    simpa only [d9435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10182 (p : Pattern) (guard : d9436 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9436, d48278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10088 p hg
    simpa only [d9436, d48278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9435 p = 1 := by simpa only [d9436, d48278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10181 p hg
    simpa only [d9436, d48278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10183 (p : Pattern) (guard : d9437 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10087 p hg
    simpa only [d9437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9436 p = 1 := by simpa only [d9437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10182 p hg
    simpa only [d9437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10184 (p : Pattern) (guard : d101897 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d101896 p = 1 := by simpa only [d101897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10177 p hg
    simpa only [d101897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9437 p = 1 := by simpa only [d101897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10183 p hg
    simpa only [d101897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10185 (p : Pattern) (guard : d101898 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d101897 p = 1 := by simpa only [d101898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10184 p hg
    simpa only [d101898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d101898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10087 p hg
    simpa only [d101898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10186 (p : Pattern) (guard : d101899 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d101898 p = 1 := by simpa only [d101899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10185 p hg
    simpa only [d101899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d101899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10087 p hg
    simpa only [d101899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10187 (p : Pattern) (guard : d101900 p = 1) : d48307 p ≤ (1 : Int) + d47910 p := by
  cases selected : p 49 with
  | false =>
    have hg : d101899 p = 1 := by simpa only [d101900, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10186 p hg
    simpa only [d101900, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d101900, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10117 p hg
    simpa only [d101900, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10188 (p : Pattern) (guard : d101901 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101901, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10086 p hg
    simpa only [d101901, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101900 p = 1 := by simpa only [d101901, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10187 p hg
    simpa only [d101901, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10189 (p : Pattern) (guard : d101902 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d101902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101901 p = 1 := by simpa only [d101902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10188 p hg
    simpa only [d101902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10190 (p : Pattern) (guard : d101903 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d101903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101902 p = 1 := by simpa only [d101903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10189 p hg
    simpa only [d101903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10191 (p : Pattern) (guard : d101904 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d101904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101903 p = 1 := by simpa only [d101904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10190 p hg
    simpa only [d101904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10192 (p : Pattern) (guard : d101905 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d101905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101904 p = 1 := by simpa only [d101905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10191 p hg
    simpa only [d101905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10193 (p : Pattern) (guard : d101906 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d101906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101905 p = 1 := by simpa only [d101906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10192 p hg
    simpa only [d101906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10194 (p : Pattern) (guard : d101907 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d101890 p = 1 := by simpa only [d101907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10152 p hg
    simpa only [d101907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101906 p = 1 := by simpa only [d101907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10193 p hg
    simpa only [d101907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10195 (p : Pattern) (guard : d9475 p = 1) : d47681 p ≤ (1 : Int) + d47681 p := by
  omega
theorem compare10196 (p : Pattern) (guard : d9476 p = 1) : d48273 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d9475 p = 1 := by simpa only [d9476, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10195 p hg
    simpa only [d9476, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9476, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10094 p hg
    simpa only [d9476, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10197 (p : Pattern) (guard : d9477 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9477, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10092 p hg
    simpa only [d9477, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9476 p = 1 := by simpa only [d9477, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10196 p hg
    simpa only [d9477, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10198 (p : Pattern) (guard : d9479 p = 1) : d47681 p ≤ (1 : Int) + d47681 p := by
  omega
theorem compare10199 (p : Pattern) (guard : d9480 p = 1) : d48273 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d9479 p = 1 := by simpa only [d9480, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10198 p hg
    simpa only [d9480, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9480, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10094 p hg
    simpa only [d9480, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10200 (p : Pattern) (guard : d9481 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9481, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10092 p hg
    simpa only [d9481, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9480 p = 1 := by simpa only [d9481, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10199 p hg
    simpa only [d9481, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10201 (p : Pattern) (guard : d9482 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d9477 p = 1 := by simpa only [d9482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10197 p hg
    simpa only [d9482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9481 p = 1 := by simpa only [d9482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10200 p hg
    simpa only [d9482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10202 (p : Pattern) (guard : d9483 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d9482 p = 1 := by simpa only [d9483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10201 p hg
    simpa only [d9483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9392 p = 1 := by simpa only [d9483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10156 p hg
    simpa only [d9483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10203 (p : Pattern) (guard : d9484 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d9484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9483 p = 1 := by simpa only [d9484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10202 p hg
    simpa only [d9484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10204 (p : Pattern) (guard : d9485 p = 1) : d48276 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d9484 p = 1 := by simpa only [d9485, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10203 p hg
    simpa only [d9485, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9485, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10100 p hg
    simpa only [d9485, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10205 (p : Pattern) (guard : d9486 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9486, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10090 p hg
    simpa only [d9486, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9485 p = 1 := by simpa only [d9486, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10204 p hg
    simpa only [d9486, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10206 (p : Pattern) (guard : d9487 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d9332 p = 1 := by simpa only [d9487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10126 p hg
    simpa only [d9487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d9487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10207 (p : Pattern) (guard : d9488 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d9392 p = 1 := by simpa only [d9488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10156 p hg
    simpa only [d9488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9487 p = 1 := by simpa only [d9488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10206 p hg
    simpa only [d9488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10208 (p : Pattern) (guard : d9489 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d9489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9488 p = 1 := by simpa only [d9489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10207 p hg
    simpa only [d9489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10209 (p : Pattern) (guard : d9490 p = 1) : d48276 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d9489 p = 1 := by simpa only [d9490, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10208 p hg
    simpa only [d9490, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9490, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10100 p hg
    simpa only [d9490, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10210 (p : Pattern) (guard : d9491 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9491, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10090 p hg
    simpa only [d9491, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9490 p = 1 := by simpa only [d9491, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10209 p hg
    simpa only [d9491, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10211 (p : Pattern) (guard : d9492 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d9486 p = 1 := by simpa only [d9492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10205 p hg
    simpa only [d9492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9491 p = 1 := by simpa only [d9492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10210 p hg
    simpa only [d9492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10212 (p : Pattern) (guard : d9493 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d9492 p = 1 := by simpa only [d9493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10211 p hg
    simpa only [d9493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10213 (p : Pattern) (guard : d9494 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d9493 p = 1 := by simpa only [d9494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10212 p hg
    simpa only [d9494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10214 (p : Pattern) (guard : d9495 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d9494 p = 1 := by simpa only [d9495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10213 p hg
    simpa only [d9495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10215 (p : Pattern) (guard : d9496 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d9487 p = 1 := by simpa only [d9496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10206 p hg
    simpa only [d9496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d9496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10216 (p : Pattern) (guard : d9497 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d9497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9496 p = 1 := by simpa only [d9497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10215 p hg
    simpa only [d9497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10217 (p : Pattern) (guard : d9498 p = 1) : d48276 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d9497 p = 1 := by simpa only [d9498, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10216 p hg
    simpa only [d9498, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9498, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10100 p hg
    simpa only [d9498, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10218 (p : Pattern) (guard : d9499 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9499, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10090 p hg
    simpa only [d9499, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9498 p = 1 := by simpa only [d9499, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10217 p hg
    simpa only [d9499, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10219 (p : Pattern) (guard : d9500 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d9491 p = 1 := by simpa only [d9500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10210 p hg
    simpa only [d9500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9499 p = 1 := by simpa only [d9500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10218 p hg
    simpa only [d9500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10220 (p : Pattern) (guard : d9501 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d9500 p = 1 := by simpa only [d9501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10219 p hg
    simpa only [d9501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10221 (p : Pattern) (guard : d9502 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d9501 p = 1 := by simpa only [d9502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10220 p hg
    simpa only [d9502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10222 (p : Pattern) (guard : d9503 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d9502 p = 1 := by simpa only [d9503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10221 p hg
    simpa only [d9503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10223 (p : Pattern) (guard : d9504 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d9495 p = 1 := by simpa only [d9504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10214 p hg
    simpa only [d9504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9503 p = 1 := by simpa only [d9504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10222 p hg
    simpa only [d9504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10224 (p : Pattern) (guard : d101908 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d9504 p = 1 := by simpa only [d101908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10223 p hg
    simpa only [d101908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d101908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d101908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10225 (p : Pattern) (guard : d9542 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d9491 p = 1 := by simpa only [d9542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10210 p hg
    simpa only [d9542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10226 (p : Pattern) (guard : d9543 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d9542 p = 1 := by simpa only [d9543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10225 p hg
    simpa only [d9543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10227 (p : Pattern) (guard : d9544 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d9543 p = 1 := by simpa only [d9544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10226 p hg
    simpa only [d9544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10228 (p : Pattern) (guard : d9545 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d9544 p = 1 := by simpa only [d9545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10227 p hg
    simpa only [d9545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10229 (p : Pattern) (guard : d9546 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d9545 p = 1 := by simpa only [d9546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10228 p hg
    simpa only [d9546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10230 (p : Pattern) (guard : d9547 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d9546 p = 1 := by simpa only [d9547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10229 p hg
    simpa only [d9547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10231 (p : Pattern) (guard : d101909 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d101908 p = 1 := by simpa only [d101909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10224 p hg
    simpa only [d101909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9547 p = 1 := by simpa only [d101909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10230 p hg
    simpa only [d101909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10232 (p : Pattern) (guard : d101910 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d101910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101909 p = 1 := by simpa only [d101910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10231 p hg
    simpa only [d101910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10233 (p : Pattern) (guard : d101911 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d101911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101910 p = 1 := by simpa only [d101911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10232 p hg
    simpa only [d101911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10234 (p : Pattern) (guard : d101912 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101912, d48278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10088 p hg
    simpa only [d101912, d48278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101911 p = 1 := by simpa only [d101912, d48278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10233 p hg
    simpa only [d101912, d48278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10235 (p : Pattern) (guard : d101913 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10087 p hg
    simpa only [d101913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101912 p = 1 := by simpa only [d101913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10234 p hg
    simpa only [d101913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10236 (p : Pattern) (guard : d9553 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d9499 p = 1 := by simpa only [d9553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10218 p hg
    simpa only [d9553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10237 (p : Pattern) (guard : d9554 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d9553 p = 1 := by simpa only [d9554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10236 p hg
    simpa only [d9554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10238 (p : Pattern) (guard : d9555 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d9554 p = 1 := by simpa only [d9555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10237 p hg
    simpa only [d9555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10239 (p : Pattern) (guard : d9556 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d9555 p = 1 := by simpa only [d9556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10238 p hg
    simpa only [d9556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10240 (p : Pattern) (guard : d9557 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d9556 p = 1 := by simpa only [d9557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10239 p hg
    simpa only [d9557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10241 (p : Pattern) (guard : d9558 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9557 p = 1 := by simpa only [d9558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10240 p hg
    simpa only [d9558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10242 (p : Pattern) (guard : d9559 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d9558 p = 1 := by simpa only [d9559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10241 p hg
    simpa only [d9559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10243 (p : Pattern) (guard : d9560 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9559 p = 1 := by simpa only [d9560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10242 p hg
    simpa only [d9560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10244 (p : Pattern) (guard : d9561 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d9561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9560 p = 1 := by simpa only [d9561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10243 p hg
    simpa only [d9561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10245 (p : Pattern) (guard : d9562 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9562, d48278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10088 p hg
    simpa only [d9562, d48278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9561 p = 1 := by simpa only [d9562, d48278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10244 p hg
    simpa only [d9562, d48278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10246 (p : Pattern) (guard : d9563 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10087 p hg
    simpa only [d9563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9562 p = 1 := by simpa only [d9563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10245 p hg
    simpa only [d9563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10247 (p : Pattern) (guard : d101914 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d101913 p = 1 := by simpa only [d101914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10235 p hg
    simpa only [d101914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9563 p = 1 := by simpa only [d101914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10246 p hg
    simpa only [d101914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10248 (p : Pattern) (guard : d101915 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d101914 p = 1 := by simpa only [d101915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10247 p hg
    simpa only [d101915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d101915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10087 p hg
    simpa only [d101915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10249 (p : Pattern) (guard : d101916 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d101915 p = 1 := by simpa only [d101916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10248 p hg
    simpa only [d101916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d101916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10087 p hg
    simpa only [d101916, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
