import NetHack.Soko22Hazard87.Compare091
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare23000 (p : Pattern) (guard : d180045 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180021 p = 1 := by simpa only [d180045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22932 p hg
    simpa only [d180045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23001 (p : Pattern) (guard : d180046 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180045 p = 1 := by simpa only [d180046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23000 p hg
    simpa only [d180046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23002 (p : Pattern) (guard : d180047 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d180044 p = 1 := by simpa only [d180047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22999 p hg
    simpa only [d180047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180046 p = 1 := by simpa only [d180047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23001 p hg
    simpa only [d180047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23003 (p : Pattern) (guard : d180048 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180047 p = 1 := by simpa only [d180048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23002 p hg
    simpa only [d180048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23004 (p : Pattern) (guard : d180049 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d180048 p = 1 := by simpa only [d180049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23003 p hg
    simpa only [d180049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23005 (p : Pattern) (guard : d180050 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180049 p = 1 := by simpa only [d180050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23004 p hg
    simpa only [d180050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23006 (p : Pattern) (guard : d180051 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180016 p = 1 := by simpa only [d180051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22927 p hg
    simpa only [d180051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23007 (p : Pattern) (guard : d180052 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d180051 p = 1 := by simpa only [d180052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23006 p hg
    simpa only [d180052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23008 (p : Pattern) (guard : d180053 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180052 p = 1 := by simpa only [d180053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23007 p hg
    simpa only [d180053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23009 (p : Pattern) (guard : d180054 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180020 p = 1 := by simpa only [d180054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22931 p hg
    simpa only [d180054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23010 (p : Pattern) (guard : d180055 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d180054 p = 1 := by simpa only [d180055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23009 p hg
    simpa only [d180055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23011 (p : Pattern) (guard : d180056 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180055 p = 1 := by simpa only [d180056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23010 p hg
    simpa only [d180056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23012 (p : Pattern) (guard : d180057 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d180053 p = 1 := by simpa only [d180057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23008 p hg
    simpa only [d180057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180056 p = 1 := by simpa only [d180057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23011 p hg
    simpa only [d180057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23013 (p : Pattern) (guard : d180058 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180057 p = 1 := by simpa only [d180058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23012 p hg
    simpa only [d180058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23014 (p : Pattern) (guard : d180059 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d180058 p = 1 := by simpa only [d180059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23013 p hg
    simpa only [d180059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23015 (p : Pattern) (guard : d180062 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180062, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21649 p hg
    simpa only [d180062, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180061 p = 1 := by simpa only [d180062, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22972 p hg
    simpa only [d180062, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23016 (p : Pattern) (guard : d180065 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180065, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21649 p hg
    simpa only [d180065, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180064 p = 1 := by simpa only [d180065, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22975 p hg
    simpa only [d180065, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23017 (p : Pattern) (guard : d180066 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d180062 p = 1 := by simpa only [d180066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23015 p hg
    simpa only [d180066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180065 p = 1 := by simpa only [d180066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23016 p hg
    simpa only [d180066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23018 (p : Pattern) (guard : d180067 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d180066 p = 1 := by simpa only [d180067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23017 p hg
    simpa only [d180067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180006 p = 1 := by simpa only [d180067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22917 p hg
    simpa only [d180067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23019 (p : Pattern) (guard : d180068 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d180067 p = 1 := by simpa only [d180068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23018 p hg
    simpa only [d180068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21651 p hg
    simpa only [d180068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23020 (p : Pattern) (guard : d180069 p = 1) : d48329 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d180068 p = 1 := by simpa only [d180069, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23019 p hg
    simpa only [d180069, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180069, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21635 p hg
    simpa only [d180069, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23021 (p : Pattern) (guard : d180070 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180070, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21648 p hg
    simpa only [d180070, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180069 p = 1 := by simpa only [d180070, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23020 p hg
    simpa only [d180070, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23022 (p : Pattern) (guard : d180071 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d180070 p = 1 := by simpa only [d180071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23021 p hg
    simpa only [d180071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180011 p = 1 := by simpa only [d180071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22922 p hg
    simpa only [d180071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23023 (p : Pattern) (guard : d180072 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d180071 p = 1 := by simpa only [d180072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23022 p hg
    simpa only [d180072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23024 (p : Pattern) (guard : d180073 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d180072 p = 1 := by simpa only [d180073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23023 p hg
    simpa only [d180073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23025 (p : Pattern) (guard : d180074 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180074, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180073 p = 1 := by simpa only [d180074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23024 p hg
    simpa only [d180074, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23026 (p : Pattern) (guard : d180075 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d180074 p = 1 := by simpa only [d180075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23025 p hg
    simpa only [d180075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180019 p = 1 := by simpa only [d180075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22930 p hg
    simpa only [d180075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23027 (p : Pattern) (guard : d180076 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d180075 p = 1 := by simpa only [d180076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23026 p hg
    simpa only [d180076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23028 (p : Pattern) (guard : d180077 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d180011 p = 1 := by simpa only [d180077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22922 p hg
    simpa only [d180077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23029 (p : Pattern) (guard : d180078 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d180077 p = 1 := by simpa only [d180078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23028 p hg
    simpa only [d180078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23030 (p : Pattern) (guard : d180079 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d180078 p = 1 := by simpa only [d180079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23029 p hg
    simpa only [d180079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23031 (p : Pattern) (guard : d180080 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180079 p = 1 := by simpa only [d180080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23030 p hg
    simpa only [d180080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23032 (p : Pattern) (guard : d180081 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d180080 p = 1 := by simpa only [d180081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23031 p hg
    simpa only [d180081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23033 (p : Pattern) (guard : d180082 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d180081 p = 1 := by simpa only [d180082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23032 p hg
    simpa only [d180082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23034 (p : Pattern) (guard : d180083 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d180076 p = 1 := by simpa only [d180083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23027 p hg
    simpa only [d180083, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180082 p = 1 := by simpa only [d180083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23033 p hg
    simpa only [d180083, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23035 (p : Pattern) (guard : d180084 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d180059 p = 1 := by simpa only [d180084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23014 p hg
    simpa only [d180084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180083 p = 1 := by simpa only [d180084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23034 p hg
    simpa only [d180084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23036 (p : Pattern) (guard : d180085 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d180050 p = 1 := by simpa only [d180085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23005 p hg
    simpa only [d180085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180084 p = 1 := by simpa only [d180085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23035 p hg
    simpa only [d180085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23037 (p : Pattern) (guard : d180087 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d180043 p = 1 := by simpa only [d180087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22951 p hg
    simpa only [d180087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23038 (p : Pattern) (guard : d180088 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d180045 p = 1 := by simpa only [d180088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22953 p hg
    simpa only [d180088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23039 (p : Pattern) (guard : d180089 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d180087 p = 1 := by simpa only [d180089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23037 p hg
    simpa only [d180089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180088 p = 1 := by simpa only [d180089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23038 p hg
    simpa only [d180089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23040 (p : Pattern) (guard : d180090 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180089 p = 1 := by simpa only [d180090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23039 p hg
    simpa only [d180090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23041 (p : Pattern) (guard : d180091 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d180090 p = 1 := by simpa only [d180091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23040 p hg
    simpa only [d180091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23042 (p : Pattern) (guard : d180092 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180091 p = 1 := by simpa only [d180092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23041 p hg
    simpa only [d180092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23043 (p : Pattern) (guard : d180093 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d180052 p = 1 := by simpa only [d180093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22960 p hg
    simpa only [d180093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23044 (p : Pattern) (guard : d180094 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d180055 p = 1 := by simpa only [d180094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22963 p hg
    simpa only [d180094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23045 (p : Pattern) (guard : d180095 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d180093 p = 1 := by simpa only [d180095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23043 p hg
    simpa only [d180095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180094 p = 1 := by simpa only [d180095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23044 p hg
    simpa only [d180095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23046 (p : Pattern) (guard : d180096 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180095 p = 1 := by simpa only [d180096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23045 p hg
    simpa only [d180096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23047 (p : Pattern) (guard : d180097 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d180096 p = 1 := by simpa only [d180097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23046 p hg
    simpa only [d180097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23048 (p : Pattern) (guard : d180098 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d180073 p = 1 := by simpa only [d180098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22984 p hg
    simpa only [d180098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23049 (p : Pattern) (guard : d180099 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d180098 p = 1 := by simpa only [d180099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23048 p hg
    simpa only [d180099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180032 p = 1 := by simpa only [d180099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22940 p hg
    simpa only [d180099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23050 (p : Pattern) (guard : d180100 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d180099 p = 1 := by simpa only [d180100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23049 p hg
    simpa only [d180100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23051 (p : Pattern) (guard : d180101 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d180079 p = 1 := by simpa only [d180101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22990 p hg
    simpa only [d180101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23052 (p : Pattern) (guard : d180102 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d180101 p = 1 := by simpa only [d180102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23051 p hg
    simpa only [d180102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23053 (p : Pattern) (guard : d180103 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d180102 p = 1 := by simpa only [d180103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23052 p hg
    simpa only [d180103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23054 (p : Pattern) (guard : d180104 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d180100 p = 1 := by simpa only [d180104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23050 p hg
    simpa only [d180104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180103 p = 1 := by simpa only [d180104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23053 p hg
    simpa only [d180104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23055 (p : Pattern) (guard : d180105 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d180097 p = 1 := by simpa only [d180105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23047 p hg
    simpa only [d180105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180104 p = 1 := by simpa only [d180105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23054 p hg
    simpa only [d180105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23056 (p : Pattern) (guard : d180106 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d180092 p = 1 := by simpa only [d180106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23042 p hg
    simpa only [d180106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180105 p = 1 := by simpa only [d180106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23055 p hg
    simpa only [d180106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23057 (p : Pattern) (guard : d180107 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d180085 p = 1 := by simpa only [d180107, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23036 p hg
    simpa only [d180107, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180106 p = 1 := by simpa only [d180107, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23056 p hg
    simpa only [d180107, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23058 (p : Pattern) (guard : d180108 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d180086 p = 1 := by simpa only [d180108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22997 p hg
    simpa only [d180108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180107 p = 1 := by simpa only [d180108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23057 p hg
    simpa only [d180108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23059 (p : Pattern) (guard : d180109 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d180023 p = 1 := by simpa only [d180109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22906 p hg
    simpa only [d180109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23060 (p : Pattern) (guard : d180110 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180109 p = 1 := by simpa only [d180110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23059 p hg
    simpa only [d180110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23061 (p : Pattern) (guard : d180111 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d180110 p = 1 := by simpa only [d180111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23060 p hg
    simpa only [d180111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23062 (p : Pattern) (guard : d180112 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180111 p = 1 := by simpa only [d180112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23061 p hg
    simpa only [d180112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23063 (p : Pattern) (guard : d180113 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180112 p = 1 := by simpa only [d180113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23062 p hg
    simpa only [d180113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23064 (p : Pattern) (guard : d180114 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d180028 p = 1 := by simpa only [d180114, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22939 p hg
    simpa only [d180114, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180113 p = 1 := by simpa only [d180114, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23063 p hg
    simpa only [d180114, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23065 (p : Pattern) (guard : d180109 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d180023 p = 1 := by simpa only [d180109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22934 p hg
    simpa only [d180109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23066 (p : Pattern) (guard : d180110 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180109 p = 1 := by simpa only [d180110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23065 p hg
    simpa only [d180110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23067 (p : Pattern) (guard : d180111 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d180110 p = 1 := by simpa only [d180111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23066 p hg
    simpa only [d180111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23068 (p : Pattern) (guard : d180112 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180111 p = 1 := by simpa only [d180112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23067 p hg
    simpa only [d180112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23069 (p : Pattern) (guard : d180113 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180112 p = 1 := by simpa only [d180113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23068 p hg
    simpa only [d180113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23070 (p : Pattern) (guard : d180115 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d180033 p = 1 := by simpa only [d180115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22941 p hg
    simpa only [d180115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23071 (p : Pattern) (guard : d180116 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180115 p = 1 := by simpa only [d180116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23070 p hg
    simpa only [d180116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23072 (p : Pattern) (guard : d180117 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d180116 p = 1 := by simpa only [d180117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23071 p hg
    simpa only [d180117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23073 (p : Pattern) (guard : d180118 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180117 p = 1 := by simpa only [d180118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23072 p hg
    simpa only [d180118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23074 (p : Pattern) (guard : d180119 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d180119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180118 p = 1 := by simpa only [d180119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23073 p hg
    simpa only [d180119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23075 (p : Pattern) (guard : d180120 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d180113 p = 1 := by simpa only [d180120, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23069 p hg
    simpa only [d180120, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180119 p = 1 := by simpa only [d180120, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23074 p hg
    simpa only [d180120, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23076 (p : Pattern) (guard : d180121 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d180114 p = 1 := by simpa only [d180121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23064 p hg
    simpa only [d180121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180120 p = 1 := by simpa only [d180121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23075 p hg
    simpa only [d180121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23077 (p : Pattern) (guard : d180122 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d180108 p = 1 := by simpa only [d180122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23058 p hg
    simpa only [d180122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180121 p = 1 := by simpa only [d180122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23076 p hg
    simpa only [d180122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23078 (p : Pattern) (guard : d180123 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d180122 p = 1 := by simpa only [d180123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23077 p hg
    simpa only [d180123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21616 p hg
    simpa only [d180123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23079 (p : Pattern) (guard : d180124 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d180042 p = 1 := by simpa only [d180124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22950 p hg
    simpa only [d180124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180123 p = 1 := by simpa only [d180124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23078 p hg
    simpa only [d180124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23080 (p : Pattern) (guard : d17226 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17225 p = 1 := by simpa only [d17226, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16214 p hg
    simpa only [d17226, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17226, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21684 p hg
    simpa only [d17226, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23081 (p : Pattern) (guard : d22767 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d22767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21682 p hg
    simpa only [d22767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17226 p = 1 := by simpa only [d22767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23080 p hg
    simpa only [d22767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23082 (p : Pattern) (guard : d149593 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d22767 p = 1 := by simpa only [d149593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23081 p hg
    simpa only [d149593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d149593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21682 p hg
    simpa only [d149593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23083 (p : Pattern) (guard : d179986 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare23084 (p : Pattern) (guard : d179987 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179986 p = 1 := by simpa only [d179987, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23083 p hg
    simpa only [d179987, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179987, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21684 p hg
    simpa only [d179987, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23085 (p : Pattern) (guard : d179988 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21682 p hg
    simpa only [d179988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179987 p = 1 := by simpa only [d179988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23084 p hg
    simpa only [d179988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23086 (p : Pattern) (guard : d179989 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179988 p = 1 := by simpa only [d179989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23085 p hg
    simpa only [d179989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21682 p hg
    simpa only [d179989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23087 (p : Pattern) (guard : d180060 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d149593 p = 1 := by simpa only [d180060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23082 p hg
    simpa only [d180060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179989 p = 1 := by simpa only [d180060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23086 p hg
    simpa only [d180060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23088 (p : Pattern) (guard : d180061 p = 1) : d48346 p ≤ (1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180061, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21681 p hg
    simpa only [d180061, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180060 p = 1 := by simpa only [d180061, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23087 p hg
    simpa only [d180061, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23089 (p : Pattern) (guard : d180062 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180062, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21680 p hg
    simpa only [d180062, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180061 p = 1 := by simpa only [d180062, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23088 p hg
    simpa only [d180062, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23090 (p : Pattern) (guard : d180063 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179989 p = 1 := by simpa only [d180063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23086 p hg
    simpa only [d180063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21682 p hg
    simpa only [d180063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23091 (p : Pattern) (guard : d180064 p = 1) : d48346 p ≤ (1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180064, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21681 p hg
    simpa only [d180064, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180063 p = 1 := by simpa only [d180064, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23090 p hg
    simpa only [d180064, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23092 (p : Pattern) (guard : d180065 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180065, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21680 p hg
    simpa only [d180065, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180064 p = 1 := by simpa only [d180065, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23091 p hg
    simpa only [d180065, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23093 (p : Pattern) (guard : d180066 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d180062 p = 1 := by simpa only [d180066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23089 p hg
    simpa only [d180066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180065 p = 1 := by simpa only [d180066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23092 p hg
    simpa only [d180066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23094 (p : Pattern) (guard : d179996 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare23095 (p : Pattern) (guard : d179997 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179996 p = 1 := by simpa only [d179997, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23094 p hg
    simpa only [d179997, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179997, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21684 p hg
    simpa only [d179997, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23096 (p : Pattern) (guard : d179998 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21682 p hg
    simpa only [d179998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179997 p = 1 := by simpa only [d179998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23095 p hg
    simpa only [d179998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23097 (p : Pattern) (guard : d179999 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179998 p = 1 := by simpa only [d179999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23096 p hg
    simpa only [d179999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21682 p hg
    simpa only [d179999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23098 (p : Pattern) (guard : d180000 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179989 p = 1 := by simpa only [d180000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23086 p hg
    simpa only [d180000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179999 p = 1 := by simpa only [d180000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23097 p hg
    simpa only [d180000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23099 (p : Pattern) (guard : d180001 p = 1) : d48346 p ≤ (1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180001, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21681 p hg
    simpa only [d180001, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180000 p = 1 := by simpa only [d180001, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23098 p hg
    simpa only [d180001, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23100 (p : Pattern) (guard : d180002 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180002, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21680 p hg
    simpa only [d180002, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180001 p = 1 := by simpa only [d180002, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23099 p hg
    simpa only [d180002, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23101 (p : Pattern) (guard : d180003 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179999 p = 1 := by simpa only [d180003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23097 p hg
    simpa only [d180003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21682 p hg
    simpa only [d180003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23102 (p : Pattern) (guard : d180004 p = 1) : d48346 p ≤ (1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180004, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21681 p hg
    simpa only [d180004, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180003 p = 1 := by simpa only [d180004, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23101 p hg
    simpa only [d180004, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23103 (p : Pattern) (guard : d180005 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180005, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21680 p hg
    simpa only [d180005, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180004 p = 1 := by simpa only [d180005, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23102 p hg
    simpa only [d180005, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23104 (p : Pattern) (guard : d180006 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d180002 p = 1 := by simpa only [d180006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23100 p hg
    simpa only [d180006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180005 p = 1 := by simpa only [d180006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23103 p hg
    simpa only [d180006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23105 (p : Pattern) (guard : d180067 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d180066 p = 1 := by simpa only [d180067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23093 p hg
    simpa only [d180067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180006 p = 1 := by simpa only [d180067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23104 p hg
    simpa only [d180067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23106 (p : Pattern) (guard : d180068 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d180067 p = 1 := by simpa only [d180068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23105 p hg
    simpa only [d180068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21691 p hg
    simpa only [d180068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23107 (p : Pattern) (guard : d180069 p = 1) : d48356 p ≤ (1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d180068 p = 1 := by simpa only [d180069, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23106 p hg
    simpa only [d180069, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180069, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21695 p hg
    simpa only [d180069, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23108 (p : Pattern) (guard : d180070 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180070, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21679 p hg
    simpa only [d180070, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180069 p = 1 := by simpa only [d180070, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23107 p hg
    simpa only [d180070, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23109 (p : Pattern) (guard : d180007 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d180005 p = 1 := by simpa only [d180007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23103 p hg
    simpa only [d180007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21691 p hg
    simpa only [d180007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23110 (p : Pattern) (guard : d180008 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d180006 p = 1 := by simpa only [d180008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23104 p hg
    simpa only [d180008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180007 p = 1 := by simpa only [d180008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23109 p hg
    simpa only [d180008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23111 (p : Pattern) (guard : d180009 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d180008 p = 1 := by simpa only [d180009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23110 p hg
    simpa only [d180009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21691 p hg
    simpa only [d180009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23112 (p : Pattern) (guard : d180010 p = 1) : d48356 p ≤ (1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d180009 p = 1 := by simpa only [d180010, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23111 p hg
    simpa only [d180010, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180010, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21695 p hg
    simpa only [d180010, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23113 (p : Pattern) (guard : d180011 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180011, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21679 p hg
    simpa only [d180011, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180010 p = 1 := by simpa only [d180011, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23112 p hg
    simpa only [d180011, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23114 (p : Pattern) (guard : d180071 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d180070 p = 1 := by simpa only [d180071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23108 p hg
    simpa only [d180071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180011 p = 1 := by simpa only [d180071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23113 p hg
    simpa only [d180071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23115 (p : Pattern) (guard : d180072 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d180071 p = 1 := by simpa only [d180072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23114 p hg
    simpa only [d180072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d180072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23116 (p : Pattern) (guard : d180073 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d180072 p = 1 := by simpa only [d180073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23115 p hg
    simpa only [d180073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d180073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23117 (p : Pattern) (guard : d180098 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d180073 p = 1 := by simpa only [d180098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23116 p hg
    simpa only [d180098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d180098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23118 (p : Pattern) (guard : d180012 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d180007 p = 1 := by simpa only [d180012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23109 p hg
    simpa only [d180012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21691 p hg
    simpa only [d180012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23119 (p : Pattern) (guard : d180013 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d180012 p = 1 := by simpa only [d180013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23118 p hg
    simpa only [d180013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21691 p hg
    simpa only [d180013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23120 (p : Pattern) (guard : d180014 p = 1) : d48356 p ≤ (1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d180013 p = 1 := by simpa only [d180014, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23119 p hg
    simpa only [d180014, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180014, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21695 p hg
    simpa only [d180014, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23121 (p : Pattern) (guard : d180015 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180015, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21679 p hg
    simpa only [d180015, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180014 p = 1 := by simpa only [d180015, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23120 p hg
    simpa only [d180015, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23122 (p : Pattern) (guard : d180016 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d180011 p = 1 := by simpa only [d180016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23113 p hg
    simpa only [d180016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180015 p = 1 := by simpa only [d180016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23121 p hg
    simpa only [d180016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23123 (p : Pattern) (guard : d180017 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d180016 p = 1 := by simpa only [d180017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23122 p hg
    simpa only [d180017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d180017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23124 (p : Pattern) (guard : d180018 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d180017 p = 1 := by simpa only [d180018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23123 p hg
    simpa only [d180018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d180018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23125 (p : Pattern) (guard : d180032 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d180018 p = 1 := by simpa only [d180032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23124 p hg
    simpa only [d180032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d180032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23126 (p : Pattern) (guard : d180099 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d180098 p = 1 := by simpa only [d180099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23117 p hg
    simpa only [d180099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180032 p = 1 := by simpa only [d180099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23125 p hg
    simpa only [d180099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23127 (p : Pattern) (guard : d180100 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d180099 p = 1 := by simpa only [d180100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23126 p hg
    simpa only [d180100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d180100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23128 (p : Pattern) (guard : d180077 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d180011 p = 1 := by simpa only [d180077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23113 p hg
    simpa only [d180077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d180077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23129 (p : Pattern) (guard : d180078 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d180077 p = 1 := by simpa only [d180078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23128 p hg
    simpa only [d180078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d180078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23130 (p : Pattern) (guard : d180079 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d180078 p = 1 := by simpa only [d180079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23129 p hg
    simpa only [d180079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d180079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23131 (p : Pattern) (guard : d180101 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d180079 p = 1 := by simpa only [d180101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23130 p hg
    simpa only [d180101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d180101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23132 (p : Pattern) (guard : d180102 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d180101 p = 1 := by simpa only [d180102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23131 p hg
    simpa only [d180102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d180102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23133 (p : Pattern) (guard : d180103 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d180102 p = 1 := by simpa only [d180103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23132 p hg
    simpa only [d180103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d180103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23134 (p : Pattern) (guard : d180104 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d180100 p = 1 := by simpa only [d180104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23127 p hg
    simpa only [d180104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180103 p = 1 := by simpa only [d180104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23133 p hg
    simpa only [d180104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23135 (p : Pattern) (guard : d180125 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d180125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180104 p = 1 := by simpa only [d180125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23134 p hg
    simpa only [d180125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23136 (p : Pattern) (guard : d180126 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d180126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180125 p = 1 := by simpa only [d180126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23135 p hg
    simpa only [d180126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23137 (p : Pattern) (guard : d180127 p = 1) : d48358 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180127, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180127, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180126 p = 1 := by simpa only [d180127, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23136 p hg
    simpa only [d180127, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23138 (p : Pattern) (guard : d180128 p = 1) : d48358 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21677 p hg
    simpa only [d180128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180127 p = 1 := by simpa only [d180128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23137 p hg
    simpa only [d180128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23139 (p : Pattern) (guard : d180020 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d180015 p = 1 := by simpa only [d180020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23121 p hg
    simpa only [d180020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d180020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23140 (p : Pattern) (guard : d180021 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d180020 p = 1 := by simpa only [d180021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23139 p hg
    simpa only [d180021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d180021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23141 (p : Pattern) (guard : d180022 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d180021 p = 1 := by simpa only [d180022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23140 p hg
    simpa only [d180022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d180022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23142 (p : Pattern) (guard : d180033 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d180022 p = 1 := by simpa only [d180033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23141 p hg
    simpa only [d180033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d180033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23143 (p : Pattern) (guard : d180115 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d180033 p = 1 := by simpa only [d180115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23142 p hg
    simpa only [d180115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d180115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23144 (p : Pattern) (guard : d180116 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d180116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180115 p = 1 := by simpa only [d180116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23143 p hg
    simpa only [d180116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23145 (p : Pattern) (guard : d180117 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d180116 p = 1 := by simpa only [d180117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23144 p hg
    simpa only [d180117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d180117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23146 (p : Pattern) (guard : d180118 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d180118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180117 p = 1 := by simpa only [d180118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23145 p hg
    simpa only [d180118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23147 (p : Pattern) (guard : d180119 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21678 p hg
    simpa only [d180119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180118 p = 1 := by simpa only [d180119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23146 p hg
    simpa only [d180119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23148 (p : Pattern) (guard : d180129 p = 1) : d48358 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180129, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180129, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180119 p = 1 := by simpa only [d180129, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23147 p hg
    simpa only [d180129, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23149 (p : Pattern) (guard : d180130 p = 1) : d48358 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21677 p hg
    simpa only [d180130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180129 p = 1 := by simpa only [d180130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23148 p hg
    simpa only [d180130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23150 (p : Pattern) (guard : d180131 p = 1) : d48358 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d180128 p = 1 := by simpa only [d180131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23138 p hg
    simpa only [d180131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180130 p = 1 := by simpa only [d180131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23149 p hg
    simpa only [d180131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23151 (p : Pattern) (guard : d180132 p = 1) : d48358 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d180131 p = 1 := by simpa only [d180132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23150 p hg
    simpa only [d180132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21677 p hg
    simpa only [d180132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23152 (p : Pattern) (guard : d180133 p = 1) : d48358 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d180132 p = 1 := by simpa only [d180133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23151 p hg
    simpa only [d180133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21677 p hg
    simpa only [d180133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23153 (p : Pattern) (guard : d180134 p = 1) : d48359 p ≤ (1 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d180124 p = 1 := by simpa only [d180134, d48359, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23079 p hg
    simpa only [d180134, d48359, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180133 p = 1 := by simpa only [d180134, d48359, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23152 p hg
    simpa only [d180134, d48359, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23154 (p : Pattern) (guard : d17372 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17371 p = 1 := by simpa only [d17372, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16327 p hg
    simpa only [d17372, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17372, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21719 p hg
    simpa only [d17372, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23155 (p : Pattern) (guard : d22930 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d22930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21717 p hg
    simpa only [d22930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17372 p = 1 := by simpa only [d22930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23154 p hg
    simpa only [d22930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23156 (p : Pattern) (guard : d149666 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d22930 p = 1 := by simpa only [d149666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23155 p hg
    simpa only [d149666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d149666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21717 p hg
    simpa only [d149666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23157 (p : Pattern) (guard : d180137 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare23158 (p : Pattern) (guard : d180138 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d180137 p = 1 := by simpa only [d180138, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23157 p hg
    simpa only [d180138, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180138, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21719 p hg
    simpa only [d180138, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23159 (p : Pattern) (guard : d180139 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21717 p hg
    simpa only [d180139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180138 p = 1 := by simpa only [d180139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23158 p hg
    simpa only [d180139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23160 (p : Pattern) (guard : d180140 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d180139 p = 1 := by simpa only [d180140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23159 p hg
    simpa only [d180140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21717 p hg
    simpa only [d180140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23161 (p : Pattern) (guard : d180141 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d149666 p = 1 := by simpa only [d180141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23156 p hg
    simpa only [d180141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180140 p = 1 := by simpa only [d180141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23160 p hg
    simpa only [d180141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23162 (p : Pattern) (guard : d180142 p = 1) : d48362 p ≤ (1 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180142, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21716 p hg
    simpa only [d180142, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180141 p = 1 := by simpa only [d180142, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23161 p hg
    simpa only [d180142, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23163 (p : Pattern) (guard : d180143 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180143, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21715 p hg
    simpa only [d180143, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180142 p = 1 := by simpa only [d180143, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23162 p hg
    simpa only [d180143, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23164 (p : Pattern) (guard : d180144 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d180140 p = 1 := by simpa only [d180144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23160 p hg
    simpa only [d180144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21717 p hg
    simpa only [d180144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23165 (p : Pattern) (guard : d180145 p = 1) : d48362 p ≤ (1 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180145, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21716 p hg
    simpa only [d180145, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180144 p = 1 := by simpa only [d180145, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23164 p hg
    simpa only [d180145, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23166 (p : Pattern) (guard : d180146 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180146, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21715 p hg
    simpa only [d180146, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180145 p = 1 := by simpa only [d180146, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23165 p hg
    simpa only [d180146, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23167 (p : Pattern) (guard : d180147 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d180143 p = 1 := by simpa only [d180147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23163 p hg
    simpa only [d180147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180146 p = 1 := by simpa only [d180147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23166 p hg
    simpa only [d180147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23168 (p : Pattern) (guard : d180150 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare23169 (p : Pattern) (guard : d180151 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d180150 p = 1 := by simpa only [d180151, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23168 p hg
    simpa only [d180151, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180151, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21719 p hg
    simpa only [d180151, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23170 (p : Pattern) (guard : d180152 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21717 p hg
    simpa only [d180152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180151 p = 1 := by simpa only [d180152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23169 p hg
    simpa only [d180152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23171 (p : Pattern) (guard : d180153 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d180152 p = 1 := by simpa only [d180153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23170 p hg
    simpa only [d180153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21717 p hg
    simpa only [d180153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23172 (p : Pattern) (guard : d180154 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d180140 p = 1 := by simpa only [d180154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23160 p hg
    simpa only [d180154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180153 p = 1 := by simpa only [d180154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23171 p hg
    simpa only [d180154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23173 (p : Pattern) (guard : d180155 p = 1) : d48362 p ≤ (1 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180155, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21716 p hg
    simpa only [d180155, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180154 p = 1 := by simpa only [d180155, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23172 p hg
    simpa only [d180155, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23174 (p : Pattern) (guard : d180156 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180156, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21715 p hg
    simpa only [d180156, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180155 p = 1 := by simpa only [d180156, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23173 p hg
    simpa only [d180156, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23175 (p : Pattern) (guard : d180157 p = 1) : d48361 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d180153 p = 1 := by simpa only [d180157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23171 p hg
    simpa only [d180157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21717 p hg
    simpa only [d180157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23176 (p : Pattern) (guard : d180158 p = 1) : d48362 p ≤ (1 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180158, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21716 p hg
    simpa only [d180158, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180157 p = 1 := by simpa only [d180158, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23175 p hg
    simpa only [d180158, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23177 (p : Pattern) (guard : d180159 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180159, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21715 p hg
    simpa only [d180159, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180158 p = 1 := by simpa only [d180159, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23176 p hg
    simpa only [d180159, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23178 (p : Pattern) (guard : d180160 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d180156 p = 1 := by simpa only [d180160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23174 p hg
    simpa only [d180160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180159 p = 1 := by simpa only [d180160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23177 p hg
    simpa only [d180160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23179 (p : Pattern) (guard : d180161 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d180147 p = 1 := by simpa only [d180161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23167 p hg
    simpa only [d180161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180160 p = 1 := by simpa only [d180161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23178 p hg
    simpa only [d180161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23180 (p : Pattern) (guard : d180162 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d180161 p = 1 := by simpa only [d180162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23179 p hg
    simpa only [d180162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21726 p hg
    simpa only [d180162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23181 (p : Pattern) (guard : d180163 p = 1) : d48365 p ≤ (1 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d180162 p = 1 := by simpa only [d180163, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23180 p hg
    simpa only [d180163, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180163, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21730 p hg
    simpa only [d180163, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23182 (p : Pattern) (guard : d180164 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180164, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21619 p hg
    simpa only [d180164, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180163 p = 1 := by simpa only [d180164, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23181 p hg
    simpa only [d180164, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23183 (p : Pattern) (guard : d180165 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d180159 p = 1 := by simpa only [d180165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23177 p hg
    simpa only [d180165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21726 p hg
    simpa only [d180165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23184 (p : Pattern) (guard : d180166 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d180160 p = 1 := by simpa only [d180166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23178 p hg
    simpa only [d180166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180165 p = 1 := by simpa only [d180166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23183 p hg
    simpa only [d180166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23185 (p : Pattern) (guard : d180167 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d180166 p = 1 := by simpa only [d180167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23184 p hg
    simpa only [d180167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21726 p hg
    simpa only [d180167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23186 (p : Pattern) (guard : d180168 p = 1) : d48365 p ≤ (1 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d180167 p = 1 := by simpa only [d180168, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23185 p hg
    simpa only [d180168, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180168, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21730 p hg
    simpa only [d180168, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23187 (p : Pattern) (guard : d180169 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180169, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21619 p hg
    simpa only [d180169, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180168 p = 1 := by simpa only [d180169, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23186 p hg
    simpa only [d180169, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23188 (p : Pattern) (guard : d180170 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d180164 p = 1 := by simpa only [d180170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23182 p hg
    simpa only [d180170, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180169 p = 1 := by simpa only [d180170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23187 p hg
    simpa only [d180170, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23189 (p : Pattern) (guard : d180171 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d180170 p = 1 := by simpa only [d180171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23188 p hg
    simpa only [d180171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d180171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23190 (p : Pattern) (guard : d180172 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d180171 p = 1 := by simpa only [d180172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23189 p hg
    simpa only [d180172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d180172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23191 (p : Pattern) (guard : d180173 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d180172 p = 1 := by simpa only [d180173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23190 p hg
    simpa only [d180173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d180173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23192 (p : Pattern) (guard : d180174 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d180165 p = 1 := by simpa only [d180174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23183 p hg
    simpa only [d180174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21726 p hg
    simpa only [d180174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23193 (p : Pattern) (guard : d180175 p = 1) : d48363 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d180174 p = 1 := by simpa only [d180175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23192 p hg
    simpa only [d180175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21726 p hg
    simpa only [d180175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23194 (p : Pattern) (guard : d180176 p = 1) : d48365 p ≤ (1 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d180175 p = 1 := by simpa only [d180176, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23193 p hg
    simpa only [d180176, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180176, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21730 p hg
    simpa only [d180176, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23195 (p : Pattern) (guard : d180177 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180177, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21619 p hg
    simpa only [d180177, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180176 p = 1 := by simpa only [d180177, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23194 p hg
    simpa only [d180177, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23196 (p : Pattern) (guard : d180178 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d180169 p = 1 := by simpa only [d180178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23187 p hg
    simpa only [d180178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180177 p = 1 := by simpa only [d180178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23195 p hg
    simpa only [d180178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23197 (p : Pattern) (guard : d180179 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d180178 p = 1 := by simpa only [d180179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23196 p hg
    simpa only [d180179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d180179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23198 (p : Pattern) (guard : d180180 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d180179 p = 1 := by simpa only [d180180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23197 p hg
    simpa only [d180180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d180180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23199 (p : Pattern) (guard : d180181 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d180180 p = 1 := by simpa only [d180181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23198 p hg
    simpa only [d180181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d180181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23200 (p : Pattern) (guard : d180182 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d180173 p = 1 := by simpa only [d180182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23191 p hg
    simpa only [d180182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180181 p = 1 := by simpa only [d180182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23199 p hg
    simpa only [d180182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23201 (p : Pattern) (guard : d180183 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d180182 p = 1 := by simpa only [d180183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23200 p hg
    simpa only [d180183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d180183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23202 (p : Pattern) (guard : d180184 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d180169 p = 1 := by simpa only [d180184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23187 p hg
    simpa only [d180184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d180184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23203 (p : Pattern) (guard : d180185 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d180184 p = 1 := by simpa only [d180185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23202 p hg
    simpa only [d180185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d180185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23204 (p : Pattern) (guard : d180186 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d180185 p = 1 := by simpa only [d180186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23203 p hg
    simpa only [d180186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d180186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23205 (p : Pattern) (guard : d180187 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d180186 p = 1 := by simpa only [d180187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23204 p hg
    simpa only [d180187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d180187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23206 (p : Pattern) (guard : d180188 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d180187 p = 1 := by simpa only [d180188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23205 p hg
    simpa only [d180188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d180188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23207 (p : Pattern) (guard : d180189 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d180188 p = 1 := by simpa only [d180189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23206 p hg
    simpa only [d180189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d180189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23208 (p : Pattern) (guard : d180190 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d180183 p = 1 := by simpa only [d180190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23201 p hg
    simpa only [d180190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180189 p = 1 := by simpa only [d180190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23207 p hg
    simpa only [d180190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23209 (p : Pattern) (guard : d180191 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d180191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180190 p = 1 := by simpa only [d180191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23208 p hg
    simpa only [d180191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23210 (p : Pattern) (guard : d180192 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d180192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180191 p = 1 := by simpa only [d180192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23209 p hg
    simpa only [d180192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23211 (p : Pattern) (guard : d180193 p = 1) : d48367 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180193, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180193, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180192 p = 1 := by simpa only [d180193, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23210 p hg
    simpa only [d180193, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23212 (p : Pattern) (guard : d180194 p = 1) : d48367 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21713 p hg
    simpa only [d180194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180193 p = 1 := by simpa only [d180194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23211 p hg
    simpa only [d180194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23213 (p : Pattern) (guard : d180195 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d180177 p = 1 := by simpa only [d180195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23195 p hg
    simpa only [d180195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d180195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23214 (p : Pattern) (guard : d180196 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d180195 p = 1 := by simpa only [d180196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23213 p hg
    simpa only [d180196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d180196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23215 (p : Pattern) (guard : d180197 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d180196 p = 1 := by simpa only [d180197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23214 p hg
    simpa only [d180197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d180197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23216 (p : Pattern) (guard : d180198 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d180197 p = 1 := by simpa only [d180198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23215 p hg
    simpa only [d180198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d180198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23217 (p : Pattern) (guard : d180199 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d180198 p = 1 := by simpa only [d180199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23216 p hg
    simpa only [d180199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d180199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23218 (p : Pattern) (guard : d180200 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d180200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180199 p = 1 := by simpa only [d180200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23217 p hg
    simpa only [d180200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23219 (p : Pattern) (guard : d180201 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d180200 p = 1 := by simpa only [d180201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23218 p hg
    simpa only [d180201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d180201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23220 (p : Pattern) (guard : d180202 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d180202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180201 p = 1 := by simpa only [d180202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23219 p hg
    simpa only [d180202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23221 (p : Pattern) (guard : d180203 p = 1) : d48366 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21714 p hg
    simpa only [d180203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180202 p = 1 := by simpa only [d180203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23220 p hg
    simpa only [d180203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23222 (p : Pattern) (guard : d180204 p = 1) : d48367 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180204, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d180204, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180203 p = 1 := by simpa only [d180204, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23221 p hg
    simpa only [d180204, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23223 (p : Pattern) (guard : d180205 p = 1) : d48367 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21713 p hg
    simpa only [d180205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180204 p = 1 := by simpa only [d180205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23222 p hg
    simpa only [d180205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23224 (p : Pattern) (guard : d180206 p = 1) : d48367 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 69 with
  | false =>
    have hg : d180194 p = 1 := by simpa only [d180206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23212 p hg
    simpa only [d180206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180205 p = 1 := by simpa only [d180206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23223 p hg
    simpa only [d180206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23225 (p : Pattern) (guard : d180207 p = 1) : d48367 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 51 with
  | false =>
    have hg : d180206 p = 1 := by simpa only [d180207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23224 p hg
    simpa only [d180207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21713 p hg
    simpa only [d180207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23226 (p : Pattern) (guard : d180208 p = 1) : d48367 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 50 with
  | false =>
    have hg : d180207 p = 1 := by simpa only [d180208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23225 p hg
    simpa only [d180208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21713 p hg
    simpa only [d180208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23227 (p : Pattern) (guard : d180209 p = 1) : d48387 p ≤ (1 : Int) + d47865 p := by
  cases selected : p 49 with
  | false =>
    have hg : d180208 p = 1 := by simpa only [d180209, d48387, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23226 p hg
    simpa only [d180209, d48387, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180209, d48387, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21747 p hg
    simpa only [d180209, d48387, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23228 (p : Pattern) (guard : d180210 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d180134 p = 1 := by simpa only [d180210, d48388, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23153 p hg
    simpa only [d180210, d48388, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180209 p = 1 := by simpa only [d180210, d48388, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23227 p hg
    simpa only [d180210, d48388, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23229 (p : Pattern) (guard : d180211 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180210 p = 1 := by simpa only [d180211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23228 p hg
    simpa only [d180211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23230 (p : Pattern) (guard : d180212 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180211 p = 1 := by simpa only [d180212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23229 p hg
    simpa only [d180212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23231 (p : Pattern) (guard : d180213 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180212 p = 1 := by simpa only [d180213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23230 p hg
    simpa only [d180213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23232 (p : Pattern) (guard : d180214 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180213 p = 1 := by simpa only [d180214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23231 p hg
    simpa only [d180214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23233 (p : Pattern) (guard : d180215 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180214 p = 1 := by simpa only [d180215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23232 p hg
    simpa only [d180215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23234 (p : Pattern) (guard : d180216 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180215 p = 1 := by simpa only [d180216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23233 p hg
    simpa only [d180216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23235 (p : Pattern) (guard : d180217 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180216 p = 1 := by simpa only [d180217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23234 p hg
    simpa only [d180217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23236 (p : Pattern) (guard : d180218 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180217 p = 1 := by simpa only [d180218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23235 p hg
    simpa only [d180218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23237 (p : Pattern) (guard : d180219 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180218 p = 1 := by simpa only [d180219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23236 p hg
    simpa only [d180219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23238 (p : Pattern) (guard : d180220 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180219 p = 1 := by simpa only [d180220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23237 p hg
    simpa only [d180220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23239 (p : Pattern) (guard : d180221 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10250 with
  | false =>
    have hg : d179979 p = 1 := by simpa only [d180221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22874 p hg
    simpa only [d180221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180220 p = 1 := by simpa only [d180221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23238 p hg
    simpa only [d180221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23240 (p : Pattern) (guard : d180222 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 260 with
  | false =>
    have hg : d180221 p = 1 := by simpa only [d180222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23239 p hg
    simpa only [d180222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23241 (p : Pattern) (guard : d180223 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 259 with
  | false =>
    have hg : d180222 p = 1 := by simpa only [d180223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23240 p hg
    simpa only [d180223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23242 (p : Pattern) (guard : d180224 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 258 with
  | false =>
    have hg : d180223 p = 1 := by simpa only [d180224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23241 p hg
    simpa only [d180224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23243 (p : Pattern) (guard : d180225 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 257 with
  | false =>
    have hg : d180224 p = 1 := by simpa only [d180225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23242 p hg
    simpa only [d180225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23244 (p : Pattern) (guard : d180226 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 256 with
  | false =>
    have hg : d180225 p = 1 := by simpa only [d180226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23243 p hg
    simpa only [d180226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23245 (p : Pattern) (guard : d180227 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 255 with
  | false =>
    have hg : d180226 p = 1 := by simpa only [d180227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23244 p hg
    simpa only [d180227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23246 (p : Pattern) (guard : d180228 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 254 with
  | false =>
    have hg : d180227 p = 1 := by simpa only [d180228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23245 p hg
    simpa only [d180228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23247 (p : Pattern) (guard : d180229 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 253 with
  | false =>
    have hg : d180228 p = 1 := by simpa only [d180229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23246 p hg
    simpa only [d180229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23248 (p : Pattern) (guard : d180230 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 252 with
  | false =>
    have hg : d180229 p = 1 := by simpa only [d180230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23247 p hg
    simpa only [d180230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23249 (p : Pattern) (guard : d180231 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 251 with
  | false =>
    have hg : d180230 p = 1 := by simpa only [d180231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23248 p hg
    simpa only [d180231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d180231, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
