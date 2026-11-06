import NetHack.Soko22Hazard87.Compare014
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare3750 (p : Pattern) (guard : d66011 p = 1) : d47700 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d66011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3392 p hg
    simpa only [d66011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d66010 p = 1 := by simpa only [d66011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3749 p hg
    simpa only [d66011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3751 (p : Pattern) (guard : d66012 p = 1) : d47768 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 49 with
  | false =>
    have hg : d66011 p = 1 := by simpa only [d66012, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3750 p hg
    simpa only [d66012, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66012, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3438 p hg
    simpa only [d66012, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3752 (p : Pattern) (guard : d66013 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 48 with
  | false =>
    have hg : d66012 p = 1 := by simpa only [d66013, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3751 p hg
    simpa only [d66013, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66013, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3440 p hg
    simpa only [d66013, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3753 (p : Pattern) (guard : d66014 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d66014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d66013 p = 1 := by simpa only [d66014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3752 p hg
    simpa only [d66014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3754 (p : Pattern) (guard : d66015 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d66015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d66014 p = 1 := by simpa only [d66015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3753 p hg
    simpa only [d66015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3755 (p : Pattern) (guard : d66016 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d66016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d66015 p = 1 := by simpa only [d66016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3754 p hg
    simpa only [d66016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3756 (p : Pattern) (guard : d66017 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d66017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d66016 p = 1 := by simpa only [d66017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3755 p hg
    simpa only [d66017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3757 (p : Pattern) (guard : d66018 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d66018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d66017 p = 1 := by simpa only [d66018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3756 p hg
    simpa only [d66018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3758 (p : Pattern) (guard : d66019 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d66019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d66018 p = 1 := by simpa only [d66019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3757 p hg
    simpa only [d66019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3759 (p : Pattern) (guard : d66020 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d66020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d66019 p = 1 := by simpa only [d66020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3758 p hg
    simpa only [d66020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3760 (p : Pattern) (guard : d66021 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d66021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d66020 p = 1 := by simpa only [d66021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3759 p hg
    simpa only [d66021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3761 (p : Pattern) (guard : d66022 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d66022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d66021 p = 1 := by simpa only [d66022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3760 p hg
    simpa only [d66022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3762 (p : Pattern) (guard : d66023 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d66007 p = 1 := by simpa only [d66023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3685 p hg
    simpa only [d66023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d66022 p = 1 := by simpa only [d66023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3761 p hg
    simpa only [d66023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3763 (p : Pattern) (guard : d2035 p = 1) : d47660 p ≤ (-1 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2034 p = 1 := by simpa only [d2035, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1876 p hg
    simpa only [d2035, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2035, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3397 p hg
    simpa only [d2035, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3764 (p : Pattern) (guard : d2036 p = 1) : d47663 p ≤ (-1 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2035 p = 1 := by simpa only [d2036, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3763 p hg
    simpa only [d2036, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2036, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d2036, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3765 (p : Pattern) (guard : d2037 p = 1) : d47664 p ≤ (-1 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2037, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3396 p hg
    simpa only [d2037, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2036 p = 1 := by simpa only [d2037, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3764 p hg
    simpa only [d2037, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3766 (p : Pattern) (guard : d2038 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2037 p = 1 := by simpa only [d2038, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3765 p hg
    simpa only [d2038, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2038, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3402 p hg
    simpa only [d2038, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3767 (p : Pattern) (guard : d2053 p = 1) : d47660 p ≤ (-1 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2052 p = 1 := by simpa only [d2053, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1909 p hg
    simpa only [d2053, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2053, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3397 p hg
    simpa only [d2053, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3768 (p : Pattern) (guard : d2054 p = 1) : d47663 p ≤ (-1 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2053 p = 1 := by simpa only [d2054, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3767 p hg
    simpa only [d2054, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2054, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d2054, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3769 (p : Pattern) (guard : d2055 p = 1) : d47664 p ≤ (-1 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2055, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3396 p hg
    simpa only [d2055, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2054 p = 1 := by simpa only [d2055, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3768 p hg
    simpa only [d2055, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3770 (p : Pattern) (guard : d2056 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2055 p = 1 := by simpa only [d2056, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3769 p hg
    simpa only [d2056, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2056, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3402 p hg
    simpa only [d2056, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3771 (p : Pattern) (guard : d2057 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2038 p = 1 := by simpa only [d2057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3766 p hg
    simpa only [d2057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2056 p = 1 := by simpa only [d2057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3770 p hg
    simpa only [d2057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3772 (p : Pattern) (guard : d2065 p = 1) : d47660 p ≤ (-1 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2064 p = 1 := by simpa only [d2065, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1929 p hg
    simpa only [d2065, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2065, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3397 p hg
    simpa only [d2065, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3773 (p : Pattern) (guard : d2066 p = 1) : d47663 p ≤ (-1 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2065 p = 1 := by simpa only [d2066, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3772 p hg
    simpa only [d2066, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2066, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d2066, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3774 (p : Pattern) (guard : d2067 p = 1) : d47664 p ≤ (-1 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2067, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3396 p hg
    simpa only [d2067, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2066 p = 1 := by simpa only [d2067, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3773 p hg
    simpa only [d2067, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3775 (p : Pattern) (guard : d2068 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2067 p = 1 := by simpa only [d2068, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3774 p hg
    simpa only [d2068, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2068, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3402 p hg
    simpa only [d2068, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3776 (p : Pattern) (guard : d2069 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2056 p = 1 := by simpa only [d2069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3770 p hg
    simpa only [d2069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2068 p = 1 := by simpa only [d2069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3775 p hg
    simpa only [d2069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3777 (p : Pattern) (guard : d2070 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2057 p = 1 := by simpa only [d2070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3771 p hg
    simpa only [d2070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2069 p = 1 := by simpa only [d2070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3776 p hg
    simpa only [d2070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3778 (p : Pattern) (guard : d2071 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2068 p = 1 := by simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3775 p hg
    simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3404 p hg
    simpa only [d2071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3779 (p : Pattern) (guard : d2072 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2069 p = 1 := by simpa only [d2072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3776 p hg
    simpa only [d2072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2071 p = 1 := by simpa only [d2072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3778 p hg
    simpa only [d2072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3780 (p : Pattern) (guard : d2073 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d2070 p = 1 := by simpa only [d2073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3777 p hg
    simpa only [d2073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2072 p = 1 := by simpa only [d2073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3779 p hg
    simpa only [d2073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3781 (p : Pattern) (guard : d2074 p = 1) : d47686 p ≤ (-1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2074, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3395 p hg
    simpa only [d2074, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2073 p = 1 := by simpa only [d2074, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3780 p hg
    simpa only [d2074, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3782 (p : Pattern) (guard : d2075 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2075, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3394 p hg
    simpa only [d2075, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2074 p = 1 := by simpa only [d2075, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3781 p hg
    simpa only [d2075, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3783 (p : Pattern) (guard : d2080 p = 1) : d47660 p ≤ (-1 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2079 p = 1 := by simpa only [d2080, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1949 p hg
    simpa only [d2080, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2080, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3397 p hg
    simpa only [d2080, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3784 (p : Pattern) (guard : d2081 p = 1) : d47663 p ≤ (-1 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2080 p = 1 := by simpa only [d2081, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3783 p hg
    simpa only [d2081, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2081, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d2081, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3785 (p : Pattern) (guard : d2082 p = 1) : d47664 p ≤ (-1 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2082, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3396 p hg
    simpa only [d2082, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2081 p = 1 := by simpa only [d2082, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3784 p hg
    simpa only [d2082, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3786 (p : Pattern) (guard : d2083 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2082 p = 1 := by simpa only [d2083, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3785 p hg
    simpa only [d2083, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2083, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3402 p hg
    simpa only [d2083, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3787 (p : Pattern) (guard : d2084 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2083 p = 1 := by simpa only [d2084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3786 p hg
    simpa only [d2084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3404 p hg
    simpa only [d2084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3788 (p : Pattern) (guard : d2085 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2071 p = 1 := by simpa only [d2085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3778 p hg
    simpa only [d2085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2084 p = 1 := by simpa only [d2085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3787 p hg
    simpa only [d2085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3789 (p : Pattern) (guard : d2086 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d2072 p = 1 := by simpa only [d2086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3779 p hg
    simpa only [d2086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2085 p = 1 := by simpa only [d2086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3788 p hg
    simpa only [d2086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3790 (p : Pattern) (guard : d2087 p = 1) : d47686 p ≤ (-1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2087, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3395 p hg
    simpa only [d2087, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2086 p = 1 := by simpa only [d2087, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3789 p hg
    simpa only [d2087, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3791 (p : Pattern) (guard : d2088 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2088, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3394 p hg
    simpa only [d2088, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2087 p = 1 := by simpa only [d2088, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3790 p hg
    simpa only [d2088, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3792 (p : Pattern) (guard : d2089 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d2075 p = 1 := by simpa only [d2089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3782 p hg
    simpa only [d2089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2088 p = 1 := by simpa only [d2089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3791 p hg
    simpa only [d2089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3793 (p : Pattern) (guard : d2090 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d2088 p = 1 := by simpa only [d2090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3791 p hg
    simpa only [d2090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3410 p hg
    simpa only [d2090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3794 (p : Pattern) (guard : d2091 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d2089 p = 1 := by simpa only [d2091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3792 p hg
    simpa only [d2091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2090 p = 1 := by simpa only [d2091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3793 p hg
    simpa only [d2091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3795 (p : Pattern) (guard : d2092 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d2091 p = 1 := by simpa only [d2092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3794 p hg
    simpa only [d2092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3410 p hg
    simpa only [d2092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3796 (p : Pattern) (guard : d2093 p = 1) : d47699 p ≤ (-1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d2092 p = 1 := by simpa only [d2093, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3795 p hg
    simpa only [d2093, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2093, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3414 p hg
    simpa only [d2093, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3797 (p : Pattern) (guard : d2094 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2094, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1133 p hg
    simpa only [d2094, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2093 p = 1 := by simpa only [d2094, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3796 p hg
    simpa only [d2094, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3798 (p : Pattern) (guard : d2095 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d2090 p = 1 := by simpa only [d2095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3793 p hg
    simpa only [d2095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3410 p hg
    simpa only [d2095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3799 (p : Pattern) (guard : d2096 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d2095 p = 1 := by simpa only [d2096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3798 p hg
    simpa only [d2096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3410 p hg
    simpa only [d2096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3800 (p : Pattern) (guard : d2097 p = 1) : d47699 p ≤ (-1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d2096 p = 1 := by simpa only [d2097, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3799 p hg
    simpa only [d2097, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2097, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3414 p hg
    simpa only [d2097, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3801 (p : Pattern) (guard : d2098 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2098, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1133 p hg
    simpa only [d2098, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2097 p = 1 := by simpa only [d2098, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3800 p hg
    simpa only [d2098, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3802 (p : Pattern) (guard : d2099 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d2094 p = 1 := by simpa only [d2099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3797 p hg
    simpa only [d2099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2098 p = 1 := by simpa only [d2099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3801 p hg
    simpa only [d2099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3803 (p : Pattern) (guard : d2100 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d2099 p = 1 := by simpa only [d2100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3802 p hg
    simpa only [d2100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d2100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3804 (p : Pattern) (guard : d2101 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d2100 p = 1 := by simpa only [d2101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3803 p hg
    simpa only [d2101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d2101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3805 (p : Pattern) (guard : d2102 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d2102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2101 p = 1 := by simpa only [d2102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3804 p hg
    simpa only [d2102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3806 (p : Pattern) (guard : d2103 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d2098 p = 1 := by simpa only [d2103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3801 p hg
    simpa only [d2103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d2103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3807 (p : Pattern) (guard : d2104 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d2103 p = 1 := by simpa only [d2104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3806 p hg
    simpa only [d2104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d2104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3808 (p : Pattern) (guard : d2105 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d2104 p = 1 := by simpa only [d2105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3807 p hg
    simpa only [d2105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d2105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3809 (p : Pattern) (guard : d2106 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d2106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2105 p = 1 := by simpa only [d2106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3808 p hg
    simpa only [d2106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3810 (p : Pattern) (guard : d2107 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d2102 p = 1 := by simpa only [d2107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3805 p hg
    simpa only [d2107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2106 p = 1 := by simpa only [d2107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3809 p hg
    simpa only [d2107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3811 (p : Pattern) (guard : d2108 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d2108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2107 p = 1 := by simpa only [d2108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3810 p hg
    simpa only [d2108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3812 (p : Pattern) (guard : d2109 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d2108 p = 1 := by simpa only [d2109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3811 p hg
    simpa only [d2109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d2109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3813 (p : Pattern) (guard : d2110 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d2110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2109 p = 1 := by simpa only [d2110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3812 p hg
    simpa only [d2110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3814 (p : Pattern) (guard : d2111 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d2111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2110 p = 1 := by simpa only [d2111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3813 p hg
    simpa only [d2111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3815 (p : Pattern) (guard : d2112 p = 1) : d47700 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2112, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1131 p hg
    simpa only [d2112, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2111 p = 1 := by simpa only [d2112, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3814 p hg
    simpa only [d2112, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3816 (p : Pattern) (guard : d2115 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d2101 p = 1 := by simpa only [d2115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3804 p hg
    simpa only [d2115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d2115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3817 (p : Pattern) (guard : d2116 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d2105 p = 1 := by simpa only [d2116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3808 p hg
    simpa only [d2116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d2116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3818 (p : Pattern) (guard : d2117 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d2115 p = 1 := by simpa only [d2117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3816 p hg
    simpa only [d2117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2116 p = 1 := by simpa only [d2117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3817 p hg
    simpa only [d2117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3819 (p : Pattern) (guard : d2118 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d2118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2117 p = 1 := by simpa only [d2118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3818 p hg
    simpa only [d2118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3820 (p : Pattern) (guard : d2119 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d2118 p = 1 := by simpa only [d2119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3819 p hg
    simpa only [d2119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d2119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3821 (p : Pattern) (guard : d2120 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d2120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2119 p = 1 := by simpa only [d2120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3820 p hg
    simpa only [d2120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3822 (p : Pattern) (guard : d2121 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d2121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2120 p = 1 := by simpa only [d2121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3821 p hg
    simpa only [d2121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3823 (p : Pattern) (guard : d53794 p = 1) : d47700 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53794, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1131 p hg
    simpa only [d53794, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2121 p = 1 := by simpa only [d53794, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3822 p hg
    simpa only [d53794, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3824 (p : Pattern) (guard : d66024 p = 1) : d47700 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d2112 p = 1 := by simpa only [d66024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3815 p hg
    simpa only [d66024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53794 p = 1 := by simpa only [d66024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3823 p hg
    simpa only [d66024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3825 (p : Pattern) (guard : d66025 p = 1) : d47700 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d66024 p = 1 := by simpa only [d66025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3824 p hg
    simpa only [d66025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3392 p hg
    simpa only [d66025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3826 (p : Pattern) (guard : d66026 p = 1) : d47700 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d66025 p = 1 := by simpa only [d66026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3825 p hg
    simpa only [d66026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3392 p hg
    simpa only [d66026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3827 (p : Pattern) (guard : d66027 p = 1) : d47700 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d66027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3392 p hg
    simpa only [d66027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d66026 p = 1 := by simpa only [d66027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3826 p hg
    simpa only [d66027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3828 (p : Pattern) (guard : d66028 p = 1) : d47768 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 49 with
  | false =>
    have hg : d66027 p = 1 := by simpa only [d66028, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3827 p hg
    simpa only [d66028, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66028, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3438 p hg
    simpa only [d66028, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3829 (p : Pattern) (guard : d66029 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 48 with
  | false =>
    have hg : d66028 p = 1 := by simpa only [d66029, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3828 p hg
    simpa only [d66029, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66029, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3440 p hg
    simpa only [d66029, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3830 (p : Pattern) (guard : d66030 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d66030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d66029 p = 1 := by simpa only [d66030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3829 p hg
    simpa only [d66030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3831 (p : Pattern) (guard : d66031 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d66031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d66030 p = 1 := by simpa only [d66031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3830 p hg
    simpa only [d66031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3832 (p : Pattern) (guard : d66032 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d66032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d66031 p = 1 := by simpa only [d66032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3831 p hg
    simpa only [d66032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3833 (p : Pattern) (guard : d66033 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d66033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d66032 p = 1 := by simpa only [d66033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3832 p hg
    simpa only [d66033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3834 (p : Pattern) (guard : d66034 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d66034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d66033 p = 1 := by simpa only [d66034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3833 p hg
    simpa only [d66034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3835 (p : Pattern) (guard : d66035 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d66035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d66034 p = 1 := by simpa only [d66035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3834 p hg
    simpa only [d66035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3836 (p : Pattern) (guard : d66036 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d66036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d66035 p = 1 := by simpa only [d66036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3835 p hg
    simpa only [d66036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3837 (p : Pattern) (guard : d66037 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d66037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66037, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d66036 p = 1 := by simpa only [d66037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3836 p hg
    simpa only [d66037, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3838 (p : Pattern) (guard : d66038 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d66038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66038, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d66037 p = 1 := by simpa only [d66038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3837 p hg
    simpa only [d66038, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3839 (p : Pattern) (guard : d66039 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d66039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d66038 p = 1 := by simpa only [d66039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3838 p hg
    simpa only [d66039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3840 (p : Pattern) (guard : d66040 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10250 with
  | false =>
    have hg : d66023 p = 1 := by simpa only [d66040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3762 p hg
    simpa only [d66040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d66039 p = 1 := by simpa only [d66040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3839 p hg
    simpa only [d66040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3841 (p : Pattern) (guard : d66041 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 260 with
  | false =>
    have hg : d66040 p = 1 := by simpa only [d66041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3840 p hg
    simpa only [d66041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3842 (p : Pattern) (guard : d66042 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 259 with
  | false =>
    have hg : d66041 p = 1 := by simpa only [d66042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3841 p hg
    simpa only [d66042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3843 (p : Pattern) (guard : d66043 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 258 with
  | false =>
    have hg : d66042 p = 1 := by simpa only [d66043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3842 p hg
    simpa only [d66043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3844 (p : Pattern) (guard : d66044 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 257 with
  | false =>
    have hg : d66043 p = 1 := by simpa only [d66044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3843 p hg
    simpa only [d66044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3845 (p : Pattern) (guard : d66045 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 256 with
  | false =>
    have hg : d66044 p = 1 := by simpa only [d66045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3844 p hg
    simpa only [d66045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3846 (p : Pattern) (guard : d66046 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 255 with
  | false =>
    have hg : d66045 p = 1 := by simpa only [d66046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3845 p hg
    simpa only [d66046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3847 (p : Pattern) (guard : d66047 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 254 with
  | false =>
    have hg : d66046 p = 1 := by simpa only [d66047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3846 p hg
    simpa only [d66047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3848 (p : Pattern) (guard : d66048 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 253 with
  | false =>
    have hg : d66047 p = 1 := by simpa only [d66048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3847 p hg
    simpa only [d66048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3849 (p : Pattern) (guard : d66049 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 252 with
  | false =>
    have hg : d66048 p = 1 := by simpa only [d66049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3848 p hg
    simpa only [d66049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3850 (p : Pattern) (guard : d66050 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 251 with
  | false =>
    have hg : d66049 p = 1 := by simpa only [d66050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3849 p hg
    simpa only [d66050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3851 (p : Pattern) (guard : d66051 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 250 with
  | false =>
    have hg : d66050 p = 1 := by simpa only [d66051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3850 p hg
    simpa only [d66051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3852 (p : Pattern) (guard : d66052 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 249 with
  | false =>
    have hg : d66051 p = 1 := by simpa only [d66052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3851 p hg
    simpa only [d66052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3853 (p : Pattern) (guard : d66053 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 245 with
  | false =>
    have hg : d66052 p = 1 := by simpa only [d66053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3852 p hg
    simpa only [d66053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3854 (p : Pattern) (guard : d66054 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 200 with
  | false =>
    have hg : d66053 p = 1 := by simpa only [d66054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3853 p hg
    simpa only [d66054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3855 (p : Pattern) (guard : d66055 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 199 with
  | false =>
    have hg : d66054 p = 1 := by simpa only [d66055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3854 p hg
    simpa only [d66055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3856 (p : Pattern) (guard : d66056 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 186 with
  | false =>
    have hg : d66055 p = 1 := by simpa only [d66056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3855 p hg
    simpa only [d66056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3857 (p : Pattern) (guard : d66057 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 185 with
  | false =>
    have hg : d66056 p = 1 := by simpa only [d66057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3856 p hg
    simpa only [d66057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3858 (p : Pattern) (guard : d66058 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 184 with
  | false =>
    have hg : d66057 p = 1 := by simpa only [d66058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3857 p hg
    simpa only [d66058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3859 (p : Pattern) (guard : d66059 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 181 with
  | false =>
    have hg : d66058 p = 1 := by simpa only [d66059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3858 p hg
    simpa only [d66059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3860 (p : Pattern) (guard : d66060 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 177 with
  | false =>
    have hg : d66059 p = 1 := by simpa only [d66060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3859 p hg
    simpa only [d66060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3861 (p : Pattern) (guard : d66061 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 164 with
  | false =>
    have hg : d66060 p = 1 := by simpa only [d66061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3860 p hg
    simpa only [d66061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3862 (p : Pattern) (guard : d66062 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 156 with
  | false =>
    have hg : d66061 p = 1 := by simpa only [d66062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3861 p hg
    simpa only [d66062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3863 (p : Pattern) (guard : d66063 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 155 with
  | false =>
    have hg : d66062 p = 1 := by simpa only [d66063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3862 p hg
    simpa only [d66063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3864 (p : Pattern) (guard : d66064 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 134 with
  | false =>
    have hg : d66063 p = 1 := by simpa only [d66064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3863 p hg
    simpa only [d66064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3865 (p : Pattern) (guard : d66065 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 133 with
  | false =>
    have hg : d66064 p = 1 := by simpa only [d66065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3864 p hg
    simpa only [d66065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3866 (p : Pattern) (guard : d66066 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 120 with
  | false =>
    have hg : d66065 p = 1 := by simpa only [d66066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3865 p hg
    simpa only [d66066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3867 (p : Pattern) (guard : d66067 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 118 with
  | false =>
    have hg : d66066 p = 1 := by simpa only [d66067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3866 p hg
    simpa only [d66067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3868 (p : Pattern) (guard : d66068 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 114 with
  | false =>
    have hg : d66067 p = 1 := by simpa only [d66068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3867 p hg
    simpa only [d66068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3869 (p : Pattern) (guard : d66069 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 111 with
  | false =>
    have hg : d66068 p = 1 := by simpa only [d66069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3868 p hg
    simpa only [d66069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3870 (p : Pattern) (guard : d66070 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 98 with
  | false =>
    have hg : d66069 p = 1 := by simpa only [d66070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3869 p hg
    simpa only [d66070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3871 (p : Pattern) (guard : d66071 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 97 with
  | false =>
    have hg : d66070 p = 1 := by simpa only [d66071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3870 p hg
    simpa only [d66071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3872 (p : Pattern) (guard : d66072 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 94 with
  | false =>
    have hg : d66071 p = 1 := by simpa only [d66072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3871 p hg
    simpa only [d66072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3873 (p : Pattern) (guard : d66073 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 76 with
  | false =>
    have hg : d66072 p = 1 := by simpa only [d66073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3872 p hg
    simpa only [d66073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3874 (p : Pattern) (guard : d66074 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 67 with
  | false =>
    have hg : d66073 p = 1 := by simpa only [d66074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3873 p hg
    simpa only [d66074, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66074, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3875 (p : Pattern) (guard : d66075 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 52 with
  | false =>
    have hg : d66074 p = 1 := by simpa only [d66075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3874 p hg
    simpa only [d66075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3876 (p : Pattern) (guard : d66076 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 47 with
  | false =>
    have hg : d66075 p = 1 := by simpa only [d66076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3875 p hg
    simpa only [d66076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3877 (p : Pattern) (guard : d66077 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 46 with
  | false =>
    have hg : d66076 p = 1 := by simpa only [d66077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3876 p hg
    simpa only [d66077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3878 (p : Pattern) (guard : d66078 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 45 with
  | false =>
    have hg : d66077 p = 1 := by simpa only [d66078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3877 p hg
    simpa only [d66078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3879 (p : Pattern) (guard : d66079 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 30 with
  | false =>
    have hg : d66078 p = 1 := by simpa only [d66079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3878 p hg
    simpa only [d66079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3880 (p : Pattern) (guard : d66080 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 29 with
  | false =>
    have hg : d66079 p = 1 := by simpa only [d66080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3879 p hg
    simpa only [d66080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3881 (p : Pattern) (guard : d66081 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 28 with
  | false =>
    have hg : d66080 p = 1 := by simpa only [d66081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3880 p hg
    simpa only [d66081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3882 (p : Pattern) (guard : d66082 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 27 with
  | false =>
    have hg : d66081 p = 1 := by simpa only [d66082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3881 p hg
    simpa only [d66082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3883 (p : Pattern) (guard : d66083 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 25 with
  | false =>
    have hg : d66082 p = 1 := by simpa only [d66083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3882 p hg
    simpa only [d66083, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66083, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3884 (p : Pattern) (guard : d2525 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d2525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d213 p = 1 := by simpa only [d2525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2590 p hg
    simpa only [d2525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3885 (p : Pattern) (guard : d2526 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d2525 p = 1 := by simpa only [d2526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3884 p hg
    simpa only [d2526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d2526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3886 (p : Pattern) (guard : d2527 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d2526 p = 1 := by simpa only [d2527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3885 p hg
    simpa only [d2527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d2527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3887 (p : Pattern) (guard : d62702 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d62702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2527 p = 1 := by simpa only [d62702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3886 p hg
    simpa only [d62702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3888 (p : Pattern) (guard : d62703 p = 1) : d47768 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 49 with
  | false =>
    have hg : d62702 p = 1 := by simpa only [d62703, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3887 p hg
    simpa only [d62703, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62703, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2528 p hg
    simpa only [d62703, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3889 (p : Pattern) (guard : d62704 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 48 with
  | false =>
    have hg : d62703 p = 1 := by simpa only [d62704, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3888 p hg
    simpa only [d62704, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62704, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2530 p hg
    simpa only [d62704, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3890 (p : Pattern) (guard : d62705 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62704 p = 1 := by simpa only [d62705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3889 p hg
    simpa only [d62705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3891 (p : Pattern) (guard : d62706 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62705 p = 1 := by simpa only [d62706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3890 p hg
    simpa only [d62706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3892 (p : Pattern) (guard : d62707 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62706 p = 1 := by simpa only [d62707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3891 p hg
    simpa only [d62707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3893 (p : Pattern) (guard : d62708 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62707 p = 1 := by simpa only [d62708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3892 p hg
    simpa only [d62708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3894 (p : Pattern) (guard : d62709 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62708 p = 1 := by simpa only [d62709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3893 p hg
    simpa only [d62709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3895 (p : Pattern) (guard : d2536 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d283 p = 1 := by simpa only [d2536, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2334 p hg
    simpa only [d2536, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2536, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2536, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3896 (p : Pattern) (guard : d2537 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d2537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2536 p = 1 := by simpa only [d2537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3895 p hg
    simpa only [d2537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3897 (p : Pattern) (guard : d2538 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d2537 p = 1 := by simpa only [d2538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3896 p hg
    simpa only [d2538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d2538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3898 (p : Pattern) (guard : d2539 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d2538 p = 1 := by simpa only [d2539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3897 p hg
    simpa only [d2539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d2539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3899 (p : Pattern) (guard : d62710 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d62710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2539 p = 1 := by simpa only [d62710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3898 p hg
    simpa only [d62710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3900 (p : Pattern) (guard : d62711 p = 1) : d47768 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 49 with
  | false =>
    have hg : d62710 p = 1 := by simpa only [d62711, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3899 p hg
    simpa only [d62711, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62711, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2528 p hg
    simpa only [d62711, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3901 (p : Pattern) (guard : d62712 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 48 with
  | false =>
    have hg : d62711 p = 1 := by simpa only [d62712, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3900 p hg
    simpa only [d62712, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62712, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2530 p hg
    simpa only [d62712, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3902 (p : Pattern) (guard : d62713 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62712 p = 1 := by simpa only [d62713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3901 p hg
    simpa only [d62713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3903 (p : Pattern) (guard : d62714 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62713 p = 1 := by simpa only [d62714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3902 p hg
    simpa only [d62714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3904 (p : Pattern) (guard : d62715 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62714 p = 1 := by simpa only [d62715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3903 p hg
    simpa only [d62715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3905 (p : Pattern) (guard : d62716 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62715 p = 1 := by simpa only [d62716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3904 p hg
    simpa only [d62716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3906 (p : Pattern) (guard : d62717 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62716 p = 1 := by simpa only [d62717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3905 p hg
    simpa only [d62717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3907 (p : Pattern) (guard : d62718 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d62709 p = 1 := by simpa only [d62718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3894 p hg
    simpa only [d62718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62717 p = 1 := by simpa only [d62718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3906 p hg
    simpa only [d62718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3908 (p : Pattern) (guard : d2549 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d496 p = 1 := by simpa only [d2549, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2348 p hg
    simpa only [d2549, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2549, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2549, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3909 (p : Pattern) (guard : d2550 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d2550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2549 p = 1 := by simpa only [d2550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3908 p hg
    simpa only [d2550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3910 (p : Pattern) (guard : d2551 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d2550 p = 1 := by simpa only [d2551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3909 p hg
    simpa only [d2551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d2551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3911 (p : Pattern) (guard : d2552 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d2551 p = 1 := by simpa only [d2552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3910 p hg
    simpa only [d2552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d2552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3912 (p : Pattern) (guard : d62719 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d62719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2552 p = 1 := by simpa only [d62719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3911 p hg
    simpa only [d62719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3913 (p : Pattern) (guard : d62720 p = 1) : d47768 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 49 with
  | false =>
    have hg : d62719 p = 1 := by simpa only [d62720, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3912 p hg
    simpa only [d62720, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62720, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2528 p hg
    simpa only [d62720, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3914 (p : Pattern) (guard : d62721 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 48 with
  | false =>
    have hg : d62720 p = 1 := by simpa only [d62721, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3913 p hg
    simpa only [d62721, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62721, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2530 p hg
    simpa only [d62721, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3915 (p : Pattern) (guard : d62722 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62721 p = 1 := by simpa only [d62722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3914 p hg
    simpa only [d62722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3916 (p : Pattern) (guard : d62723 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62722 p = 1 := by simpa only [d62723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3915 p hg
    simpa only [d62723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3917 (p : Pattern) (guard : d62724 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62723 p = 1 := by simpa only [d62724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3916 p hg
    simpa only [d62724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3918 (p : Pattern) (guard : d62725 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62724 p = 1 := by simpa only [d62725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3917 p hg
    simpa only [d62725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3919 (p : Pattern) (guard : d62726 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62725 p = 1 := by simpa only [d62726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3918 p hg
    simpa only [d62726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3920 (p : Pattern) (guard : d62727 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62726 p = 1 := by simpa only [d62727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3919 p hg
    simpa only [d62727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3921 (p : Pattern) (guard : d62728 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d62718 p = 1 := by simpa only [d62728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3907 p hg
    simpa only [d62728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62727 p = 1 := by simpa only [d62728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3920 p hg
    simpa only [d62728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3922 (p : Pattern) (guard : d2563 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d788 p = 1 := by simpa only [d2563, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2363 p hg
    simpa only [d2563, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2563, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2563, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3923 (p : Pattern) (guard : d2564 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d2564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2563 p = 1 := by simpa only [d2564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3922 p hg
    simpa only [d2564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3924 (p : Pattern) (guard : d2565 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d2564 p = 1 := by simpa only [d2565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3923 p hg
    simpa only [d2565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d2565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3925 (p : Pattern) (guard : d2566 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d2565 p = 1 := by simpa only [d2566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3924 p hg
    simpa only [d2566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d2566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3926 (p : Pattern) (guard : d62729 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d62729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2566 p = 1 := by simpa only [d62729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3925 p hg
    simpa only [d62729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3927 (p : Pattern) (guard : d62730 p = 1) : d47768 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 49 with
  | false =>
    have hg : d62729 p = 1 := by simpa only [d62730, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3926 p hg
    simpa only [d62730, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62730, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2528 p hg
    simpa only [d62730, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3928 (p : Pattern) (guard : d62731 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 48 with
  | false =>
    have hg : d62730 p = 1 := by simpa only [d62731, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3927 p hg
    simpa only [d62731, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62731, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2530 p hg
    simpa only [d62731, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3929 (p : Pattern) (guard : d62732 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62731 p = 1 := by simpa only [d62732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3928 p hg
    simpa only [d62732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3930 (p : Pattern) (guard : d62733 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62732 p = 1 := by simpa only [d62733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3929 p hg
    simpa only [d62733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3931 (p : Pattern) (guard : d62734 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62733 p = 1 := by simpa only [d62734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3930 p hg
    simpa only [d62734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3932 (p : Pattern) (guard : d62735 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62734 p = 1 := by simpa only [d62735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3931 p hg
    simpa only [d62735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3933 (p : Pattern) (guard : d62736 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62735 p = 1 := by simpa only [d62736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3932 p hg
    simpa only [d62736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3934 (p : Pattern) (guard : d62737 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62736 p = 1 := by simpa only [d62737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3933 p hg
    simpa only [d62737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3935 (p : Pattern) (guard : d62738 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62737 p = 1 := by simpa only [d62738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3934 p hg
    simpa only [d62738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3936 (p : Pattern) (guard : d62739 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d62728 p = 1 := by simpa only [d62739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3921 p hg
    simpa only [d62739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62738 p = 1 := by simpa only [d62739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3935 p hg
    simpa only [d62739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3937 (p : Pattern) (guard : d2578 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d2578, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2379 p hg
    simpa only [d2578, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2578, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2578, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3938 (p : Pattern) (guard : d2579 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d2579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2578 p = 1 := by simpa only [d2579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3937 p hg
    simpa only [d2579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3939 (p : Pattern) (guard : d2580 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d2579 p = 1 := by simpa only [d2580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3938 p hg
    simpa only [d2580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d2580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3940 (p : Pattern) (guard : d2581 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d2580 p = 1 := by simpa only [d2581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3939 p hg
    simpa only [d2581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d2581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3941 (p : Pattern) (guard : d62740 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d62740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2581 p = 1 := by simpa only [d62740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3940 p hg
    simpa only [d62740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3942 (p : Pattern) (guard : d62741 p = 1) : d47768 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 49 with
  | false =>
    have hg : d62740 p = 1 := by simpa only [d62741, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3941 p hg
    simpa only [d62741, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62741, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2528 p hg
    simpa only [d62741, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3943 (p : Pattern) (guard : d62742 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 48 with
  | false =>
    have hg : d62741 p = 1 := by simpa only [d62742, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3942 p hg
    simpa only [d62742, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62742, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2530 p hg
    simpa only [d62742, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3944 (p : Pattern) (guard : d62743 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62742 p = 1 := by simpa only [d62743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3943 p hg
    simpa only [d62743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3945 (p : Pattern) (guard : d62744 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62743 p = 1 := by simpa only [d62744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3944 p hg
    simpa only [d62744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3946 (p : Pattern) (guard : d62745 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62744 p = 1 := by simpa only [d62745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3945 p hg
    simpa only [d62745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3947 (p : Pattern) (guard : d62746 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62745 p = 1 := by simpa only [d62746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3946 p hg
    simpa only [d62746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3948 (p : Pattern) (guard : d62747 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62746 p = 1 := by simpa only [d62747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3947 p hg
    simpa only [d62747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3949 (p : Pattern) (guard : d62748 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62747 p = 1 := by simpa only [d62748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3948 p hg
    simpa only [d62748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3950 (p : Pattern) (guard : d62749 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62748 p = 1 := by simpa only [d62749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3949 p hg
    simpa only [d62749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3951 (p : Pattern) (guard : d62750 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62749 p = 1 := by simpa only [d62750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3950 p hg
    simpa only [d62750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3952 (p : Pattern) (guard : d62751 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d62739 p = 1 := by simpa only [d62751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3936 p hg
    simpa only [d62751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62750 p = 1 := by simpa only [d62751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3951 p hg
    simpa only [d62751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3953 (p : Pattern) (guard : d2594 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1628 p = 1 := by simpa only [d2594, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2396 p hg
    simpa only [d2594, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2594, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2594, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3954 (p : Pattern) (guard : d2595 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d2595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2594 p = 1 := by simpa only [d2595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3953 p hg
    simpa only [d2595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3955 (p : Pattern) (guard : d2596 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d2595 p = 1 := by simpa only [d2596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3954 p hg
    simpa only [d2596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d2596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3956 (p : Pattern) (guard : d2597 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d2596 p = 1 := by simpa only [d2597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3955 p hg
    simpa only [d2597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d2597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3957 (p : Pattern) (guard : d62752 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d62752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2597 p = 1 := by simpa only [d62752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3956 p hg
    simpa only [d62752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3958 (p : Pattern) (guard : d62753 p = 1) : d47768 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 49 with
  | false =>
    have hg : d62752 p = 1 := by simpa only [d62753, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3957 p hg
    simpa only [d62753, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62753, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2528 p hg
    simpa only [d62753, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3959 (p : Pattern) (guard : d62754 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 48 with
  | false =>
    have hg : d62753 p = 1 := by simpa only [d62754, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3958 p hg
    simpa only [d62754, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62754, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2530 p hg
    simpa only [d62754, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3960 (p : Pattern) (guard : d62755 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62754 p = 1 := by simpa only [d62755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3959 p hg
    simpa only [d62755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3961 (p : Pattern) (guard : d62756 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62755 p = 1 := by simpa only [d62756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3960 p hg
    simpa only [d62756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3962 (p : Pattern) (guard : d62757 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62756 p = 1 := by simpa only [d62757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3961 p hg
    simpa only [d62757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3963 (p : Pattern) (guard : d62758 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62757 p = 1 := by simpa only [d62758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3962 p hg
    simpa only [d62758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3964 (p : Pattern) (guard : d62759 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62758 p = 1 := by simpa only [d62759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3963 p hg
    simpa only [d62759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3965 (p : Pattern) (guard : d62760 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62759 p = 1 := by simpa only [d62760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3964 p hg
    simpa only [d62760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3966 (p : Pattern) (guard : d62761 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62760 p = 1 := by simpa only [d62761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3965 p hg
    simpa only [d62761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3967 (p : Pattern) (guard : d62762 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62761 p = 1 := by simpa only [d62762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3966 p hg
    simpa only [d62762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3968 (p : Pattern) (guard : d62763 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62762 p = 1 := by simpa only [d62763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3967 p hg
    simpa only [d62763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3969 (p : Pattern) (guard : d62764 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d62751 p = 1 := by simpa only [d62764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3952 p hg
    simpa only [d62764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62763 p = 1 := by simpa only [d62764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3968 p hg
    simpa only [d62764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3970 (p : Pattern) (guard : d2611 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d2111 p = 1 := by simpa only [d2611, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2414 p hg
    simpa only [d2611, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2611, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2482 p hg
    simpa only [d2611, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3971 (p : Pattern) (guard : d2612 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d2612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2611 p = 1 := by simpa only [d2612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3970 p hg
    simpa only [d2612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3972 (p : Pattern) (guard : d2613 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d2612 p = 1 := by simpa only [d2613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3971 p hg
    simpa only [d2613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d2613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3973 (p : Pattern) (guard : d2614 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d2613 p = 1 := by simpa only [d2614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3972 p hg
    simpa only [d2614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d2614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3974 (p : Pattern) (guard : d62765 p = 1) : d47700 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2481 p hg
    simpa only [d62765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2614 p = 1 := by simpa only [d62765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3973 p hg
    simpa only [d62765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3975 (p : Pattern) (guard : d62766 p = 1) : d47768 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 49 with
  | false =>
    have hg : d62765 p = 1 := by simpa only [d62766, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3974 p hg
    simpa only [d62766, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62766, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2528 p hg
    simpa only [d62766, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3976 (p : Pattern) (guard : d62767 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 48 with
  | false =>
    have hg : d62766 p = 1 := by simpa only [d62767, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3975 p hg
    simpa only [d62767, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62767, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2530 p hg
    simpa only [d62767, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3977 (p : Pattern) (guard : d62768 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62767 p = 1 := by simpa only [d62768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3976 p hg
    simpa only [d62768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3978 (p : Pattern) (guard : d62769 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62768 p = 1 := by simpa only [d62769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3977 p hg
    simpa only [d62769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3979 (p : Pattern) (guard : d62770 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62769 p = 1 := by simpa only [d62770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3978 p hg
    simpa only [d62770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3980 (p : Pattern) (guard : d62771 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62770 p = 1 := by simpa only [d62771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3979 p hg
    simpa only [d62771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3981 (p : Pattern) (guard : d62772 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62771 p = 1 := by simpa only [d62772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3980 p hg
    simpa only [d62772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3982 (p : Pattern) (guard : d62773 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62772 p = 1 := by simpa only [d62773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3981 p hg
    simpa only [d62773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3983 (p : Pattern) (guard : d62774 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62773 p = 1 := by simpa only [d62774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3982 p hg
    simpa only [d62774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3984 (p : Pattern) (guard : d62775 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62774 p = 1 := by simpa only [d62775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3983 p hg
    simpa only [d62775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3985 (p : Pattern) (guard : d62776 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62775 p = 1 := by simpa only [d62776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3984 p hg
    simpa only [d62776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3986 (p : Pattern) (guard : d62777 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d62777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62776 p = 1 := by simpa only [d62777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3985 p hg
    simpa only [d62777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3987 (p : Pattern) (guard : d62778 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 10250 with
  | false =>
    have hg : d62764 p = 1 := by simpa only [d62778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3969 p hg
    simpa only [d62778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d62777 p = 1 := by simpa only [d62778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3986 p hg
    simpa only [d62778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3988 (p : Pattern) (guard : d62779 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 260 with
  | false =>
    have hg : d62778 p = 1 := by simpa only [d62779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3987 p hg
    simpa only [d62779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3989 (p : Pattern) (guard : d62780 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 259 with
  | false =>
    have hg : d62779 p = 1 := by simpa only [d62780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3988 p hg
    simpa only [d62780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3990 (p : Pattern) (guard : d62781 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 258 with
  | false =>
    have hg : d62780 p = 1 := by simpa only [d62781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3989 p hg
    simpa only [d62781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3991 (p : Pattern) (guard : d62782 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 257 with
  | false =>
    have hg : d62781 p = 1 := by simpa only [d62782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3990 p hg
    simpa only [d62782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3992 (p : Pattern) (guard : d62783 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 256 with
  | false =>
    have hg : d62782 p = 1 := by simpa only [d62783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3991 p hg
    simpa only [d62783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3993 (p : Pattern) (guard : d62784 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 255 with
  | false =>
    have hg : d62783 p = 1 := by simpa only [d62784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3992 p hg
    simpa only [d62784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3994 (p : Pattern) (guard : d62785 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 254 with
  | false =>
    have hg : d62784 p = 1 := by simpa only [d62785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3993 p hg
    simpa only [d62785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3995 (p : Pattern) (guard : d62786 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 253 with
  | false =>
    have hg : d62785 p = 1 := by simpa only [d62786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3994 p hg
    simpa only [d62786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3996 (p : Pattern) (guard : d62787 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 252 with
  | false =>
    have hg : d62786 p = 1 := by simpa only [d62787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3995 p hg
    simpa only [d62787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3997 (p : Pattern) (guard : d62788 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 251 with
  | false =>
    have hg : d62787 p = 1 := by simpa only [d62788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3996 p hg
    simpa only [d62788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3998 (p : Pattern) (guard : d62789 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 250 with
  | false =>
    have hg : d62788 p = 1 := by simpa only [d62789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3997 p hg
    simpa only [d62789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3999 (p : Pattern) (guard : d62790 p = 1) : d47911 p ≤ (0 : Int) + d65730 p := by
  cases selected : p 249 with
  | false =>
    have hg : d62789 p = 1 := by simpa only [d62790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3998 p hg
    simpa only [d62790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2480 p hg
    simpa only [d62790, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
