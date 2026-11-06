import NetHack.Soko22Hazard87.Compare055
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare14000 (p : Pattern) (guard : d12494 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d12493 p = 1 := by simpa only [d12494, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13999 p hg
    simpa only [d12494, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d12494, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d12494, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14001 (p : Pattern) (guard : d12495 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d12494 p = 1 := by simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14000 p hg
    simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d28 p = 1 := by simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13673 p hg
    simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14002 (p : Pattern) (guard : d15966 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d323 p = 1 := by simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13998 p hg
    simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12495 p = 1 := by simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14001 p hg
    simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14003 (p : Pattern) (guard : d15967 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 157 with
  | false =>
    have hg : d15966 p = 1 := by simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14002 p hg
    simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d144 p = 1 := by simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13837 p hg
    simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14004 (p : Pattern) (guard : d15968 p = 1) : d48326 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15968, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13670 p hg
    simpa only [d15968, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15967 p = 1 := by simpa only [d15968, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14003 p hg
    simpa only [d15968, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14005 (p : Pattern) (guard : d15969 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15969, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13669 p hg
    simpa only [d15969, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15968 p = 1 := by simpa only [d15969, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14004 p hg
    simpa only [d15969, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14006 (p : Pattern) (guard : d15970 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d15969 p = 1 := by simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14005 p hg
    simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d147 p = 1 := by simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13840 p hg
    simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14007 (p : Pattern) (guard : d15971 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d15970 p = 1 := by simpa only [d15971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14006 p hg
    simpa only [d15971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d148 p = 1 := by simpa only [d15971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13841 p hg
    simpa only [d15971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14008 (p : Pattern) (guard : d15972 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d15971 p = 1 := by simpa only [d15972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14007 p hg
    simpa only [d15972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13680 p hg
    simpa only [d15972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14009 (p : Pattern) (guard : d15973 p = 1) : d48338 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d15972 p = 1 := by simpa only [d15973, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14008 p hg
    simpa only [d15973, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15973, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d15973, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14010 (p : Pattern) (guard : d15974 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15974, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d15974, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15973 p = 1 := by simpa only [d15974, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14009 p hg
    simpa only [d15974, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14011 (p : Pattern) (guard : d15975 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d15974 p = 1 := by simpa only [d15975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14010 p hg
    simpa only [d15975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d152 p = 1 := by simpa only [d15975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13845 p hg
    simpa only [d15975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14012 (p : Pattern) (guard : d15976 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d15975 p = 1 := by simpa only [d15976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14011 p hg
    simpa only [d15976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d15976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14013 (p : Pattern) (guard : d15977 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d15976 p = 1 := by simpa only [d15977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14012 p hg
    simpa only [d15977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d15977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14014 (p : Pattern) (guard : d15978 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d15978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15977 p = 1 := by simpa only [d15978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14013 p hg
    simpa only [d15978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14015 (p : Pattern) (guard : d15979 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d15978 p = 1 := by simpa only [d15979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14014 p hg
    simpa only [d15979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d156 p = 1 := by simpa only [d15979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13849 p hg
    simpa only [d15979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14016 (p : Pattern) (guard : d128191 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d15979 p = 1 := by simpa only [d128191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14015 p hg
    simpa only [d128191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d128191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14017 (p : Pattern) (guard : d4733 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d152 p = 1 := by simpa only [d4733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13845 p hg
    simpa only [d4733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d4733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14018 (p : Pattern) (guard : d4734 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d4733 p = 1 := by simpa only [d4734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14017 p hg
    simpa only [d4734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d4734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14019 (p : Pattern) (guard : d4735 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d4734 p = 1 := by simpa only [d4735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14018 p hg
    simpa only [d4735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d4735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14020 (p : Pattern) (guard : d4736 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d4736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4735 p = 1 := by simpa only [d4736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14019 p hg
    simpa only [d4736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14021 (p : Pattern) (guard : d4737 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d4736 p = 1 := by simpa only [d4737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14020 p hg
    simpa only [d4737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d4737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14022 (p : Pattern) (guard : d5350 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d4737 p = 1 := by simpa only [d5350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14021 p hg
    simpa only [d5350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d5350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14023 (p : Pattern) (guard : d128192 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128191 p = 1 := by simpa only [d128192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14016 p hg
    simpa only [d128192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5350 p = 1 := by simpa only [d128192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14022 p hg
    simpa only [d128192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14024 (p : Pattern) (guard : d128193 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d306 p = 1 := by simpa only [d128193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13995 p hg
    simpa only [d128193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128192 p = 1 := by simpa only [d128193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14023 p hg
    simpa only [d128193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14025 (p : Pattern) (guard : d128194 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d300 p = 1 := by simpa only [d128194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13989 p hg
    simpa only [d128194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128193 p = 1 := by simpa only [d128194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14024 p hg
    simpa only [d128194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14026 (p : Pattern) (guard : d128195 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128195, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d128195, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128194 p = 1 := by simpa only [d128195, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14025 p hg
    simpa only [d128195, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14027 (p : Pattern) (guard : d295 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d154 p = 1 := by simpa only [d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13875 p hg
    simpa only [d295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14028 (p : Pattern) (guard : d296 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295 p = 1 := by simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14027 p hg
    simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14029 (p : Pattern) (guard : d297 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d296 p = 1 := by simpa only [d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14028 p hg
    simpa only [d297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d116 p = 1 := by simpa only [d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13857 p hg
    simpa only [d297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14030 (p : Pattern) (guard : d298 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d297 p = 1 := by simpa only [d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14029 p hg
    simpa only [d298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14031 (p : Pattern) (guard : d299 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d298 p = 1 := by simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14030 p hg
    simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14032 (p : Pattern) (guard : d300 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d299 p = 1 := by simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14031 p hg
    simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14033 (p : Pattern) (guard : d301 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d153 p = 1 := by simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13874 p hg
    simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14034 (p : Pattern) (guard : d302 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d301 p = 1 := by simpa only [d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14033 p hg
    simpa only [d302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14035 (p : Pattern) (guard : d303 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d302 p = 1 := by simpa only [d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14034 p hg
    simpa only [d303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14036 (p : Pattern) (guard : d304 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d303 p = 1 := by simpa only [d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14035 p hg
    simpa only [d304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d123 p = 1 := by simpa only [d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13864 p hg
    simpa only [d304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14037 (p : Pattern) (guard : d305 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d304 p = 1 := by simpa only [d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14036 p hg
    simpa only [d305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14038 (p : Pattern) (guard : d306 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d305 p = 1 := by simpa only [d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14037 p hg
    simpa only [d306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14039 (p : Pattern) (guard : d15969 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15969, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13698 p hg
    simpa only [d15969, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15968 p = 1 := by simpa only [d15969, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14004 p hg
    simpa only [d15969, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14040 (p : Pattern) (guard : d15970 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d15969 p = 1 := by simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14039 p hg
    simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d147 p = 1 := by simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13868 p hg
    simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14041 (p : Pattern) (guard : d15971 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d15970 p = 1 := by simpa only [d15971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14040 p hg
    simpa only [d15971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d148 p = 1 := by simpa only [d15971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13869 p hg
    simpa only [d15971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14042 (p : Pattern) (guard : d15972 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d15971 p = 1 := by simpa only [d15972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14041 p hg
    simpa only [d15972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13700 p hg
    simpa only [d15972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14043 (p : Pattern) (guard : d15973 p = 1) : d48329 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d15972 p = 1 := by simpa only [d15973, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14042 p hg
    simpa only [d15973, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15973, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d15973, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14044 (p : Pattern) (guard : d15974 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15974, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13697 p hg
    simpa only [d15974, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15973 p = 1 := by simpa only [d15974, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14043 p hg
    simpa only [d15974, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14045 (p : Pattern) (guard : d15975 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d15974 p = 1 := by simpa only [d15975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14044 p hg
    simpa only [d15975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d152 p = 1 := by simpa only [d15975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13873 p hg
    simpa only [d15975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14046 (p : Pattern) (guard : d15976 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d15975 p = 1 := by simpa only [d15976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14045 p hg
    simpa only [d15976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d15976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14047 (p : Pattern) (guard : d15977 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d15976 p = 1 := by simpa only [d15977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14046 p hg
    simpa only [d15977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d15977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14048 (p : Pattern) (guard : d15978 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d15978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15977 p = 1 := by simpa only [d15978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14047 p hg
    simpa only [d15978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14049 (p : Pattern) (guard : d15979 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d15978 p = 1 := by simpa only [d15979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14048 p hg
    simpa only [d15979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d156 p = 1 := by simpa only [d15979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13877 p hg
    simpa only [d15979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14050 (p : Pattern) (guard : d128191 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d15979 p = 1 := by simpa only [d128191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14049 p hg
    simpa only [d128191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d128191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14051 (p : Pattern) (guard : d4733 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d152 p = 1 := by simpa only [d4733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13873 p hg
    simpa only [d4733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d4733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14052 (p : Pattern) (guard : d4734 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d4733 p = 1 := by simpa only [d4734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14051 p hg
    simpa only [d4734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d4734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14053 (p : Pattern) (guard : d4735 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d4734 p = 1 := by simpa only [d4735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14052 p hg
    simpa only [d4735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d4735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14054 (p : Pattern) (guard : d4736 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d4736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4735 p = 1 := by simpa only [d4736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14053 p hg
    simpa only [d4736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14055 (p : Pattern) (guard : d4737 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d4736 p = 1 := by simpa only [d4737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14054 p hg
    simpa only [d4737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d4737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14056 (p : Pattern) (guard : d5350 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d4737 p = 1 := by simpa only [d5350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14055 p hg
    simpa only [d5350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d5350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14057 (p : Pattern) (guard : d128192 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128191 p = 1 := by simpa only [d128192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14050 p hg
    simpa only [d128192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5350 p = 1 := by simpa only [d128192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14056 p hg
    simpa only [d128192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14058 (p : Pattern) (guard : d128193 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d306 p = 1 := by simpa only [d128193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14038 p hg
    simpa only [d128193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128192 p = 1 := by simpa only [d128193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14057 p hg
    simpa only [d128193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14059 (p : Pattern) (guard : d128194 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d300 p = 1 := by simpa only [d128194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14032 p hg
    simpa only [d128194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128193 p = 1 := by simpa only [d128194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14058 p hg
    simpa only [d128194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14060 (p : Pattern) (guard : d376 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295 p = 1 := by simpa only [d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13984 p hg
    simpa only [d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14061 (p : Pattern) (guard : d377 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d376 p = 1 := by simpa only [d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14060 p hg
    simpa only [d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d194 p = 1 := by simpa only [d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13883 p hg
    simpa only [d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14062 (p : Pattern) (guard : d378 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d377 p = 1 := by simpa only [d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14061 p hg
    simpa only [d378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14063 (p : Pattern) (guard : d379 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d378 p = 1 := by simpa only [d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14062 p hg
    simpa only [d379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14064 (p : Pattern) (guard : d380 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d379 p = 1 := by simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14063 p hg
    simpa only [d380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14065 (p : Pattern) (guard : d381 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d302 p = 1 := by simpa only [d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13991 p hg
    simpa only [d381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14066 (p : Pattern) (guard : d382 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d381 p = 1 := by simpa only [d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14065 p hg
    simpa only [d382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d199 p = 1 := by simpa only [d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13888 p hg
    simpa only [d382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14067 (p : Pattern) (guard : d383 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d382 p = 1 := by simpa only [d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14066 p hg
    simpa only [d383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14068 (p : Pattern) (guard : d384 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d383 p = 1 := by simpa only [d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14067 p hg
    simpa only [d384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14069 (p : Pattern) (guard : d15985 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d15977 p = 1 := by simpa only [d15985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14013 p hg
    simpa only [d15985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d15985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14070 (p : Pattern) (guard : d15986 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d15985 p = 1 := by simpa only [d15986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14069 p hg
    simpa only [d15986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d203 p = 1 := by simpa only [d15986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13892 p hg
    simpa only [d15986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14071 (p : Pattern) (guard : d128196 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d15986 p = 1 := by simpa only [d128196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14070 p hg
    simpa only [d128196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d128196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14072 (p : Pattern) (guard : d5355 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d4735 p = 1 := by simpa only [d5355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14019 p hg
    simpa only [d5355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d5355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14073 (p : Pattern) (guard : d5356 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d5355 p = 1 := by simpa only [d5356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14072 p hg
    simpa only [d5356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d5356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14074 (p : Pattern) (guard : d5357 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d5356 p = 1 := by simpa only [d5357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14073 p hg
    simpa only [d5357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d5357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14075 (p : Pattern) (guard : d128197 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128196 p = 1 := by simpa only [d128197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14071 p hg
    simpa only [d128197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5357 p = 1 := by simpa only [d128197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14074 p hg
    simpa only [d128197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14076 (p : Pattern) (guard : d128198 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d384 p = 1 := by simpa only [d128198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14068 p hg
    simpa only [d128198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128197 p = 1 := by simpa only [d128198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14075 p hg
    simpa only [d128198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14077 (p : Pattern) (guard : d128199 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d380 p = 1 := by simpa only [d128199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14064 p hg
    simpa only [d128199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128198 p = 1 := by simpa only [d128199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14076 p hg
    simpa only [d128199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14078 (p : Pattern) (guard : d128200 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d128194 p = 1 := by simpa only [d128200, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14059 p hg
    simpa only [d128200, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128199 p = 1 := by simpa only [d128200, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14077 p hg
    simpa only [d128200, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14079 (p : Pattern) (guard : d128201 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 70 with
  | false =>
    have hg : d128195 p = 1 := by simpa only [d128201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14026 p hg
    simpa only [d128201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128200 p = 1 := by simpa only [d128201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14078 p hg
    simpa only [d128201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14080 (p : Pattern) (guard : d397 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d283 p = 1 := by simpa only [d397, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13975 p hg
    simpa only [d397, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d103 p = 1 := by simpa only [d397, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13806 p hg
    simpa only [d397, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14081 (p : Pattern) (guard : d398 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 70 with
  | false =>
    have hg : d397 p = 1 := by simpa only [d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14080 p hg
    simpa only [d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d111 p = 1 := by simpa only [d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13818 p hg
    simpa only [d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14082 (p : Pattern) (guard : d128202 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 69 with
  | false =>
    have hg : d128201 p = 1 := by simpa only [d128202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14079 p hg
    simpa only [d128202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d398 p = 1 := by simpa only [d128202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14081 p hg
    simpa only [d128202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14083 (p : Pattern) (guard : d128203 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 51 with
  | false =>
    have hg : d128202 p = 1 := by simpa only [d128203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14082 p hg
    simpa only [d128203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13665 p hg
    simpa only [d128203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14084 (p : Pattern) (guard : d128204 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 50 with
  | false =>
    have hg : d294 p = 1 := by simpa only [d128204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13983 p hg
    simpa only [d128204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128203 p = 1 := by simpa only [d128204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14083 p hg
    simpa only [d128204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14085 (p : Pattern) (guard : d321 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare14086 (p : Pattern) (guard : d322 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d321 p = 1 := by simpa only [d322, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14085 p hg
    simpa only [d322, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d322, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d322, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14087 (p : Pattern) (guard : d323 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d322 p = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14086 p hg
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d142 p = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13906 p hg
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14088 (p : Pattern) (guard : d12493 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare14089 (p : Pattern) (guard : d12494 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d12493 p = 1 := by simpa only [d12494, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14088 p hg
    simpa only [d12494, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d12494, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d12494, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14090 (p : Pattern) (guard : d12495 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d12494 p = 1 := by simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14089 p hg
    simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d28 p = 1 := by simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13733 p hg
    simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14091 (p : Pattern) (guard : d15966 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d323 p = 1 := by simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14087 p hg
    simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12495 p = 1 := by simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14090 p hg
    simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14092 (p : Pattern) (guard : d15967 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 157 with
  | false =>
    have hg : d15966 p = 1 := by simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14091 p hg
    simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d144 p = 1 := by simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13908 p hg
    simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14093 (p : Pattern) (guard : d15968 p = 1) : d48346 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15968, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13730 p hg
    simpa only [d15968, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15967 p = 1 := by simpa only [d15968, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14092 p hg
    simpa only [d15968, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14094 (p : Pattern) (guard : d15969 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15969, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13729 p hg
    simpa only [d15969, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15968 p = 1 := by simpa only [d15969, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14093 p hg
    simpa only [d15969, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14095 (p : Pattern) (guard : d15970 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 136 with
  | false =>
    have hg : d15969 p = 1 := by simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14094 p hg
    simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d147 p = 1 := by simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13911 p hg
    simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14096 (p : Pattern) (guard : d15971 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 135 with
  | false =>
    have hg : d15970 p = 1 := by simpa only [d15971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14095 p hg
    simpa only [d15971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d148 p = 1 := by simpa only [d15971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13912 p hg
    simpa only [d15971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14097 (p : Pattern) (guard : d15972 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 119 with
  | false =>
    have hg : d15971 p = 1 := by simpa only [d15972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14096 p hg
    simpa only [d15972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13740 p hg
    simpa only [d15972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14098 (p : Pattern) (guard : d15973 p = 1) : d48356 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 116 with
  | false =>
    have hg : d15972 p = 1 := by simpa only [d15973, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14097 p hg
    simpa only [d15973, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15973, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13744 p hg
    simpa only [d15973, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14099 (p : Pattern) (guard : d15974 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15974, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13728 p hg
    simpa only [d15974, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15973 p = 1 := by simpa only [d15974, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14098 p hg
    simpa only [d15974, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14100 (p : Pattern) (guard : d15975 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 113 with
  | false =>
    have hg : d15974 p = 1 := by simpa only [d15975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14099 p hg
    simpa only [d15975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d152 p = 1 := by simpa only [d15975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13916 p hg
    simpa only [d15975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14101 (p : Pattern) (guard : d15976 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 96 with
  | false =>
    have hg : d15975 p = 1 := by simpa only [d15976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14100 p hg
    simpa only [d15976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d15976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14102 (p : Pattern) (guard : d15977 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 95 with
  | false =>
    have hg : d15976 p = 1 := by simpa only [d15977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14101 p hg
    simpa only [d15977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d15977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14103 (p : Pattern) (guard : d15985 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 93 with
  | false =>
    have hg : d15977 p = 1 := by simpa only [d15985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14102 p hg
    simpa only [d15985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d15985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14104 (p : Pattern) (guard : d15986 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 91 with
  | false =>
    have hg : d15985 p = 1 := by simpa only [d15986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14103 p hg
    simpa only [d15986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d203 p = 1 := by simpa only [d15986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13920 p hg
    simpa only [d15986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14105 (p : Pattern) (guard : d128196 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 90 with
  | false =>
    have hg : d15986 p = 1 := by simpa only [d128196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14104 p hg
    simpa only [d128196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d128196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14106 (p : Pattern) (guard : d4733 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 113 with
  | false =>
    have hg : d152 p = 1 := by simpa only [d4733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13916 p hg
    simpa only [d4733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d4733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14107 (p : Pattern) (guard : d4734 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 96 with
  | false =>
    have hg : d4733 p = 1 := by simpa only [d4734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14106 p hg
    simpa only [d4734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d4734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14108 (p : Pattern) (guard : d4735 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 95 with
  | false =>
    have hg : d4734 p = 1 := by simpa only [d4735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14107 p hg
    simpa only [d4735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d4735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14109 (p : Pattern) (guard : d5355 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 93 with
  | false =>
    have hg : d4735 p = 1 := by simpa only [d5355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14108 p hg
    simpa only [d5355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d5355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14110 (p : Pattern) (guard : d5356 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 91 with
  | false =>
    have hg : d5355 p = 1 := by simpa only [d5356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14109 p hg
    simpa only [d5356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d5356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14111 (p : Pattern) (guard : d5357 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 90 with
  | false =>
    have hg : d5356 p = 1 := by simpa only [d5357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14110 p hg
    simpa only [d5357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d5357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14112 (p : Pattern) (guard : d128197 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128196 p = 1 := by simpa only [d128197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14105 p hg
    simpa only [d128197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5357 p = 1 := by simpa only [d128197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14111 p hg
    simpa only [d128197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14113 (p : Pattern) (guard : d128205 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d128205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128197 p = 1 := by simpa only [d128205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14112 p hg
    simpa only [d128205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14114 (p : Pattern) (guard : d128206 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d128206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128205 p = 1 := by simpa only [d128206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14113 p hg
    simpa only [d128206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14115 (p : Pattern) (guard : d128207 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128207, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d128207, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128206 p = 1 := by simpa only [d128207, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14114 p hg
    simpa only [d128207, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14116 (p : Pattern) (guard : d128208 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13726 p hg
    simpa only [d128208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128207 p = 1 := by simpa only [d128208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14115 p hg
    simpa only [d128208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14117 (p : Pattern) (guard : d107 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d50 p = 1 := by simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13751 p hg
    simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14118 (p : Pattern) (guard : d108 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 89 with
  | false =>
    have hg : d107 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14117 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14119 (p : Pattern) (guard : d109 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d108 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14118 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14120 (p : Pattern) (guard : d110 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d109 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14119 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14121 (p : Pattern) (guard : d406 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d406, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d406, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d110 p = 1 := by simpa only [d406, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14120 p hg
    simpa only [d406, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14122 (p : Pattern) (guard : d407 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13726 p hg
    simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d406 p = 1 := by simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14121 p hg
    simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14123 (p : Pattern) (guard : d128209 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 69 with
  | false =>
    have hg : d128208 p = 1 := by simpa only [d128209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14116 p hg
    simpa only [d128209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d407 p = 1 := by simpa only [d128209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14122 p hg
    simpa only [d128209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14124 (p : Pattern) (guard : d128210 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 51 with
  | false =>
    have hg : d128209 p = 1 := by simpa only [d128210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14123 p hg
    simpa only [d128210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13726 p hg
    simpa only [d128210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14125 (p : Pattern) (guard : d128211 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 50 with
  | false =>
    have hg : d128210 p = 1 := by simpa only [d128211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14124 p hg
    simpa only [d128211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13726 p hg
    simpa only [d128211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14126 (p : Pattern) (guard : d128212 p = 1) : d48359 p ≤ (1 : Int) + d171289 p := by
  cases selected : p 49 with
  | false =>
    have hg : d128204 p = 1 := by simpa only [d128212, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14084 p hg
    simpa only [d128212, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128211 p = 1 := by simpa only [d128212, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14125 p hg
    simpa only [d128212, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14127 (p : Pattern) (guard : d414 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare14128 (p : Pattern) (guard : d415 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d414 p = 1 := by simpa only [d415, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14127 p hg
    simpa only [d415, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d415, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d415, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14129 (p : Pattern) (guard : d416 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d415 p = 1 := by simpa only [d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14128 p hg
    simpa only [d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d229 p = 1 := by simpa only [d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13933 p hg
    simpa only [d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14130 (p : Pattern) (guard : d12601 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare14131 (p : Pattern) (guard : d12602 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d12601 p = 1 := by simpa only [d12602, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14130 p hg
    simpa only [d12602, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d12602, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d12602, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14132 (p : Pattern) (guard : d12603 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d12602 p = 1 := by simpa only [d12603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14131 p hg
    simpa only [d12603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d69 p = 1 := by simpa only [d12603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13768 p hg
    simpa only [d12603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14133 (p : Pattern) (guard : d16004 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d416 p = 1 := by simpa only [d16004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14129 p hg
    simpa only [d16004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12603 p = 1 := by simpa only [d16004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14132 p hg
    simpa only [d16004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14134 (p : Pattern) (guard : d16005 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16004 p = 1 := by simpa only [d16005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14133 p hg
    simpa only [d16005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d231 p = 1 := by simpa only [d16005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13935 p hg
    simpa only [d16005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14135 (p : Pattern) (guard : d16006 p = 1) : d48362 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16006, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13765 p hg
    simpa only [d16006, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16005 p = 1 := by simpa only [d16006, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14134 p hg
    simpa only [d16006, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14136 (p : Pattern) (guard : d16007 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16007, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13764 p hg
    simpa only [d16007, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16006 p = 1 := by simpa only [d16007, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14135 p hg
    simpa only [d16007, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14137 (p : Pattern) (guard : d16008 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16007 p = 1 := by simpa only [d16008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14136 p hg
    simpa only [d16008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d234 p = 1 := by simpa only [d16008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13938 p hg
    simpa only [d16008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14138 (p : Pattern) (guard : d16009 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16008 p = 1 := by simpa only [d16009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14137 p hg
    simpa only [d16009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d235 p = 1 := by simpa only [d16009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13939 p hg
    simpa only [d16009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14139 (p : Pattern) (guard : d16010 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16009 p = 1 := by simpa only [d16010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14138 p hg
    simpa only [d16010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13775 p hg
    simpa only [d16010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14140 (p : Pattern) (guard : d16011 p = 1) : d48365 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16010 p = 1 := by simpa only [d16011, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14139 p hg
    simpa only [d16011, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16011, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13779 p hg
    simpa only [d16011, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14141 (p : Pattern) (guard : d16012 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16012, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d16012, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16011 p = 1 := by simpa only [d16012, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14140 p hg
    simpa only [d16012, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14142 (p : Pattern) (guard : d16013 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16012 p = 1 := by simpa only [d16013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14141 p hg
    simpa only [d16013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d239 p = 1 := by simpa only [d16013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13943 p hg
    simpa only [d16013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14143 (p : Pattern) (guard : d16014 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16013 p = 1 := by simpa only [d16014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14142 p hg
    simpa only [d16014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14144 (p : Pattern) (guard : d16015 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16014 p = 1 := by simpa only [d16015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14143 p hg
    simpa only [d16015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14145 (p : Pattern) (guard : d16016 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16015 p = 1 := by simpa only [d16016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14144 p hg
    simpa only [d16016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d16016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14146 (p : Pattern) (guard : d16017 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16016 p = 1 := by simpa only [d16017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14145 p hg
    simpa only [d16017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d243 p = 1 := by simpa only [d16017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13947 p hg
    simpa only [d16017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14147 (p : Pattern) (guard : d128213 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16017 p = 1 := by simpa only [d128213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14146 p hg
    simpa only [d128213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d128213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14148 (p : Pattern) (guard : d5374 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 113 with
  | false =>
    have hg : d239 p = 1 := by simpa only [d5374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13943 p hg
    simpa only [d5374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d5374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14149 (p : Pattern) (guard : d5375 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 96 with
  | false =>
    have hg : d5374 p = 1 := by simpa only [d5375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14148 p hg
    simpa only [d5375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d5375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14150 (p : Pattern) (guard : d5376 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 95 with
  | false =>
    have hg : d5375 p = 1 := by simpa only [d5376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14149 p hg
    simpa only [d5376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d5376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14151 (p : Pattern) (guard : d5377 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 93 with
  | false =>
    have hg : d5376 p = 1 := by simpa only [d5377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14150 p hg
    simpa only [d5377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d5377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14152 (p : Pattern) (guard : d5378 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 91 with
  | false =>
    have hg : d5377 p = 1 := by simpa only [d5378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14151 p hg
    simpa only [d5378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d5378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14153 (p : Pattern) (guard : d5379 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 90 with
  | false =>
    have hg : d5378 p = 1 := by simpa only [d5379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14152 p hg
    simpa only [d5379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d5379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14154 (p : Pattern) (guard : d128214 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128213 p = 1 := by simpa only [d128214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14147 p hg
    simpa only [d128214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5379 p = 1 := by simpa only [d128214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14153 p hg
    simpa only [d128214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14155 (p : Pattern) (guard : d128215 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d128215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128214 p = 1 := by simpa only [d128215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14154 p hg
    simpa only [d128215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14156 (p : Pattern) (guard : d128216 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d128216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128215 p = 1 := by simpa only [d128216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14155 p hg
    simpa only [d128216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14157 (p : Pattern) (guard : d128217 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128217, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d128217, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128216 p = 1 := by simpa only [d128217, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14156 p hg
    simpa only [d128217, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14158 (p : Pattern) (guard : d128218 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13762 p hg
    simpa only [d128218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128217 p = 1 := by simpa only [d128218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14157 p hg
    simpa only [d128218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14159 (p : Pattern) (guard : d458 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d84 p = 1 := by simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13786 p hg
    simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14160 (p : Pattern) (guard : d459 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 89 with
  | false =>
    have hg : d458 p = 1 := by simpa only [d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14159 p hg
    simpa only [d459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14161 (p : Pattern) (guard : d460 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d459 p = 1 := by simpa only [d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14160 p hg
    simpa only [d460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14162 (p : Pattern) (guard : d461 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d460 p = 1 := by simpa only [d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14161 p hg
    simpa only [d461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14163 (p : Pattern) (guard : d462 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d462, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d462, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d461 p = 1 := by simpa only [d462, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14162 p hg
    simpa only [d462, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14164 (p : Pattern) (guard : d463 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13762 p hg
    simpa only [d463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d462 p = 1 := by simpa only [d463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14163 p hg
    simpa only [d463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14165 (p : Pattern) (guard : d128219 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 69 with
  | false =>
    have hg : d128218 p = 1 := by simpa only [d128219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14158 p hg
    simpa only [d128219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d463 p = 1 := by simpa only [d128219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14164 p hg
    simpa only [d128219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14166 (p : Pattern) (guard : d128220 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 51 with
  | false =>
    have hg : d128219 p = 1 := by simpa only [d128220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14165 p hg
    simpa only [d128220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13762 p hg
    simpa only [d128220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14167 (p : Pattern) (guard : d128221 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 50 with
  | false =>
    have hg : d128220 p = 1 := by simpa only [d128221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14166 p hg
    simpa only [d128221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13762 p hg
    simpa only [d128221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14168 (p : Pattern) (guard : d128222 p = 1) : d48387 p ≤ (1 : Int) + d171294 p := by
  cases selected : p 49 with
  | false =>
    have hg : d128221 p = 1 := by simpa only [d128222, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14167 p hg
    simpa only [d128222, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128222, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13796 p hg
    simpa only [d128222, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14169 (p : Pattern) (guard : d128223 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 48 with
  | false =>
    have hg : d128212 p = 1 := by simpa only [d128223, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14126 p hg
    simpa only [d128223, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128222 p = 1 := by simpa only [d128223, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14168 p hg
    simpa only [d128223, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14170 (p : Pattern) (guard : d128224 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128223 p = 1 := by simpa only [d128224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14169 p hg
    simpa only [d128224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14171 (p : Pattern) (guard : d128225 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128224 p = 1 := by simpa only [d128225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14170 p hg
    simpa only [d128225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14172 (p : Pattern) (guard : d128226 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128225 p = 1 := by simpa only [d128226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14171 p hg
    simpa only [d128226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14173 (p : Pattern) (guard : d128227 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128226 p = 1 := by simpa only [d128227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14172 p hg
    simpa only [d128227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14174 (p : Pattern) (guard : d128228 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d128228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128227 p = 1 := by simpa only [d128228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14173 p hg
    simpa only [d128228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14175 (p : Pattern) (guard : d128229 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d51657 p = 1 := by simpa only [d128229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13964 p hg
    simpa only [d128229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128228 p = 1 := by simpa only [d128229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14174 p hg
    simpa only [d128229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14176 (p : Pattern) (guard : d475 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d147 p = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13840 p hg
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13680 p hg
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14177 (p : Pattern) (guard : d16035 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d15970 p = 1 := by simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14006 p hg
    simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d475 p = 1 := by simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14176 p hg
    simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14178 (p : Pattern) (guard : d16036 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16035 p = 1 := by simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14177 p hg
    simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13680 p hg
    simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14179 (p : Pattern) (guard : d16037 p = 1) : d48338 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16036 p = 1 := by simpa only [d16037, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14178 p hg
    simpa only [d16037, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16037, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d16037, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14180 (p : Pattern) (guard : d16038 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16038, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d16038, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16037 p = 1 := by simpa only [d16038, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14179 p hg
    simpa only [d16038, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14181 (p : Pattern) (guard : d480 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d475 p = 1 := by simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14176 p hg
    simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13680 p hg
    simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14182 (p : Pattern) (guard : d481 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d480 p = 1 := by simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14181 p hg
    simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13680 p hg
    simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14183 (p : Pattern) (guard : d482 p = 1) : d48338 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d481 p = 1 := by simpa only [d482, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14182 p hg
    simpa only [d482, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d482, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d482, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14184 (p : Pattern) (guard : d483 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d483, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d483, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d482 p = 1 := by simpa only [d483, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14183 p hg
    simpa only [d483, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14185 (p : Pattern) (guard : d16039 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16038 p = 1 := by simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14180 p hg
    simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d483 p = 1 := by simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14184 p hg
    simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14186 (p : Pattern) (guard : d16040 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16039 p = 1 := by simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14185 p hg
    simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14187 (p : Pattern) (guard : d16041 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16040 p = 1 := by simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14186 p hg
    simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14188 (p : Pattern) (guard : d16042 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16041 p = 1 := by simpa only [d16042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14187 p hg
    simpa only [d16042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14189 (p : Pattern) (guard : d488 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d483 p = 1 := by simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14184 p hg
    simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14190 (p : Pattern) (guard : d489 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d488 p = 1 := by simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14189 p hg
    simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14191 (p : Pattern) (guard : d490 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d489 p = 1 := by simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14190 p hg
    simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14192 (p : Pattern) (guard : d491 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d490 p = 1 := by simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14191 p hg
    simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14193 (p : Pattern) (guard : d16043 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16042 p = 1 := by simpa only [d16043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14188 p hg
    simpa only [d16043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d491 p = 1 := by simpa only [d16043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14192 p hg
    simpa only [d16043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14194 (p : Pattern) (guard : d16044 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16043 p = 1 := by simpa only [d16044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14193 p hg
    simpa only [d16044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14195 (p : Pattern) (guard : d16045 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16044 p = 1 := by simpa only [d16045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14194 p hg
    simpa only [d16045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14196 (p : Pattern) (guard : d16046 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16045 p = 1 := by simpa only [d16046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14195 p hg
    simpa only [d16046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14197 (p : Pattern) (guard : d16047 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16046 p = 1 := by simpa only [d16047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14196 p hg
    simpa only [d16047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14198 (p : Pattern) (guard : d16048 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16048, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16048, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16047 p = 1 := by simpa only [d16048, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14197 p hg
    simpa only [d16048, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14199 (p : Pattern) (guard : d16049 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13665 p hg
    simpa only [d16049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16048 p = 1 := by simpa only [d16049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14198 p hg
    simpa only [d16049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14200 (p : Pattern) (guard : d16050 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 69 with
  | false =>
    have hg : d16049 p = 1 := by simpa only [d16050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14199 p hg
    simpa only [d16050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13665 p hg
    simpa only [d16050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14201 (p : Pattern) (guard : d475 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d147 p = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13868 p hg
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13700 p hg
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14202 (p : Pattern) (guard : d16035 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d15970 p = 1 := by simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14040 p hg
    simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d475 p = 1 := by simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14201 p hg
    simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14203 (p : Pattern) (guard : d16036 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16035 p = 1 := by simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14202 p hg
    simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13700 p hg
    simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14204 (p : Pattern) (guard : d16037 p = 1) : d48329 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16036 p = 1 := by simpa only [d16037, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14203 p hg
    simpa only [d16037, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16037, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d16037, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14205 (p : Pattern) (guard : d16038 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16038, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13697 p hg
    simpa only [d16038, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16037 p = 1 := by simpa only [d16038, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14204 p hg
    simpa only [d16038, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14206 (p : Pattern) (guard : d480 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d475 p = 1 := by simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14201 p hg
    simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13700 p hg
    simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14207 (p : Pattern) (guard : d481 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d480 p = 1 := by simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14206 p hg
    simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13700 p hg
    simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14208 (p : Pattern) (guard : d482 p = 1) : d48329 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d481 p = 1 := by simpa only [d482, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14207 p hg
    simpa only [d482, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d482, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d482, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14209 (p : Pattern) (guard : d483 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d483, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13697 p hg
    simpa only [d483, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d482 p = 1 := by simpa only [d483, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14208 p hg
    simpa only [d483, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14210 (p : Pattern) (guard : d16039 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16038 p = 1 := by simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14205 p hg
    simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d483 p = 1 := by simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14209 p hg
    simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14211 (p : Pattern) (guard : d16040 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16039 p = 1 := by simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14210 p hg
    simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14212 (p : Pattern) (guard : d16041 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16040 p = 1 := by simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14211 p hg
    simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14213 (p : Pattern) (guard : d16042 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16041 p = 1 := by simpa only [d16042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14212 p hg
    simpa only [d16042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14214 (p : Pattern) (guard : d488 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d483 p = 1 := by simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14209 p hg
    simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14215 (p : Pattern) (guard : d489 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d488 p = 1 := by simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14214 p hg
    simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14216 (p : Pattern) (guard : d490 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d489 p = 1 := by simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14215 p hg
    simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14217 (p : Pattern) (guard : d491 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d490 p = 1 := by simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14216 p hg
    simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14218 (p : Pattern) (guard : d16043 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16042 p = 1 := by simpa only [d16043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14213 p hg
    simpa only [d16043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d491 p = 1 := by simpa only [d16043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14217 p hg
    simpa only [d16043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14219 (p : Pattern) (guard : d16044 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16043 p = 1 := by simpa only [d16044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14218 p hg
    simpa only [d16044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14220 (p : Pattern) (guard : d16045 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16044 p = 1 := by simpa only [d16045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14219 p hg
    simpa only [d16045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14221 (p : Pattern) (guard : d16046 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16045 p = 1 := by simpa only [d16046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14220 p hg
    simpa only [d16046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14222 (p : Pattern) (guard : d16047 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16046 p = 1 := by simpa only [d16047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14221 p hg
    simpa only [d16047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14223 (p : Pattern) (guard : d16051 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16041 p = 1 := by simpa only [d16051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14187 p hg
    simpa only [d16051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14224 (p : Pattern) (guard : d501 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d490 p = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14191 p hg
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14225 (p : Pattern) (guard : d16052 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16051 p = 1 := by simpa only [d16052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14223 p hg
    simpa only [d16052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d501 p = 1 := by simpa only [d16052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14224 p hg
    simpa only [d16052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14226 (p : Pattern) (guard : d16053 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16052 p = 1 := by simpa only [d16053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14225 p hg
    simpa only [d16053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14227 (p : Pattern) (guard : d16054 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16053 p = 1 := by simpa only [d16054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14226 p hg
    simpa only [d16054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14228 (p : Pattern) (guard : d16055 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16054 p = 1 := by simpa only [d16055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14227 p hg
    simpa only [d16055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14229 (p : Pattern) (guard : d16056 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16055 p = 1 := by simpa only [d16056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14228 p hg
    simpa only [d16056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14230 (p : Pattern) (guard : d16057 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d16047 p = 1 := by simpa only [d16057, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14222 p hg
    simpa only [d16057, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16056 p = 1 := by simpa only [d16057, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14229 p hg
    simpa only [d16057, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14231 (p : Pattern) (guard : d16058 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 70 with
  | false =>
    have hg : d16048 p = 1 := by simpa only [d16058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14198 p hg
    simpa only [d16058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16057 p = 1 := by simpa only [d16058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14230 p hg
    simpa only [d16058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14232 (p : Pattern) (guard : d16059 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 69 with
  | false =>
    have hg : d16058 p = 1 := by simpa only [d16059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14231 p hg
    simpa only [d16059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13665 p hg
    simpa only [d16059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14233 (p : Pattern) (guard : d16060 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 51 with
  | false =>
    have hg : d16050 p = 1 := by simpa only [d16060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14200 p hg
    simpa only [d16060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16059 p = 1 := by simpa only [d16060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14232 p hg
    simpa only [d16060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14234 (p : Pattern) (guard : d16061 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16040 p = 1 := by simpa only [d16061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14186 p hg
    simpa only [d16061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14235 (p : Pattern) (guard : d16062 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16061 p = 1 := by simpa only [d16062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14234 p hg
    simpa only [d16062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14236 (p : Pattern) (guard : d513 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d489 p = 1 := by simpa only [d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14190 p hg
    simpa only [d513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14237 (p : Pattern) (guard : d514 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d513 p = 1 := by simpa only [d514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14236 p hg
    simpa only [d514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14238 (p : Pattern) (guard : d16063 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16062 p = 1 := by simpa only [d16063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14235 p hg
    simpa only [d16063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d514 p = 1 := by simpa only [d16063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14237 p hg
    simpa only [d16063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14239 (p : Pattern) (guard : d16064 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16063 p = 1 := by simpa only [d16064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14238 p hg
    simpa only [d16064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14240 (p : Pattern) (guard : d16065 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16064 p = 1 := by simpa only [d16065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14239 p hg
    simpa only [d16065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14241 (p : Pattern) (guard : d16066 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16065 p = 1 := by simpa only [d16066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14240 p hg
    simpa only [d16066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14242 (p : Pattern) (guard : d16067 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16039 p = 1 := by simpa only [d16067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14185 p hg
    simpa only [d16067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14243 (p : Pattern) (guard : d16068 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16067 p = 1 := by simpa only [d16068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14242 p hg
    simpa only [d16068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14244 (p : Pattern) (guard : d16069 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16068 p = 1 := by simpa only [d16069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14243 p hg
    simpa only [d16069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14245 (p : Pattern) (guard : d522 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d488 p = 1 := by simpa only [d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14189 p hg
    simpa only [d522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14246 (p : Pattern) (guard : d523 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d522 p = 1 := by simpa only [d523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14245 p hg
    simpa only [d523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14247 (p : Pattern) (guard : d524 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d523 p = 1 := by simpa only [d524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14246 p hg
    simpa only [d524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14248 (p : Pattern) (guard : d16070 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16069 p = 1 := by simpa only [d16070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14244 p hg
    simpa only [d16070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d524 p = 1 := by simpa only [d16070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14247 p hg
    simpa only [d16070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare14249 (p : Pattern) (guard : d16071 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16070 p = 1 := by simpa only [d16071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14248 p hg
    simpa only [d16071, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
