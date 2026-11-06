import NetHack.Soko22Hazard87.Compare059
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare15000 (p : Pattern) (guard : d16498 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16463 p = 1 := by simpa only [d16498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14939 p hg
    simpa only [d16498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15001 (p : Pattern) (guard : d16499 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16498 p = 1 := by simpa only [d16499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15000 p hg
    simpa only [d16499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15002 (p : Pattern) (guard : d16500 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16499 p = 1 := by simpa only [d16500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15001 p hg
    simpa only [d16500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15003 (p : Pattern) (guard : d16501 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16467 p = 1 := by simpa only [d16501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14943 p hg
    simpa only [d16501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15004 (p : Pattern) (guard : d16502 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16501 p = 1 := by simpa only [d16502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15003 p hg
    simpa only [d16502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15005 (p : Pattern) (guard : d16503 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16502 p = 1 := by simpa only [d16503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15004 p hg
    simpa only [d16503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15006 (p : Pattern) (guard : d16504 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16500 p = 1 := by simpa only [d16504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15002 p hg
    simpa only [d16504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16503 p = 1 := by simpa only [d16504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15005 p hg
    simpa only [d16504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15007 (p : Pattern) (guard : d16505 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16504 p = 1 := by simpa only [d16505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15006 p hg
    simpa only [d16505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15008 (p : Pattern) (guard : d16506 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16505 p = 1 := by simpa only [d16506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15007 p hg
    simpa only [d16506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15009 (p : Pattern) (guard : d1212 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare15010 (p : Pattern) (guard : d1213 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1212 p = 1 := by simpa only [d1213, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15009 p hg
    simpa only [d1213, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1213, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d1213, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15011 (p : Pattern) (guard : d16507 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare15012 (p : Pattern) (guard : d16508 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16507 p = 1 := by simpa only [d16508, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15011 p hg
    simpa only [d16508, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16508, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d16508, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15013 (p : Pattern) (guard : d16509 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1213 p = 1 := by simpa only [d16509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15010 p hg
    simpa only [d16509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16508 p = 1 := by simpa only [d16509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15012 p hg
    simpa only [d16509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15014 (p : Pattern) (guard : d14836 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare15015 (p : Pattern) (guard : d14837 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14836 p = 1 := by simpa only [d14837, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15014 p hg
    simpa only [d14837, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14837, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d14837, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15016 (p : Pattern) (guard : d16510 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14837 p = 1 := by simpa only [d16510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15015 p hg
    simpa only [d16510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14759 p = 1 := by simpa only [d16510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14899 p hg
    simpa only [d16510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15017 (p : Pattern) (guard : d16511 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16509 p = 1 := by simpa only [d16511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15013 p hg
    simpa only [d16511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16510 p = 1 := by simpa only [d16511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15016 p hg
    simpa only [d16511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15018 (p : Pattern) (guard : d16512 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16511 p = 1 := by simpa only [d16512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15017 p hg
    simpa only [d16512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16442 p = 1 := by simpa only [d16512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14903 p hg
    simpa only [d16512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15019 (p : Pattern) (guard : d16513 p = 1) : d48326 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16513, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13670 p hg
    simpa only [d16513, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16512 p = 1 := by simpa only [d16513, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15018 p hg
    simpa only [d16513, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15020 (p : Pattern) (guard : d16514 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16514, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13669 p hg
    simpa only [d16514, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16513 p = 1 := by simpa only [d16514, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15019 p hg
    simpa only [d16514, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15021 (p : Pattern) (guard : d13022 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare15022 (p : Pattern) (guard : d13023 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d13022 p = 1 := by simpa only [d13023, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15021 p hg
    simpa only [d13023, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13023, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d13023, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15023 (p : Pattern) (guard : d16515 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d13023 p = 1 := by simpa only [d16515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15022 p hg
    simpa only [d16515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14764 p = 1 := by simpa only [d16515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14901 p hg
    simpa only [d16515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15024 (p : Pattern) (guard : d16516 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16515 p = 1 := by simpa only [d16516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15023 p hg
    simpa only [d16516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14765 p = 1 := by simpa only [d16516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14909 p hg
    simpa only [d16516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15025 (p : Pattern) (guard : d16517 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16442 p = 1 := by simpa only [d16517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14903 p hg
    simpa only [d16517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16516 p = 1 := by simpa only [d16517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15024 p hg
    simpa only [d16517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15026 (p : Pattern) (guard : d16518 p = 1) : d48326 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16518, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13670 p hg
    simpa only [d16518, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16517 p = 1 := by simpa only [d16518, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15025 p hg
    simpa only [d16518, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15027 (p : Pattern) (guard : d16519 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16519, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13669 p hg
    simpa only [d16519, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16518 p = 1 := by simpa only [d16519, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15026 p hg
    simpa only [d16519, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15028 (p : Pattern) (guard : d16520 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16514 p = 1 := by simpa only [d16520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15020 p hg
    simpa only [d16520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16519 p = 1 := by simpa only [d16520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15027 p hg
    simpa only [d16520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15029 (p : Pattern) (guard : d16521 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16520 p = 1 := by simpa only [d16521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15028 p hg
    simpa only [d16521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16450 p = 1 := by simpa only [d16521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14924 p hg
    simpa only [d16521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15030 (p : Pattern) (guard : d16522 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16521 p = 1 := by simpa only [d16522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15029 p hg
    simpa only [d16522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13680 p hg
    simpa only [d16522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15031 (p : Pattern) (guard : d16523 p = 1) : d48338 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16522 p = 1 := by simpa only [d16523, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15030 p hg
    simpa only [d16523, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16523, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d16523, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15032 (p : Pattern) (guard : d16524 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16524, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d16524, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16523 p = 1 := by simpa only [d16524, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15031 p hg
    simpa only [d16524, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15033 (p : Pattern) (guard : d16525 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16449 p = 1 := by simpa only [d16525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14923 p hg
    simpa only [d16525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13680 p hg
    simpa only [d16525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15034 (p : Pattern) (guard : d16526 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16450 p = 1 := by simpa only [d16526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14924 p hg
    simpa only [d16526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16525 p = 1 := by simpa only [d16526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15033 p hg
    simpa only [d16526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15035 (p : Pattern) (guard : d16527 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16526 p = 1 := by simpa only [d16527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15034 p hg
    simpa only [d16527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13680 p hg
    simpa only [d16527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15036 (p : Pattern) (guard : d16528 p = 1) : d48338 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16527 p = 1 := by simpa only [d16528, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15035 p hg
    simpa only [d16528, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16528, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d16528, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15037 (p : Pattern) (guard : d16529 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16529, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d16529, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16528 p = 1 := by simpa only [d16529, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15036 p hg
    simpa only [d16529, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15038 (p : Pattern) (guard : d16530 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16524 p = 1 := by simpa only [d16530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15032 p hg
    simpa only [d16530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16529 p = 1 := by simpa only [d16530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15037 p hg
    simpa only [d16530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15039 (p : Pattern) (guard : d16531 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16530 p = 1 := by simpa only [d16531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15038 p hg
    simpa only [d16531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15040 (p : Pattern) (guard : d16532 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16531 p = 1 := by simpa only [d16532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15039 p hg
    simpa only [d16532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15041 (p : Pattern) (guard : d16533 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16532 p = 1 := by simpa only [d16533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15040 p hg
    simpa only [d16533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15042 (p : Pattern) (guard : d16534 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16529 p = 1 := by simpa only [d16534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15037 p hg
    simpa only [d16534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16462 p = 1 := by simpa only [d16534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14938 p hg
    simpa only [d16534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15043 (p : Pattern) (guard : d16535 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16534 p = 1 := by simpa only [d16535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15042 p hg
    simpa only [d16535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15044 (p : Pattern) (guard : d16536 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16535 p = 1 := by simpa only [d16536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15043 p hg
    simpa only [d16536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15045 (p : Pattern) (guard : d16537 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16536 p = 1 := by simpa only [d16537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15044 p hg
    simpa only [d16537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15046 (p : Pattern) (guard : d16538 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16533 p = 1 := by simpa only [d16538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15041 p hg
    simpa only [d16538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16537 p = 1 := by simpa only [d16538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15045 p hg
    simpa only [d16538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15047 (p : Pattern) (guard : d128311 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16538 p = 1 := by simpa only [d128311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15046 p hg
    simpa only [d128311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d128311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15048 (p : Pattern) (guard : d12961 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1127 p = 1 := by simpa only [d12961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14925 p hg
    simpa only [d12961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d12961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13674 p hg
    simpa only [d12961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15049 (p : Pattern) (guard : d16574 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16443 p = 1 := by simpa only [d16574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14910 p hg
    simpa only [d16574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12961 p = 1 := by simpa only [d16574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15048 p hg
    simpa only [d16574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15050 (p : Pattern) (guard : d16575 p = 1) : d48326 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16575, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13670 p hg
    simpa only [d16575, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16574 p = 1 := by simpa only [d16575, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15049 p hg
    simpa only [d16575, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15051 (p : Pattern) (guard : d16576 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16576, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13669 p hg
    simpa only [d16576, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16575 p = 1 := by simpa only [d16576, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15050 p hg
    simpa only [d16576, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15052 (p : Pattern) (guard : d16577 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16576 p = 1 := by simpa only [d16577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15051 p hg
    simpa only [d16577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13680 p hg
    simpa only [d16577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15053 (p : Pattern) (guard : d16578 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16450 p = 1 := by simpa only [d16578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14924 p hg
    simpa only [d16578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16577 p = 1 := by simpa only [d16578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15052 p hg
    simpa only [d16578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15054 (p : Pattern) (guard : d16579 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16578 p = 1 := by simpa only [d16579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15053 p hg
    simpa only [d16579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13680 p hg
    simpa only [d16579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15055 (p : Pattern) (guard : d16580 p = 1) : d48338 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16579 p = 1 := by simpa only [d16580, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15054 p hg
    simpa only [d16580, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16580, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d16580, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15056 (p : Pattern) (guard : d16581 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16581, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d16581, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16580 p = 1 := by simpa only [d16581, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15055 p hg
    simpa only [d16581, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15057 (p : Pattern) (guard : d16582 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16581 p = 1 := by simpa only [d16582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15056 p hg
    simpa only [d16582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15058 (p : Pattern) (guard : d16583 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16582 p = 1 := by simpa only [d16583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15057 p hg
    simpa only [d16583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15059 (p : Pattern) (guard : d16584 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16583 p = 1 := by simpa only [d16584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15058 p hg
    simpa only [d16584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15060 (p : Pattern) (guard : d16585 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16584 p = 1 := by simpa only [d16585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15059 p hg
    simpa only [d16585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15061 (p : Pattern) (guard : d16586 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16585 p = 1 := by simpa only [d16586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15060 p hg
    simpa only [d16586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15062 (p : Pattern) (guard : d16587 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16586 p = 1 := by simpa only [d16587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15061 p hg
    simpa only [d16587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15063 (p : Pattern) (guard : d128312 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128311 p = 1 := by simpa only [d128312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15047 p hg
    simpa only [d128312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16587 p = 1 := by simpa only [d128312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15062 p hg
    simpa only [d128312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15064 (p : Pattern) (guard : d128313 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d16506 p = 1 := by simpa only [d128313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15008 p hg
    simpa only [d128313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128312 p = 1 := by simpa only [d128313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15063 p hg
    simpa only [d128313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15065 (p : Pattern) (guard : d128314 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d16497 p = 1 := by simpa only [d128314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14999 p hg
    simpa only [d128314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128313 p = 1 := by simpa only [d128314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15064 p hg
    simpa only [d128314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15066 (p : Pattern) (guard : d128315 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d128315, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d128315, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128314 p = 1 := by simpa only [d128315, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15065 p hg
    simpa only [d128315, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15067 (p : Pattern) (guard : d16490 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16464 p = 1 := by simpa only [d16490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14969 p hg
    simpa only [d16490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15068 (p : Pattern) (guard : d16491 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16490 p = 1 := by simpa only [d16491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15067 p hg
    simpa only [d16491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15069 (p : Pattern) (guard : d16492 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16468 p = 1 := by simpa only [d16492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14973 p hg
    simpa only [d16492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15070 (p : Pattern) (guard : d16493 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16492 p = 1 := by simpa only [d16493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15069 p hg
    simpa only [d16493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15071 (p : Pattern) (guard : d16494 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16491 p = 1 := by simpa only [d16494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15068 p hg
    simpa only [d16494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16493 p = 1 := by simpa only [d16494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15070 p hg
    simpa only [d16494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15072 (p : Pattern) (guard : d16495 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16494 p = 1 := by simpa only [d16495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15071 p hg
    simpa only [d16495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15073 (p : Pattern) (guard : d16496 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16495 p = 1 := by simpa only [d16496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15072 p hg
    simpa only [d16496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15074 (p : Pattern) (guard : d16497 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16496 p = 1 := by simpa only [d16497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15073 p hg
    simpa only [d16497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15075 (p : Pattern) (guard : d16498 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16463 p = 1 := by simpa only [d16498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14968 p hg
    simpa only [d16498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15076 (p : Pattern) (guard : d16499 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16498 p = 1 := by simpa only [d16499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15075 p hg
    simpa only [d16499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15077 (p : Pattern) (guard : d16500 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16499 p = 1 := by simpa only [d16500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15076 p hg
    simpa only [d16500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15078 (p : Pattern) (guard : d16501 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16467 p = 1 := by simpa only [d16501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14972 p hg
    simpa only [d16501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15079 (p : Pattern) (guard : d16502 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16501 p = 1 := by simpa only [d16502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15078 p hg
    simpa only [d16502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15080 (p : Pattern) (guard : d16503 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16502 p = 1 := by simpa only [d16503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15079 p hg
    simpa only [d16503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15081 (p : Pattern) (guard : d16504 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16500 p = 1 := by simpa only [d16504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15077 p hg
    simpa only [d16504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16503 p = 1 := by simpa only [d16504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15080 p hg
    simpa only [d16504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15082 (p : Pattern) (guard : d16505 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16504 p = 1 := by simpa only [d16505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15081 p hg
    simpa only [d16505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15083 (p : Pattern) (guard : d16506 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16505 p = 1 := by simpa only [d16506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15082 p hg
    simpa only [d16506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15084 (p : Pattern) (guard : d16514 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16514, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13698 p hg
    simpa only [d16514, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16513 p = 1 := by simpa only [d16514, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15019 p hg
    simpa only [d16514, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15085 (p : Pattern) (guard : d16519 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16519, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13698 p hg
    simpa only [d16519, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16518 p = 1 := by simpa only [d16519, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15026 p hg
    simpa only [d16519, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15086 (p : Pattern) (guard : d16520 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16514 p = 1 := by simpa only [d16520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15084 p hg
    simpa only [d16520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16519 p = 1 := by simpa only [d16520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15085 p hg
    simpa only [d16520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15087 (p : Pattern) (guard : d16521 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16520 p = 1 := by simpa only [d16521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15086 p hg
    simpa only [d16521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16450 p = 1 := by simpa only [d16521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14957 p hg
    simpa only [d16521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15088 (p : Pattern) (guard : d16522 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16521 p = 1 := by simpa only [d16522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15087 p hg
    simpa only [d16522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13700 p hg
    simpa only [d16522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15089 (p : Pattern) (guard : d16523 p = 1) : d48329 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16522 p = 1 := by simpa only [d16523, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15088 p hg
    simpa only [d16523, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16523, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d16523, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15090 (p : Pattern) (guard : d16524 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16524, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13697 p hg
    simpa only [d16524, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16523 p = 1 := by simpa only [d16524, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15089 p hg
    simpa only [d16524, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15091 (p : Pattern) (guard : d16525 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16449 p = 1 := by simpa only [d16525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14956 p hg
    simpa only [d16525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13700 p hg
    simpa only [d16525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15092 (p : Pattern) (guard : d16526 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16450 p = 1 := by simpa only [d16526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14957 p hg
    simpa only [d16526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16525 p = 1 := by simpa only [d16526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15091 p hg
    simpa only [d16526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15093 (p : Pattern) (guard : d16527 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16526 p = 1 := by simpa only [d16527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15092 p hg
    simpa only [d16527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13700 p hg
    simpa only [d16527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15094 (p : Pattern) (guard : d16528 p = 1) : d48329 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16527 p = 1 := by simpa only [d16528, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15093 p hg
    simpa only [d16528, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16528, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d16528, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15095 (p : Pattern) (guard : d16529 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16529, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13697 p hg
    simpa only [d16529, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16528 p = 1 := by simpa only [d16529, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15094 p hg
    simpa only [d16529, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15096 (p : Pattern) (guard : d16530 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16524 p = 1 := by simpa only [d16530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15090 p hg
    simpa only [d16530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16529 p = 1 := by simpa only [d16530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15095 p hg
    simpa only [d16530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15097 (p : Pattern) (guard : d16531 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16530 p = 1 := by simpa only [d16531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15096 p hg
    simpa only [d16531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15098 (p : Pattern) (guard : d16532 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16531 p = 1 := by simpa only [d16532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15097 p hg
    simpa only [d16532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15099 (p : Pattern) (guard : d16533 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16532 p = 1 := by simpa only [d16533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15098 p hg
    simpa only [d16533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15100 (p : Pattern) (guard : d16534 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16529 p = 1 := by simpa only [d16534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15095 p hg
    simpa only [d16534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16462 p = 1 := by simpa only [d16534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14967 p hg
    simpa only [d16534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15101 (p : Pattern) (guard : d16535 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16534 p = 1 := by simpa only [d16535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15100 p hg
    simpa only [d16535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15102 (p : Pattern) (guard : d16536 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16535 p = 1 := by simpa only [d16536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15101 p hg
    simpa only [d16536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15103 (p : Pattern) (guard : d16537 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16536 p = 1 := by simpa only [d16537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15102 p hg
    simpa only [d16537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15104 (p : Pattern) (guard : d16538 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16533 p = 1 := by simpa only [d16538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15099 p hg
    simpa only [d16538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16537 p = 1 := by simpa only [d16538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15103 p hg
    simpa only [d16538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15105 (p : Pattern) (guard : d128311 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16538 p = 1 := by simpa only [d128311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15104 p hg
    simpa only [d128311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d128311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15106 (p : Pattern) (guard : d16576 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16576, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13698 p hg
    simpa only [d16576, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16575 p = 1 := by simpa only [d16576, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15050 p hg
    simpa only [d16576, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15107 (p : Pattern) (guard : d16577 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16576 p = 1 := by simpa only [d16577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15106 p hg
    simpa only [d16577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13700 p hg
    simpa only [d16577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15108 (p : Pattern) (guard : d16578 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16450 p = 1 := by simpa only [d16578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14957 p hg
    simpa only [d16578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16577 p = 1 := by simpa only [d16578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15107 p hg
    simpa only [d16578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15109 (p : Pattern) (guard : d16579 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16578 p = 1 := by simpa only [d16579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15108 p hg
    simpa only [d16579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13700 p hg
    simpa only [d16579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15110 (p : Pattern) (guard : d16580 p = 1) : d48329 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16579 p = 1 := by simpa only [d16580, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15109 p hg
    simpa only [d16580, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16580, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d16580, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15111 (p : Pattern) (guard : d16581 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16581, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13697 p hg
    simpa only [d16581, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16580 p = 1 := by simpa only [d16581, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15110 p hg
    simpa only [d16581, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15112 (p : Pattern) (guard : d16582 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16581 p = 1 := by simpa only [d16582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15111 p hg
    simpa only [d16582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15113 (p : Pattern) (guard : d16583 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16582 p = 1 := by simpa only [d16583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15112 p hg
    simpa only [d16583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15114 (p : Pattern) (guard : d16584 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16583 p = 1 := by simpa only [d16584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15113 p hg
    simpa only [d16584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15115 (p : Pattern) (guard : d16585 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16584 p = 1 := by simpa only [d16585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15114 p hg
    simpa only [d16585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15116 (p : Pattern) (guard : d16586 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16585 p = 1 := by simpa only [d16586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15115 p hg
    simpa only [d16586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15117 (p : Pattern) (guard : d16587 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16586 p = 1 := by simpa only [d16587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15116 p hg
    simpa only [d16587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15118 (p : Pattern) (guard : d128312 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128311 p = 1 := by simpa only [d128312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15105 p hg
    simpa only [d128312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16587 p = 1 := by simpa only [d128312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15117 p hg
    simpa only [d128312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15119 (p : Pattern) (guard : d128313 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d16506 p = 1 := by simpa only [d128313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15083 p hg
    simpa only [d128313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128312 p = 1 := by simpa only [d128313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15118 p hg
    simpa only [d128313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15120 (p : Pattern) (guard : d128314 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d16497 p = 1 := by simpa only [d128314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15074 p hg
    simpa only [d128314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128313 p = 1 := by simpa only [d128314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15119 p hg
    simpa only [d128314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15121 (p : Pattern) (guard : d16592 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16490 p = 1 := by simpa only [d16592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14992 p hg
    simpa only [d16592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15122 (p : Pattern) (guard : d16593 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16492 p = 1 := by simpa only [d16593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14994 p hg
    simpa only [d16593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15123 (p : Pattern) (guard : d16594 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16592 p = 1 := by simpa only [d16594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15121 p hg
    simpa only [d16594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16593 p = 1 := by simpa only [d16594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15122 p hg
    simpa only [d16594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15124 (p : Pattern) (guard : d16595 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16594 p = 1 := by simpa only [d16595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15123 p hg
    simpa only [d16595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15125 (p : Pattern) (guard : d16596 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16595 p = 1 := by simpa only [d16596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15124 p hg
    simpa only [d16596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15126 (p : Pattern) (guard : d16597 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16596 p = 1 := by simpa only [d16597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15125 p hg
    simpa only [d16597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15127 (p : Pattern) (guard : d16598 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16499 p = 1 := by simpa only [d16598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15001 p hg
    simpa only [d16598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15128 (p : Pattern) (guard : d16599 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16502 p = 1 := by simpa only [d16599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15004 p hg
    simpa only [d16599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15129 (p : Pattern) (guard : d16600 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16598 p = 1 := by simpa only [d16600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15127 p hg
    simpa only [d16600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16599 p = 1 := by simpa only [d16600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15128 p hg
    simpa only [d16600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15130 (p : Pattern) (guard : d16601 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16600 p = 1 := by simpa only [d16601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15129 p hg
    simpa only [d16601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15131 (p : Pattern) (guard : d16602 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16601 p = 1 := by simpa only [d16602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15130 p hg
    simpa only [d16602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15132 (p : Pattern) (guard : d16603 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16532 p = 1 := by simpa only [d16603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15040 p hg
    simpa only [d16603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15133 (p : Pattern) (guard : d16604 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16536 p = 1 := by simpa only [d16604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15044 p hg
    simpa only [d16604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15134 (p : Pattern) (guard : d16605 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16603 p = 1 := by simpa only [d16605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15132 p hg
    simpa only [d16605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16604 p = 1 := by simpa only [d16605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15133 p hg
    simpa only [d16605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15135 (p : Pattern) (guard : d128316 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16605 p = 1 := by simpa only [d128316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15134 p hg
    simpa only [d128316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d128316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15136 (p : Pattern) (guard : d16610 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16584 p = 1 := by simpa only [d16610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15059 p hg
    simpa only [d16610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15137 (p : Pattern) (guard : d16611 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16610 p = 1 := by simpa only [d16611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15136 p hg
    simpa only [d16611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15138 (p : Pattern) (guard : d16612 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d16611 p = 1 := by simpa only [d16612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15137 p hg
    simpa only [d16612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15139 (p : Pattern) (guard : d128317 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d128316 p = 1 := by simpa only [d128317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15135 p hg
    simpa only [d128317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16612 p = 1 := by simpa only [d128317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15138 p hg
    simpa only [d128317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15140 (p : Pattern) (guard : d128318 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d16602 p = 1 := by simpa only [d128318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15131 p hg
    simpa only [d128318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128317 p = 1 := by simpa only [d128318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15139 p hg
    simpa only [d128318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15141 (p : Pattern) (guard : d128319 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d16597 p = 1 := by simpa only [d128319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15126 p hg
    simpa only [d128319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128318 p = 1 := by simpa only [d128319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15140 p hg
    simpa only [d128319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15142 (p : Pattern) (guard : d128320 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d128314 p = 1 := by simpa only [d128320, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15120 p hg
    simpa only [d128320, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128319 p = 1 := by simpa only [d128320, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15141 p hg
    simpa only [d128320, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15143 (p : Pattern) (guard : d128321 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 70 with
  | false =>
    have hg : d128315 p = 1 := by simpa only [d128321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15066 p hg
    simpa only [d128321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128320 p = 1 := by simpa only [d128321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15142 p hg
    simpa only [d128321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15144 (p : Pattern) (guard : d16618 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16537 p = 1 := by simpa only [d16618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15103 p hg
    simpa only [d16618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16470 p = 1 := by simpa only [d16618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14975 p hg
    simpa only [d16618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15145 (p : Pattern) (guard : d16619 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16618 p = 1 := by simpa only [d16619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15144 p hg
    simpa only [d16619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15146 (p : Pattern) (guard : d16620 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16619 p = 1 := by simpa only [d16620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15145 p hg
    simpa only [d16620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15147 (p : Pattern) (guard : d16621 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16620 p = 1 := by simpa only [d16621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15146 p hg
    simpa only [d16621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15148 (p : Pattern) (guard : d16622 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16621 p = 1 := by simpa only [d16622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15147 p hg
    simpa only [d16622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15149 (p : Pattern) (guard : d16623 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16470 p = 1 := by simpa only [d16623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14946 p hg
    simpa only [d16623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15150 (p : Pattern) (guard : d16624 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16623 p = 1 := by simpa only [d16624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15149 p hg
    simpa only [d16624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15151 (p : Pattern) (guard : d16625 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16624 p = 1 := by simpa only [d16625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15150 p hg
    simpa only [d16625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15152 (p : Pattern) (guard : d16626 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16625 p = 1 := by simpa only [d16626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15151 p hg
    simpa only [d16626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15153 (p : Pattern) (guard : d16627 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16626 p = 1 := by simpa only [d16627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15152 p hg
    simpa only [d16627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15154 (p : Pattern) (guard : d16628 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d16622 p = 1 := by simpa only [d16628, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15148 p hg
    simpa only [d16628, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16627 p = 1 := by simpa only [d16628, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15153 p hg
    simpa only [d16628, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15155 (p : Pattern) (guard : d16623 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16470 p = 1 := by simpa only [d16623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14975 p hg
    simpa only [d16623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15156 (p : Pattern) (guard : d16624 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16623 p = 1 := by simpa only [d16624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15155 p hg
    simpa only [d16624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15157 (p : Pattern) (guard : d16625 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16624 p = 1 := by simpa only [d16625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15156 p hg
    simpa only [d16625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15158 (p : Pattern) (guard : d16626 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16625 p = 1 := by simpa only [d16626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15157 p hg
    simpa only [d16626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15159 (p : Pattern) (guard : d16627 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d16627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16626 p = 1 := by simpa only [d16627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15158 p hg
    simpa only [d16627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15160 (p : Pattern) (guard : d16629 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16480 p = 1 := by simpa only [d16629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14982 p hg
    simpa only [d16629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15161 (p : Pattern) (guard : d16630 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16629 p = 1 := by simpa only [d16630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15160 p hg
    simpa only [d16630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15162 (p : Pattern) (guard : d16631 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16630 p = 1 := by simpa only [d16631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15161 p hg
    simpa only [d16631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15163 (p : Pattern) (guard : d16632 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16631 p = 1 := by simpa only [d16632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15162 p hg
    simpa only [d16632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15164 (p : Pattern) (guard : d16633 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d16633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16632 p = 1 := by simpa only [d16633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15163 p hg
    simpa only [d16633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15165 (p : Pattern) (guard : d16634 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d16627 p = 1 := by simpa only [d16634, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15159 p hg
    simpa only [d16634, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16633 p = 1 := by simpa only [d16634, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15164 p hg
    simpa only [d16634, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15166 (p : Pattern) (guard : d16635 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 70 with
  | false =>
    have hg : d16628 p = 1 := by simpa only [d16635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15154 p hg
    simpa only [d16635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16634 p = 1 := by simpa only [d16635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15165 p hg
    simpa only [d16635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15167 (p : Pattern) (guard : d128322 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 69 with
  | false =>
    have hg : d128321 p = 1 := by simpa only [d128322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15143 p hg
    simpa only [d128322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16635 p = 1 := by simpa only [d128322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15166 p hg
    simpa only [d128322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15168 (p : Pattern) (guard : d128323 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 51 with
  | false =>
    have hg : d128322 p = 1 := by simpa only [d128323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15167 p hg
    simpa only [d128323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d128323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13665 p hg
    simpa only [d128323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15169 (p : Pattern) (guard : d128324 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 50 with
  | false =>
    have hg : d16489 p = 1 := by simpa only [d128324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14991 p hg
    simpa only [d128324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d128323 p = 1 := by simpa only [d128324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15168 p hg
    simpa only [d128324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15170 (p : Pattern) (guard : d1212 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare15171 (p : Pattern) (guard : d1213 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1212 p = 1 := by simpa only [d1213, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15170 p hg
    simpa only [d1213, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1213, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d1213, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15172 (p : Pattern) (guard : d16507 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare15173 (p : Pattern) (guard : d16508 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16507 p = 1 := by simpa only [d16508, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15172 p hg
    simpa only [d16508, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16508, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d16508, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15174 (p : Pattern) (guard : d16509 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1213 p = 1 := by simpa only [d16509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15171 p hg
    simpa only [d16509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16508 p = 1 := by simpa only [d16509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15173 p hg
    simpa only [d16509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15175 (p : Pattern) (guard : d14836 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare15176 (p : Pattern) (guard : d14837 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14836 p = 1 := by simpa only [d14837, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15175 p hg
    simpa only [d14837, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14837, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d14837, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15177 (p : Pattern) (guard : d14758 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare15178 (p : Pattern) (guard : d14759 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14758 p = 1 := by simpa only [d14759, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15177 p hg
    simpa only [d14759, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14759, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d14759, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15179 (p : Pattern) (guard : d16510 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14837 p = 1 := by simpa only [d16510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15176 p hg
    simpa only [d16510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14759 p = 1 := by simpa only [d16510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15178 p hg
    simpa only [d16510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15180 (p : Pattern) (guard : d16511 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16509 p = 1 := by simpa only [d16511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15174 p hg
    simpa only [d16511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16510 p = 1 := by simpa only [d16511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15179 p hg
    simpa only [d16511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15181 (p : Pattern) (guard : d1102 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare15182 (p : Pattern) (guard : d1103 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1102 p = 1 := by simpa only [d1103, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15181 p hg
    simpa only [d1103, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1103, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d1103, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15183 (p : Pattern) (guard : d16438 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare15184 (p : Pattern) (guard : d16439 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16438 p = 1 := by simpa only [d16439, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15183 p hg
    simpa only [d16439, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16439, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d16439, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15185 (p : Pattern) (guard : d16440 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1103 p = 1 := by simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15182 p hg
    simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16439 p = 1 := by simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15184 p hg
    simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15186 (p : Pattern) (guard : d14763 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare15187 (p : Pattern) (guard : d14764 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14763 p = 1 := by simpa only [d14764, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15186 p hg
    simpa only [d14764, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14764, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d14764, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15188 (p : Pattern) (guard : d16441 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14759 p = 1 := by simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15178 p hg
    simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14764 p = 1 := by simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15187 p hg
    simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15189 (p : Pattern) (guard : d16442 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16440 p = 1 := by simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15185 p hg
    simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16441 p = 1 := by simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15188 p hg
    simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15190 (p : Pattern) (guard : d16512 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16511 p = 1 := by simpa only [d16512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15180 p hg
    simpa only [d16512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16442 p = 1 := by simpa only [d16512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15189 p hg
    simpa only [d16512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15191 (p : Pattern) (guard : d16513 p = 1) : d48346 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16513, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13730 p hg
    simpa only [d16513, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16512 p = 1 := by simpa only [d16513, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15190 p hg
    simpa only [d16513, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15192 (p : Pattern) (guard : d16514 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16514, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13729 p hg
    simpa only [d16514, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16513 p = 1 := by simpa only [d16514, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15191 p hg
    simpa only [d16514, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15193 (p : Pattern) (guard : d13022 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare15194 (p : Pattern) (guard : d13023 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d13022 p = 1 := by simpa only [d13023, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15193 p hg
    simpa only [d13023, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13023, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d13023, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15195 (p : Pattern) (guard : d16515 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d13023 p = 1 := by simpa only [d16515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15194 p hg
    simpa only [d16515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14764 p = 1 := by simpa only [d16515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15187 p hg
    simpa only [d16515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15196 (p : Pattern) (guard : d14765 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14764 p = 1 := by simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15187 p hg
    simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13734 p hg
    simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15197 (p : Pattern) (guard : d16516 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16515 p = 1 := by simpa only [d16516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15195 p hg
    simpa only [d16516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14765 p = 1 := by simpa only [d16516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15196 p hg
    simpa only [d16516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15198 (p : Pattern) (guard : d16517 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16442 p = 1 := by simpa only [d16517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15189 p hg
    simpa only [d16517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16516 p = 1 := by simpa only [d16517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15197 p hg
    simpa only [d16517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15199 (p : Pattern) (guard : d16518 p = 1) : d48346 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16518, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13730 p hg
    simpa only [d16518, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16517 p = 1 := by simpa only [d16518, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15198 p hg
    simpa only [d16518, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15200 (p : Pattern) (guard : d16519 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16519, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13729 p hg
    simpa only [d16519, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16518 p = 1 := by simpa only [d16519, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15199 p hg
    simpa only [d16519, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15201 (p : Pattern) (guard : d16520 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16514 p = 1 := by simpa only [d16520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15192 p hg
    simpa only [d16520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16519 p = 1 := by simpa only [d16520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15200 p hg
    simpa only [d16520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15202 (p : Pattern) (guard : d1112 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare15203 (p : Pattern) (guard : d1113 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1112 p = 1 := by simpa only [d1113, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15202 p hg
    simpa only [d1113, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1113, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d1113, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15204 (p : Pattern) (guard : d1123 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare15205 (p : Pattern) (guard : d1124 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1123 p = 1 := by simpa only [d1124, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15204 p hg
    simpa only [d1124, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1124, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d1124, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15206 (p : Pattern) (guard : d1125 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1113 p = 1 := by simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15203 p hg
    simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1124 p = 1 := by simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15205 p hg
    simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15207 (p : Pattern) (guard : d16443 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1125 p = 1 := by simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15206 p hg
    simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14765 p = 1 := by simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15196 p hg
    simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15208 (p : Pattern) (guard : d16444 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16442 p = 1 := by simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15189 p hg
    simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16443 p = 1 := by simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15207 p hg
    simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15209 (p : Pattern) (guard : d16445 p = 1) : d48346 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16445, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13730 p hg
    simpa only [d16445, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16444 p = 1 := by simpa only [d16445, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15208 p hg
    simpa only [d16445, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15210 (p : Pattern) (guard : d16446 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16446, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13729 p hg
    simpa only [d16446, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16445 p = 1 := by simpa only [d16446, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15209 p hg
    simpa only [d16446, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15211 (p : Pattern) (guard : d5020 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare15212 (p : Pattern) (guard : d5021 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5020 p = 1 := by simpa only [d5021, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15211 p hg
    simpa only [d5021, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5021, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d5021, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15213 (p : Pattern) (guard : d5022 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d5021 p = 1 := by simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15212 p hg
    simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13734 p hg
    simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15214 (p : Pattern) (guard : d14770 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare15215 (p : Pattern) (guard : d14771 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14770 p = 1 := by simpa only [d14771, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15214 p hg
    simpa only [d14771, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14771, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d14771, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15216 (p : Pattern) (guard : d14772 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14771 p = 1 := by simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15215 p hg
    simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13734 p hg
    simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15217 (p : Pattern) (guard : d14773 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d5022 p = 1 := by simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15213 p hg
    simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14772 p = 1 := by simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15216 p hg
    simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15218 (p : Pattern) (guard : d16447 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16443 p = 1 := by simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15207 p hg
    simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14773 p = 1 := by simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15217 p hg
    simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15219 (p : Pattern) (guard : d16448 p = 1) : d48346 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16448, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13730 p hg
    simpa only [d16448, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16447 p = 1 := by simpa only [d16448, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15218 p hg
    simpa only [d16448, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15220 (p : Pattern) (guard : d16449 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16449, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13729 p hg
    simpa only [d16449, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16448 p = 1 := by simpa only [d16449, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15219 p hg
    simpa only [d16449, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15221 (p : Pattern) (guard : d16450 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16446 p = 1 := by simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15210 p hg
    simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16449 p = 1 := by simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15220 p hg
    simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15222 (p : Pattern) (guard : d16521 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16520 p = 1 := by simpa only [d16521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15201 p hg
    simpa only [d16521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16450 p = 1 := by simpa only [d16521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15221 p hg
    simpa only [d16521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15223 (p : Pattern) (guard : d16522 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16521 p = 1 := by simpa only [d16522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15222 p hg
    simpa only [d16522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13740 p hg
    simpa only [d16522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15224 (p : Pattern) (guard : d16523 p = 1) : d48356 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16522 p = 1 := by simpa only [d16523, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15223 p hg
    simpa only [d16523, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16523, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13744 p hg
    simpa only [d16523, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15225 (p : Pattern) (guard : d16524 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16524, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13728 p hg
    simpa only [d16524, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16523 p = 1 := by simpa only [d16524, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15224 p hg
    simpa only [d16524, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15226 (p : Pattern) (guard : d16525 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16449 p = 1 := by simpa only [d16525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15220 p hg
    simpa only [d16525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13740 p hg
    simpa only [d16525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15227 (p : Pattern) (guard : d16526 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16450 p = 1 := by simpa only [d16526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15221 p hg
    simpa only [d16526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16525 p = 1 := by simpa only [d16526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15226 p hg
    simpa only [d16526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15228 (p : Pattern) (guard : d16527 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16526 p = 1 := by simpa only [d16527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15227 p hg
    simpa only [d16527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13740 p hg
    simpa only [d16527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15229 (p : Pattern) (guard : d16528 p = 1) : d48356 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16527 p = 1 := by simpa only [d16528, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15228 p hg
    simpa only [d16528, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16528, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13744 p hg
    simpa only [d16528, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15230 (p : Pattern) (guard : d16529 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16529, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13728 p hg
    simpa only [d16529, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16528 p = 1 := by simpa only [d16529, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15229 p hg
    simpa only [d16529, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15231 (p : Pattern) (guard : d16530 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16524 p = 1 := by simpa only [d16530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15225 p hg
    simpa only [d16530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16529 p = 1 := by simpa only [d16530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15230 p hg
    simpa only [d16530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15232 (p : Pattern) (guard : d16531 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16530 p = 1 := by simpa only [d16531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15231 p hg
    simpa only [d16531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15233 (p : Pattern) (guard : d16532 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16531 p = 1 := by simpa only [d16532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15232 p hg
    simpa only [d16532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15234 (p : Pattern) (guard : d16603 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16532 p = 1 := by simpa only [d16603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15233 p hg
    simpa only [d16603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15235 (p : Pattern) (guard : d1127 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1124 p = 1 := by simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15205 p hg
    simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13734 p hg
    simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15236 (p : Pattern) (guard : d14778 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1127 p = 1 := by simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15235 p hg
    simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14772 p = 1 := by simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15216 p hg
    simpa only [d14778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15237 (p : Pattern) (guard : d16451 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16443 p = 1 := by simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15207 p hg
    simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14778 p = 1 := by simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15236 p hg
    simpa only [d16451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15238 (p : Pattern) (guard : d16452 p = 1) : d48346 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16452, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13730 p hg
    simpa only [d16452, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16451 p = 1 := by simpa only [d16452, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15237 p hg
    simpa only [d16452, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15239 (p : Pattern) (guard : d16453 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16453, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13729 p hg
    simpa only [d16453, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16452 p = 1 := by simpa only [d16453, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15238 p hg
    simpa only [d16453, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15240 (p : Pattern) (guard : d16454 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16453 p = 1 := by simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15239 p hg
    simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13740 p hg
    simpa only [d16454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15241 (p : Pattern) (guard : d16459 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16454 p = 1 := by simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15240 p hg
    simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13740 p hg
    simpa only [d16459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15242 (p : Pattern) (guard : d16460 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16459 p = 1 := by simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15241 p hg
    simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13740 p hg
    simpa only [d16460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15243 (p : Pattern) (guard : d16461 p = 1) : d48356 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16460 p = 1 := by simpa only [d16461, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15242 p hg
    simpa only [d16461, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16461, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13744 p hg
    simpa only [d16461, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15244 (p : Pattern) (guard : d16462 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16462, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13728 p hg
    simpa only [d16462, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16461 p = 1 := by simpa only [d16462, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15243 p hg
    simpa only [d16462, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15245 (p : Pattern) (guard : d16534 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16529 p = 1 := by simpa only [d16534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15230 p hg
    simpa only [d16534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16462 p = 1 := by simpa only [d16534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15244 p hg
    simpa only [d16534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15246 (p : Pattern) (guard : d16535 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16534 p = 1 := by simpa only [d16535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15245 p hg
    simpa only [d16535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15247 (p : Pattern) (guard : d16536 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16535 p = 1 := by simpa only [d16536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15246 p hg
    simpa only [d16536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15248 (p : Pattern) (guard : d16604 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16536 p = 1 := by simpa only [d16604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15247 p hg
    simpa only [d16604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d16604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15249 (p : Pattern) (guard : d16605 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16603 p = 1 := by simpa only [d16605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15234 p hg
    simpa only [d16605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16604 p = 1 := by simpa only [d16605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15248 p hg
    simpa only [d16605, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
