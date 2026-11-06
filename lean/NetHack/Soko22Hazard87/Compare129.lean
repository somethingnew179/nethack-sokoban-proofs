import NetHack.Soko22Hazard87.Compare128
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare32250 (p : Pattern) (guard : d294630 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294604 p = 1 := by simpa only [d294630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32199 p hg
    simpa only [d294630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32251 (p : Pattern) (guard : d294631 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294630 p = 1 := by simpa only [d294631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32250 p hg
    simpa only [d294631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32252 (p : Pattern) (guard : d294632 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294608 p = 1 := by simpa only [d294632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32203 p hg
    simpa only [d294632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32253 (p : Pattern) (guard : d294633 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294632 p = 1 := by simpa only [d294633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32252 p hg
    simpa only [d294633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32254 (p : Pattern) (guard : d294634 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294631 p = 1 := by simpa only [d294634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32251 p hg
    simpa only [d294634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294633 p = 1 := by simpa only [d294634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32253 p hg
    simpa only [d294634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32255 (p : Pattern) (guard : d294635 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294634 p = 1 := by simpa only [d294635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32254 p hg
    simpa only [d294635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32256 (p : Pattern) (guard : d294636 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294635 p = 1 := by simpa only [d294636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32255 p hg
    simpa only [d294636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32257 (p : Pattern) (guard : d294637 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294636 p = 1 := by simpa only [d294637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32256 p hg
    simpa only [d294637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32258 (p : Pattern) (guard : d294638 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294603 p = 1 := by simpa only [d294638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32198 p hg
    simpa only [d294638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32259 (p : Pattern) (guard : d294639 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294638 p = 1 := by simpa only [d294639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32258 p hg
    simpa only [d294639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32260 (p : Pattern) (guard : d294640 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294639 p = 1 := by simpa only [d294640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32259 p hg
    simpa only [d294640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32261 (p : Pattern) (guard : d294641 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294607 p = 1 := by simpa only [d294641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32202 p hg
    simpa only [d294641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32262 (p : Pattern) (guard : d294642 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294641 p = 1 := by simpa only [d294642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32261 p hg
    simpa only [d294642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32263 (p : Pattern) (guard : d294643 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294642 p = 1 := by simpa only [d294643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32262 p hg
    simpa only [d294643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32264 (p : Pattern) (guard : d294644 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294640 p = 1 := by simpa only [d294644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32260 p hg
    simpa only [d294644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294643 p = 1 := by simpa only [d294644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32263 p hg
    simpa only [d294644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32265 (p : Pattern) (guard : d294645 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294644 p = 1 := by simpa only [d294645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32264 p hg
    simpa only [d294645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32266 (p : Pattern) (guard : d294646 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294645 p = 1 := by simpa only [d294646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32265 p hg
    simpa only [d294646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32267 (p : Pattern) (guard : d131 p = 1) : d47617 p ≤ (1 : Int) + d47617 p := by
  omega
theorem compare32268 (p : Pattern) (guard : d25432 p = 1) : d49795 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d131 p = 1 := by simpa only [d25432, d49795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32267 p hg
    simpa only [d25432, d49795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25432, d49795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31976 p hg
    simpa only [d25432, d49795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32269 (p : Pattern) (guard : d25433 p = 1) : d49795 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d25432 p = 1 := by simpa only [d25433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32268 p hg
    simpa only [d25433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31974 p hg
    simpa only [d25433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32270 (p : Pattern) (guard : d25434 p = 1) : d49795 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d25433 p = 1 := by simpa only [d25434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32269 p hg
    simpa only [d25434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31974 p hg
    simpa only [d25434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32271 (p : Pattern) (guard : d205998 p = 1) : d49795 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d205998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31974 p hg
    simpa only [d205998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d25434 p = 1 := by simpa only [d205998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32270 p hg
    simpa only [d205998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32272 (p : Pattern) (guard : d294647 p = 1) : d49795 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31974 p hg
    simpa only [d294647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d205998 p = 1 := by simpa only [d294647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32271 p hg
    simpa only [d294647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32273 (p : Pattern) (guard : d294648 p = 1) : d49797 p ≤ (1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d294647 p = 1 := by simpa only [d294648, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32272 p hg
    simpa only [d294648, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294648, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31982 p hg
    simpa only [d294648, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32274 (p : Pattern) (guard : d294649 p = 1) : d49797 p ≤ (1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d294648 p = 1 := by simpa only [d294649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32273 p hg
    simpa only [d294649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31984 p hg
    simpa only [d294649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32275 (p : Pattern) (guard : d294650 p = 1) : d49838 p ≤ (1 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d294649 p = 1 := by simpa only [d294650, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32274 p hg
    simpa only [d294650, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294650, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31986 p hg
    simpa only [d294650, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32276 (p : Pattern) (guard : d294651 p = 1) : d49841 p ≤ (1 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d294650 p = 1 := by simpa only [d294651, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32275 p hg
    simpa only [d294651, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294651, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31988 p hg
    simpa only [d294651, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32277 (p : Pattern) (guard : d294652 p = 1) : d49864 p ≤ (1 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294652, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31973 p hg
    simpa only [d294652, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294651 p = 1 := by simpa only [d294652, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32276 p hg
    simpa only [d294652, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32278 (p : Pattern) (guard : d294653 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d294652 p = 1 := by simpa only [d294653, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32277 p hg
    simpa only [d294653, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294653, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31991 p hg
    simpa only [d294653, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32279 (p : Pattern) (guard : d294654 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31972 p hg
    simpa only [d294654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294653 p = 1 := by simpa only [d294654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32278 p hg
    simpa only [d294654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32280 (p : Pattern) (guard : d294655 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294654 p = 1 := by simpa only [d294655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32279 p hg
    simpa only [d294655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31972 p hg
    simpa only [d294655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32281 (p : Pattern) (guard : d294656 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d294655 p = 1 := by simpa only [d294656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32280 p hg
    simpa only [d294656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294585 p = 1 := by simpa only [d294656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32178 p hg
    simpa only [d294656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32282 (p : Pattern) (guard : d294657 p = 1) : d49869 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294657, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31971 p hg
    simpa only [d294657, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294656 p = 1 := by simpa only [d294657, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32281 p hg
    simpa only [d294657, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32283 (p : Pattern) (guard : d294658 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294658, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31970 p hg
    simpa only [d294658, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294657 p = 1 := by simpa only [d294658, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32282 p hg
    simpa only [d294658, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32284 (p : Pattern) (guard : d294659 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d294658 p = 1 := by simpa only [d294659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32283 p hg
    simpa only [d294659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294589 p = 1 := by simpa only [d294659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32183 p hg
    simpa only [d294659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32285 (p : Pattern) (guard : d294660 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d294659 p = 1 := by simpa only [d294660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32284 p hg
    simpa only [d294660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294593 p = 1 := by simpa only [d294660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32188 p hg
    simpa only [d294660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32286 (p : Pattern) (guard : d294661 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d294660 p = 1 := by simpa only [d294661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32285 p hg
    simpa only [d294661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31998 p hg
    simpa only [d294661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32287 (p : Pattern) (guard : d294662 p = 1) : d49914 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d294661 p = 1 := by simpa only [d294662, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32286 p hg
    simpa only [d294662, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294662, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32002 p hg
    simpa only [d294662, d49914, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32288 (p : Pattern) (guard : d294663 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294663, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31969 p hg
    simpa only [d294663, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294662 p = 1 := by simpa only [d294663, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32287 p hg
    simpa only [d294663, d49915, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32289 (p : Pattern) (guard : d294664 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294663 p = 1 := by simpa only [d294664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32288 p hg
    simpa only [d294664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294598 p = 1 := by simpa only [d294664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32193 p hg
    simpa only [d294664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32290 (p : Pattern) (guard : d294665 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294664 p = 1 := by simpa only [d294665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32289 p hg
    simpa only [d294665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32291 (p : Pattern) (guard : d294666 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294665 p = 1 := by simpa only [d294666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32290 p hg
    simpa only [d294666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32292 (p : Pattern) (guard : d294667 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294666 p = 1 := by simpa only [d294667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32291 p hg
    simpa only [d294667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32293 (p : Pattern) (guard : d294668 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294667 p = 1 := by simpa only [d294668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32292 p hg
    simpa only [d294668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294606 p = 1 := by simpa only [d294668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32201 p hg
    simpa only [d294668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32294 (p : Pattern) (guard : d294669 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d294668 p = 1 := by simpa only [d294669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32293 p hg
    simpa only [d294669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32295 (p : Pattern) (guard : d294670 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294598 p = 1 := by simpa only [d294670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32193 p hg
    simpa only [d294670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32296 (p : Pattern) (guard : d294671 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294670 p = 1 := by simpa only [d294671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32295 p hg
    simpa only [d294671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32297 (p : Pattern) (guard : d294672 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294671 p = 1 := by simpa only [d294672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32296 p hg
    simpa only [d294672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32298 (p : Pattern) (guard : d294673 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294672 p = 1 := by simpa only [d294673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32297 p hg
    simpa only [d294673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32299 (p : Pattern) (guard : d294674 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294673 p = 1 := by simpa only [d294674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32298 p hg
    simpa only [d294674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32300 (p : Pattern) (guard : d294675 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d294674 p = 1 := by simpa only [d294675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32299 p hg
    simpa only [d294675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32301 (p : Pattern) (guard : d294676 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294669 p = 1 := by simpa only [d294676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32294 p hg
    simpa only [d294676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294675 p = 1 := by simpa only [d294676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32300 p hg
    simpa only [d294676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32302 (p : Pattern) (guard : d294677 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d294646 p = 1 := by simpa only [d294677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32266 p hg
    simpa only [d294677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294676 p = 1 := by simpa only [d294677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32301 p hg
    simpa only [d294677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32303 (p : Pattern) (guard : d294678 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d294637 p = 1 := by simpa only [d294678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32257 p hg
    simpa only [d294678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294677 p = 1 := by simpa only [d294678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32302 p hg
    simpa only [d294678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32304 (p : Pattern) (guard : d294679 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294679, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294679, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294678 p = 1 := by simpa only [d294679, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32303 p hg
    simpa only [d294679, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32305 (p : Pattern) (guard : d294630 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294604 p = 1 := by simpa only [d294630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32227 p hg
    simpa only [d294630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32306 (p : Pattern) (guard : d294631 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294630 p = 1 := by simpa only [d294631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32305 p hg
    simpa only [d294631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32307 (p : Pattern) (guard : d294632 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294608 p = 1 := by simpa only [d294632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32231 p hg
    simpa only [d294632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32308 (p : Pattern) (guard : d294633 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294632 p = 1 := by simpa only [d294633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32307 p hg
    simpa only [d294633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32309 (p : Pattern) (guard : d294634 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294631 p = 1 := by simpa only [d294634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32306 p hg
    simpa only [d294634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294633 p = 1 := by simpa only [d294634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32308 p hg
    simpa only [d294634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32310 (p : Pattern) (guard : d294635 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294634 p = 1 := by simpa only [d294635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32309 p hg
    simpa only [d294635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32311 (p : Pattern) (guard : d294636 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294635 p = 1 := by simpa only [d294636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32310 p hg
    simpa only [d294636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32312 (p : Pattern) (guard : d294637 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294636 p = 1 := by simpa only [d294637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32311 p hg
    simpa only [d294637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32313 (p : Pattern) (guard : d294638 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294603 p = 1 := by simpa only [d294638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32226 p hg
    simpa only [d294638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32314 (p : Pattern) (guard : d294639 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294638 p = 1 := by simpa only [d294639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32313 p hg
    simpa only [d294639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32315 (p : Pattern) (guard : d294640 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294639 p = 1 := by simpa only [d294640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32314 p hg
    simpa only [d294640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32316 (p : Pattern) (guard : d294641 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294607 p = 1 := by simpa only [d294641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32230 p hg
    simpa only [d294641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32317 (p : Pattern) (guard : d294642 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294641 p = 1 := by simpa only [d294642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32316 p hg
    simpa only [d294642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32318 (p : Pattern) (guard : d294643 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294642 p = 1 := by simpa only [d294643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32317 p hg
    simpa only [d294643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32319 (p : Pattern) (guard : d294644 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294640 p = 1 := by simpa only [d294644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32315 p hg
    simpa only [d294644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294643 p = 1 := by simpa only [d294644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32318 p hg
    simpa only [d294644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32320 (p : Pattern) (guard : d294645 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294644 p = 1 := by simpa only [d294645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32319 p hg
    simpa only [d294645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32321 (p : Pattern) (guard : d294646 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294645 p = 1 := by simpa only [d294646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32320 p hg
    simpa only [d294646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32322 (p : Pattern) (guard : d294658 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294658, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32016 p hg
    simpa only [d294658, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294657 p = 1 := by simpa only [d294658, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32282 p hg
    simpa only [d294658, d49892, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32323 (p : Pattern) (guard : d294659 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d294658 p = 1 := by simpa only [d294659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32322 p hg
    simpa only [d294659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294589 p = 1 := by simpa only [d294659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32214 p hg
    simpa only [d294659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32324 (p : Pattern) (guard : d294660 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d294659 p = 1 := by simpa only [d294660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32323 p hg
    simpa only [d294660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294593 p = 1 := by simpa only [d294660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32216 p hg
    simpa only [d294660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32325 (p : Pattern) (guard : d294661 p = 1) : d49892 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d294660 p = 1 := by simpa only [d294661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32324 p hg
    simpa only [d294661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32018 p hg
    simpa only [d294661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32326 (p : Pattern) (guard : d294662 p = 1) : d49894 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d294661 p = 1 := by simpa only [d294662, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32325 p hg
    simpa only [d294662, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294662, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32002 p hg
    simpa only [d294662, d49894, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32327 (p : Pattern) (guard : d294663 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294663, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32015 p hg
    simpa only [d294663, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294662 p = 1 := by simpa only [d294663, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32326 p hg
    simpa only [d294663, d49895, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32328 (p : Pattern) (guard : d294664 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294663 p = 1 := by simpa only [d294664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32327 p hg
    simpa only [d294664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294598 p = 1 := by simpa only [d294664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32221 p hg
    simpa only [d294664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32329 (p : Pattern) (guard : d294665 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294664 p = 1 := by simpa only [d294665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32328 p hg
    simpa only [d294665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32330 (p : Pattern) (guard : d294666 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294665 p = 1 := by simpa only [d294666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32329 p hg
    simpa only [d294666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32331 (p : Pattern) (guard : d294667 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294666 p = 1 := by simpa only [d294667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32330 p hg
    simpa only [d294667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32332 (p : Pattern) (guard : d294668 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294667 p = 1 := by simpa only [d294668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32331 p hg
    simpa only [d294668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294606 p = 1 := by simpa only [d294668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32229 p hg
    simpa only [d294668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32333 (p : Pattern) (guard : d294669 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d294668 p = 1 := by simpa only [d294669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32332 p hg
    simpa only [d294669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32334 (p : Pattern) (guard : d294670 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294598 p = 1 := by simpa only [d294670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32221 p hg
    simpa only [d294670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32335 (p : Pattern) (guard : d294671 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294670 p = 1 := by simpa only [d294671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32334 p hg
    simpa only [d294671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32336 (p : Pattern) (guard : d294672 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294671 p = 1 := by simpa only [d294672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32335 p hg
    simpa only [d294672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32337 (p : Pattern) (guard : d294673 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294672 p = 1 := by simpa only [d294673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32336 p hg
    simpa only [d294673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32338 (p : Pattern) (guard : d294674 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294673 p = 1 := by simpa only [d294674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32337 p hg
    simpa only [d294674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32339 (p : Pattern) (guard : d294675 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d294674 p = 1 := by simpa only [d294675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32338 p hg
    simpa only [d294675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32340 (p : Pattern) (guard : d294676 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294669 p = 1 := by simpa only [d294676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32333 p hg
    simpa only [d294676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294675 p = 1 := by simpa only [d294676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32339 p hg
    simpa only [d294676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32341 (p : Pattern) (guard : d294677 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d294646 p = 1 := by simpa only [d294677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32321 p hg
    simpa only [d294677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294676 p = 1 := by simpa only [d294677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32340 p hg
    simpa only [d294677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32342 (p : Pattern) (guard : d294678 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d294637 p = 1 := by simpa only [d294678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32312 p hg
    simpa only [d294678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294677 p = 1 := by simpa only [d294678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32341 p hg
    simpa only [d294678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32343 (p : Pattern) (guard : d294680 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d294630 p = 1 := by simpa only [d294680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32250 p hg
    simpa only [d294680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32344 (p : Pattern) (guard : d294681 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d294632 p = 1 := by simpa only [d294681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32252 p hg
    simpa only [d294681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32345 (p : Pattern) (guard : d294682 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294680 p = 1 := by simpa only [d294682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32343 p hg
    simpa only [d294682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294681 p = 1 := by simpa only [d294682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32344 p hg
    simpa only [d294682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32346 (p : Pattern) (guard : d294683 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294682 p = 1 := by simpa only [d294683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32345 p hg
    simpa only [d294683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32347 (p : Pattern) (guard : d294684 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294683 p = 1 := by simpa only [d294684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32346 p hg
    simpa only [d294684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32348 (p : Pattern) (guard : d294685 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294684 p = 1 := by simpa only [d294685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32347 p hg
    simpa only [d294685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32349 (p : Pattern) (guard : d294686 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d294639 p = 1 := by simpa only [d294686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32259 p hg
    simpa only [d294686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32350 (p : Pattern) (guard : d294687 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d294642 p = 1 := by simpa only [d294687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32262 p hg
    simpa only [d294687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32351 (p : Pattern) (guard : d294688 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294686 p = 1 := by simpa only [d294688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32349 p hg
    simpa only [d294688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294687 p = 1 := by simpa only [d294688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32350 p hg
    simpa only [d294688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32352 (p : Pattern) (guard : d294689 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294688 p = 1 := by simpa only [d294689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32351 p hg
    simpa only [d294689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32353 (p : Pattern) (guard : d294690 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294689 p = 1 := by simpa only [d294690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32352 p hg
    simpa only [d294690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32354 (p : Pattern) (guard : d294691 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d294666 p = 1 := by simpa only [d294691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32291 p hg
    simpa only [d294691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32355 (p : Pattern) (guard : d294692 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294691 p = 1 := by simpa only [d294692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32354 p hg
    simpa only [d294692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294619 p = 1 := by simpa only [d294692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32239 p hg
    simpa only [d294692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32356 (p : Pattern) (guard : d294693 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d294692 p = 1 := by simpa only [d294693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32355 p hg
    simpa only [d294693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32357 (p : Pattern) (guard : d294694 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d294672 p = 1 := by simpa only [d294694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32297 p hg
    simpa only [d294694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32358 (p : Pattern) (guard : d294695 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294694 p = 1 := by simpa only [d294695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32357 p hg
    simpa only [d294695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32359 (p : Pattern) (guard : d294696 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d294695 p = 1 := by simpa only [d294696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32358 p hg
    simpa only [d294696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32360 (p : Pattern) (guard : d294697 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294693 p = 1 := by simpa only [d294697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32356 p hg
    simpa only [d294697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294696 p = 1 := by simpa only [d294697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32359 p hg
    simpa only [d294697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32361 (p : Pattern) (guard : d294698 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d294690 p = 1 := by simpa only [d294698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32353 p hg
    simpa only [d294698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294697 p = 1 := by simpa only [d294698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32360 p hg
    simpa only [d294698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32362 (p : Pattern) (guard : d294699 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d294685 p = 1 := by simpa only [d294699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32348 p hg
    simpa only [d294699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294698 p = 1 := by simpa only [d294699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32361 p hg
    simpa only [d294699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32363 (p : Pattern) (guard : d294700 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d294678 p = 1 := by simpa only [d294700, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32342 p hg
    simpa only [d294700, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294699 p = 1 := by simpa only [d294700, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32362 p hg
    simpa only [d294700, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32364 (p : Pattern) (guard : d294701 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d294679 p = 1 := by simpa only [d294701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32304 p hg
    simpa only [d294701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294700 p = 1 := by simpa only [d294701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32363 p hg
    simpa only [d294701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32365 (p : Pattern) (guard : d294702 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294610 p = 1 := by simpa only [d294702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32205 p hg
    simpa only [d294702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32366 (p : Pattern) (guard : d294703 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294702 p = 1 := by simpa only [d294703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32365 p hg
    simpa only [d294703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32367 (p : Pattern) (guard : d294704 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294703 p = 1 := by simpa only [d294704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32366 p hg
    simpa only [d294704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32368 (p : Pattern) (guard : d294705 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294704 p = 1 := by simpa only [d294705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32367 p hg
    simpa only [d294705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32369 (p : Pattern) (guard : d294706 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294705 p = 1 := by simpa only [d294706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32368 p hg
    simpa only [d294706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32370 (p : Pattern) (guard : d294707 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d294615 p = 1 := by simpa only [d294707, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32238 p hg
    simpa only [d294707, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294706 p = 1 := by simpa only [d294707, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32369 p hg
    simpa only [d294707, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32371 (p : Pattern) (guard : d294702 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294610 p = 1 := by simpa only [d294702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32233 p hg
    simpa only [d294702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32372 (p : Pattern) (guard : d294703 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294702 p = 1 := by simpa only [d294703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32371 p hg
    simpa only [d294703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32373 (p : Pattern) (guard : d294704 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294703 p = 1 := by simpa only [d294704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32372 p hg
    simpa only [d294704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32374 (p : Pattern) (guard : d294705 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294704 p = 1 := by simpa only [d294705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32373 p hg
    simpa only [d294705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32375 (p : Pattern) (guard : d294706 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294705 p = 1 := by simpa only [d294706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32374 p hg
    simpa only [d294706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32376 (p : Pattern) (guard : d294708 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294620 p = 1 := by simpa only [d294708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32240 p hg
    simpa only [d294708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32377 (p : Pattern) (guard : d294709 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294708 p = 1 := by simpa only [d294709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32376 p hg
    simpa only [d294709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32378 (p : Pattern) (guard : d294710 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294709 p = 1 := by simpa only [d294710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32377 p hg
    simpa only [d294710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32379 (p : Pattern) (guard : d294711 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294710 p = 1 := by simpa only [d294711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32378 p hg
    simpa only [d294711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32380 (p : Pattern) (guard : d294712 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31968 p hg
    simpa only [d294712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294711 p = 1 := by simpa only [d294712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32379 p hg
    simpa only [d294712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32381 (p : Pattern) (guard : d294713 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d294706 p = 1 := by simpa only [d294713, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32375 p hg
    simpa only [d294713, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294712 p = 1 := by simpa only [d294713, d49916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32380 p hg
    simpa only [d294713, d49916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32382 (p : Pattern) (guard : d294714 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d294707 p = 1 := by simpa only [d294714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32370 p hg
    simpa only [d294714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294713 p = 1 := by simpa only [d294714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32381 p hg
    simpa only [d294714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32383 (p : Pattern) (guard : d294715 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d294701 p = 1 := by simpa only [d294715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32364 p hg
    simpa only [d294715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294714 p = 1 := by simpa only [d294715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32382 p hg
    simpa only [d294715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32384 (p : Pattern) (guard : d294716 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d294715 p = 1 := by simpa only [d294716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32383 p hg
    simpa only [d294716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31966 p hg
    simpa only [d294716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32385 (p : Pattern) (guard : d294717 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d294629 p = 1 := by simpa only [d294717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32249 p hg
    simpa only [d294717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294716 p = 1 := by simpa only [d294717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32384 p hg
    simpa only [d294717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32386 (p : Pattern) (guard : d131 p = 1) : d47706 p ≤ (1 : Int) + d47706 p := by
  omega
theorem compare32387 (p : Pattern) (guard : d25432 p = 1) : d49927 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d131 p = 1 := by simpa only [d25432, d49927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32386 p hg
    simpa only [d25432, d49927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25432, d49927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32053 p hg
    simpa only [d25432, d49927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32388 (p : Pattern) (guard : d25433 p = 1) : d49927 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d25432 p = 1 := by simpa only [d25433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32387 p hg
    simpa only [d25433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32051 p hg
    simpa only [d25433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32389 (p : Pattern) (guard : d25434 p = 1) : d49927 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d25433 p = 1 := by simpa only [d25434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32388 p hg
    simpa only [d25434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32051 p hg
    simpa only [d25434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32390 (p : Pattern) (guard : d205998 p = 1) : d49927 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d205998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32051 p hg
    simpa only [d205998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d25434 p = 1 := by simpa only [d205998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32389 p hg
    simpa only [d205998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32391 (p : Pattern) (guard : d294647 p = 1) : d49927 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32051 p hg
    simpa only [d294647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d205998 p = 1 := by simpa only [d294647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32390 p hg
    simpa only [d294647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32392 (p : Pattern) (guard : d294648 p = 1) : d49929 p ≤ (1 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d294647 p = 1 := by simpa only [d294648, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32391 p hg
    simpa only [d294648, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294648, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32059 p hg
    simpa only [d294648, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32393 (p : Pattern) (guard : d294649 p = 1) : d49929 p ≤ (1 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d294648 p = 1 := by simpa only [d294649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32392 p hg
    simpa only [d294649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32061 p hg
    simpa only [d294649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32394 (p : Pattern) (guard : d294650 p = 1) : d49957 p ≤ (1 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d294649 p = 1 := by simpa only [d294650, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32393 p hg
    simpa only [d294650, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294650, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32063 p hg
    simpa only [d294650, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32395 (p : Pattern) (guard : d294651 p = 1) : d49958 p ≤ (1 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d294650 p = 1 := by simpa only [d294651, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32394 p hg
    simpa only [d294651, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294651, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d294651, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32396 (p : Pattern) (guard : d294652 p = 1) : d49978 p ≤ (1 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294652, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32050 p hg
    simpa only [d294652, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294651 p = 1 := by simpa only [d294652, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32395 p hg
    simpa only [d294652, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32397 (p : Pattern) (guard : d294653 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d294652 p = 1 := by simpa only [d294653, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32396 p hg
    simpa only [d294653, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294653, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32068 p hg
    simpa only [d294653, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32398 (p : Pattern) (guard : d294654 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32049 p hg
    simpa only [d294654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294653 p = 1 := by simpa only [d294654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32397 p hg
    simpa only [d294654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32399 (p : Pattern) (guard : d294655 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294654 p = 1 := by simpa only [d294655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32398 p hg
    simpa only [d294655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32049 p hg
    simpa only [d294655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32400 (p : Pattern) (guard : d205892 p = 1) : d49927 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d29090 p = 1 := by simpa only [d205892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32057 p hg
    simpa only [d205892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32051 p hg
    simpa only [d205892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32401 (p : Pattern) (guard : d205893 p = 1) : d49929 p ≤ (1 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d205892 p = 1 := by simpa only [d205893, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32400 p hg
    simpa only [d205893, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205893, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32059 p hg
    simpa only [d205893, d49929, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32402 (p : Pattern) (guard : d205894 p = 1) : d49929 p ≤ (1 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d205893 p = 1 := by simpa only [d205894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32401 p hg
    simpa only [d205894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32061 p hg
    simpa only [d205894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32403 (p : Pattern) (guard : d205895 p = 1) : d49957 p ≤ (1 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d205894 p = 1 := by simpa only [d205895, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32402 p hg
    simpa only [d205895, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205895, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32063 p hg
    simpa only [d205895, d49957, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32404 (p : Pattern) (guard : d205896 p = 1) : d49958 p ≤ (1 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d205895 p = 1 := by simpa only [d205896, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32403 p hg
    simpa only [d205896, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205896, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d205896, d49958, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32405 (p : Pattern) (guard : d205897 p = 1) : d49978 p ≤ (1 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d205897, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32050 p hg
    simpa only [d205897, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d205896 p = 1 := by simpa only [d205897, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32404 p hg
    simpa only [d205897, d49978, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32406 (p : Pattern) (guard : d205898 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d205897 p = 1 := by simpa only [d205898, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32405 p hg
    simpa only [d205898, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205898, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32068 p hg
    simpa only [d205898, d49982, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32407 (p : Pattern) (guard : d294584 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32049 p hg
    simpa only [d294584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d205898 p = 1 := by simpa only [d294584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32406 p hg
    simpa only [d294584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32408 (p : Pattern) (guard : d294585 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294510 p = 1 := by simpa only [d294585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32070 p hg
    simpa only [d294585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294584 p = 1 := by simpa only [d294585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32407 p hg
    simpa only [d294585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32409 (p : Pattern) (guard : d294656 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d294655 p = 1 := by simpa only [d294656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32399 p hg
    simpa only [d294656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294585 p = 1 := by simpa only [d294656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32408 p hg
    simpa only [d294656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32410 (p : Pattern) (guard : d294657 p = 1) : d49983 p ≤ (1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294657, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32048 p hg
    simpa only [d294657, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294656 p = 1 := by simpa only [d294657, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32409 p hg
    simpa only [d294657, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32411 (p : Pattern) (guard : d294658 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294658, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32047 p hg
    simpa only [d294658, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294657 p = 1 := by simpa only [d294658, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32410 p hg
    simpa only [d294658, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32412 (p : Pattern) (guard : d205899 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d205898 p = 1 := by simpa only [d205899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32406 p hg
    simpa only [d205899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32049 p hg
    simpa only [d205899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32413 (p : Pattern) (guard : d294586 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294584 p = 1 := by simpa only [d294586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32407 p hg
    simpa only [d294586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d205899 p = 1 := by simpa only [d294586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32412 p hg
    simpa only [d294586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32414 (p : Pattern) (guard : d294587 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d294585 p = 1 := by simpa only [d294587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32408 p hg
    simpa only [d294587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294586 p = 1 := by simpa only [d294587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32413 p hg
    simpa only [d294587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32415 (p : Pattern) (guard : d294588 p = 1) : d49983 p ≤ (1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294588, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32048 p hg
    simpa only [d294588, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294587 p = 1 := by simpa only [d294588, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32414 p hg
    simpa only [d294588, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32416 (p : Pattern) (guard : d294589 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294589, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32047 p hg
    simpa only [d294589, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294588 p = 1 := by simpa only [d294589, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32415 p hg
    simpa only [d294589, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32417 (p : Pattern) (guard : d294659 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d294658 p = 1 := by simpa only [d294659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32411 p hg
    simpa only [d294659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294589 p = 1 := by simpa only [d294659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32416 p hg
    simpa only [d294659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32418 (p : Pattern) (guard : d205900 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d205899 p = 1 := by simpa only [d205900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32412 p hg
    simpa only [d205900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32049 p hg
    simpa only [d205900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32419 (p : Pattern) (guard : d294590 p = 1) : d49982 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d294586 p = 1 := by simpa only [d294590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32413 p hg
    simpa only [d294590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d205900 p = 1 := by simpa only [d294590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32418 p hg
    simpa only [d294590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32420 (p : Pattern) (guard : d294591 p = 1) : d49983 p ≤ (1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294591, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32048 p hg
    simpa only [d294591, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294590 p = 1 := by simpa only [d294591, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32419 p hg
    simpa only [d294591, d49983, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32421 (p : Pattern) (guard : d294592 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294592, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32047 p hg
    simpa only [d294592, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294591 p = 1 := by simpa only [d294592, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32420 p hg
    simpa only [d294592, d49997, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32422 (p : Pattern) (guard : d294593 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d294589 p = 1 := by simpa only [d294593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32416 p hg
    simpa only [d294593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294592 p = 1 := by simpa only [d294593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32421 p hg
    simpa only [d294593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32423 (p : Pattern) (guard : d294660 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d294659 p = 1 := by simpa only [d294660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32417 p hg
    simpa only [d294660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294593 p = 1 := by simpa only [d294660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32422 p hg
    simpa only [d294660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32424 (p : Pattern) (guard : d294661 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d294660 p = 1 := by simpa only [d294661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32423 p hg
    simpa only [d294661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32075 p hg
    simpa only [d294661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32425 (p : Pattern) (guard : d294662 p = 1) : d49999 p ≤ (1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d294661 p = 1 := by simpa only [d294662, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32424 p hg
    simpa only [d294662, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294662, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32079 p hg
    simpa only [d294662, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32426 (p : Pattern) (guard : d294663 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294663, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32046 p hg
    simpa only [d294663, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294662 p = 1 := by simpa only [d294663, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32425 p hg
    simpa only [d294663, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32427 (p : Pattern) (guard : d294594 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d294592 p = 1 := by simpa only [d294594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32421 p hg
    simpa only [d294594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32075 p hg
    simpa only [d294594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32428 (p : Pattern) (guard : d294595 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d294593 p = 1 := by simpa only [d294595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32422 p hg
    simpa only [d294595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294594 p = 1 := by simpa only [d294595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32427 p hg
    simpa only [d294595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32429 (p : Pattern) (guard : d294596 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d294595 p = 1 := by simpa only [d294596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32428 p hg
    simpa only [d294596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32075 p hg
    simpa only [d294596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32430 (p : Pattern) (guard : d294597 p = 1) : d49999 p ≤ (1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d294596 p = 1 := by simpa only [d294597, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32429 p hg
    simpa only [d294597, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294597, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32079 p hg
    simpa only [d294597, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32431 (p : Pattern) (guard : d294598 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294598, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32046 p hg
    simpa only [d294598, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294597 p = 1 := by simpa only [d294598, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32430 p hg
    simpa only [d294598, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32432 (p : Pattern) (guard : d294664 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294663 p = 1 := by simpa only [d294664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32426 p hg
    simpa only [d294664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294598 p = 1 := by simpa only [d294664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32431 p hg
    simpa only [d294664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32433 (p : Pattern) (guard : d294665 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294664 p = 1 := by simpa only [d294665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32432 p hg
    simpa only [d294665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32434 (p : Pattern) (guard : d294666 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294665 p = 1 := by simpa only [d294666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32433 p hg
    simpa only [d294666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32435 (p : Pattern) (guard : d294691 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d294666 p = 1 := by simpa only [d294691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32434 p hg
    simpa only [d294691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32436 (p : Pattern) (guard : d294599 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d294594 p = 1 := by simpa only [d294599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32427 p hg
    simpa only [d294599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32075 p hg
    simpa only [d294599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32437 (p : Pattern) (guard : d294600 p = 1) : d49997 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d294599 p = 1 := by simpa only [d294600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32436 p hg
    simpa only [d294600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32075 p hg
    simpa only [d294600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32438 (p : Pattern) (guard : d294601 p = 1) : d49999 p ≤ (1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d294600 p = 1 := by simpa only [d294601, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32437 p hg
    simpa only [d294601, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294601, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32079 p hg
    simpa only [d294601, d49999, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32439 (p : Pattern) (guard : d294602 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294602, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32046 p hg
    simpa only [d294602, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294601 p = 1 := by simpa only [d294602, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32438 p hg
    simpa only [d294602, d50000, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32440 (p : Pattern) (guard : d294603 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294598 p = 1 := by simpa only [d294603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32431 p hg
    simpa only [d294603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294602 p = 1 := by simpa only [d294603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32439 p hg
    simpa only [d294603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32441 (p : Pattern) (guard : d294604 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294603 p = 1 := by simpa only [d294604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32440 p hg
    simpa only [d294604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32442 (p : Pattern) (guard : d294605 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294604 p = 1 := by simpa only [d294605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32441 p hg
    simpa only [d294605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32443 (p : Pattern) (guard : d294619 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d294605 p = 1 := by simpa only [d294619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32442 p hg
    simpa only [d294619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32444 (p : Pattern) (guard : d294692 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294691 p = 1 := by simpa only [d294692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32435 p hg
    simpa only [d294692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294619 p = 1 := by simpa only [d294692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32443 p hg
    simpa only [d294692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32445 (p : Pattern) (guard : d294693 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d294692 p = 1 := by simpa only [d294693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32444 p hg
    simpa only [d294693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32446 (p : Pattern) (guard : d294670 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294598 p = 1 := by simpa only [d294670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32431 p hg
    simpa only [d294670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32447 (p : Pattern) (guard : d294671 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294670 p = 1 := by simpa only [d294671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32446 p hg
    simpa only [d294671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32448 (p : Pattern) (guard : d294672 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294671 p = 1 := by simpa only [d294672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32447 p hg
    simpa only [d294672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32449 (p : Pattern) (guard : d294694 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d294672 p = 1 := by simpa only [d294694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32448 p hg
    simpa only [d294694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32450 (p : Pattern) (guard : d294695 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294694 p = 1 := by simpa only [d294695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32449 p hg
    simpa only [d294695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32451 (p : Pattern) (guard : d294696 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d294695 p = 1 := by simpa only [d294696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32450 p hg
    simpa only [d294696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32452 (p : Pattern) (guard : d294697 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294693 p = 1 := by simpa only [d294697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32445 p hg
    simpa only [d294697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294696 p = 1 := by simpa only [d294697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32451 p hg
    simpa only [d294697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32453 (p : Pattern) (guard : d294718 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294697 p = 1 := by simpa only [d294718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32452 p hg
    simpa only [d294718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32454 (p : Pattern) (guard : d294719 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294718 p = 1 := by simpa only [d294719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32453 p hg
    simpa only [d294719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32455 (p : Pattern) (guard : d294720 p = 1) : d50001 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294720, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294720, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294719 p = 1 := by simpa only [d294720, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32454 p hg
    simpa only [d294720, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32456 (p : Pattern) (guard : d294721 p = 1) : d50001 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32044 p hg
    simpa only [d294721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294720 p = 1 := by simpa only [d294721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32455 p hg
    simpa only [d294721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32457 (p : Pattern) (guard : d294607 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d294602 p = 1 := by simpa only [d294607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32439 p hg
    simpa only [d294607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32458 (p : Pattern) (guard : d294608 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d294607 p = 1 := by simpa only [d294608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32457 p hg
    simpa only [d294608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32459 (p : Pattern) (guard : d294609 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d294608 p = 1 := by simpa only [d294609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32458 p hg
    simpa only [d294609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32460 (p : Pattern) (guard : d294620 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d294609 p = 1 := by simpa only [d294620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32459 p hg
    simpa only [d294620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32461 (p : Pattern) (guard : d294708 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d294620 p = 1 := by simpa only [d294708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32460 p hg
    simpa only [d294708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32462 (p : Pattern) (guard : d294709 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294708 p = 1 := by simpa only [d294709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32461 p hg
    simpa only [d294709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32463 (p : Pattern) (guard : d294710 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d294709 p = 1 := by simpa only [d294710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32462 p hg
    simpa only [d294710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32464 (p : Pattern) (guard : d294711 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294710 p = 1 := by simpa only [d294711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32463 p hg
    simpa only [d294711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32465 (p : Pattern) (guard : d294712 p = 1) : d50000 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32045 p hg
    simpa only [d294712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294711 p = 1 := by simpa only [d294712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32464 p hg
    simpa only [d294712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32466 (p : Pattern) (guard : d294722 p = 1) : d50001 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294722, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31967 p hg
    simpa only [d294722, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294712 p = 1 := by simpa only [d294722, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32465 p hg
    simpa only [d294722, d50001, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32467 (p : Pattern) (guard : d294723 p = 1) : d50001 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32044 p hg
    simpa only [d294723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294722 p = 1 := by simpa only [d294723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32466 p hg
    simpa only [d294723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32468 (p : Pattern) (guard : d294724 p = 1) : d50001 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d294721 p = 1 := by simpa only [d294724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32456 p hg
    simpa only [d294724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294723 p = 1 := by simpa only [d294724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32467 p hg
    simpa only [d294724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32469 (p : Pattern) (guard : d294725 p = 1) : d50001 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d294724 p = 1 := by simpa only [d294725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32468 p hg
    simpa only [d294725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32044 p hg
    simpa only [d294725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32470 (p : Pattern) (guard : d294726 p = 1) : d50001 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d294725 p = 1 := by simpa only [d294726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32469 p hg
    simpa only [d294726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32044 p hg
    simpa only [d294726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32471 (p : Pattern) (guard : d294727 p = 1) : d50002 p ≤ (1 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d294717 p = 1 := by simpa only [d294727, d50002, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32385 p hg
    simpa only [d294727, d50002, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294726 p = 1 := by simpa only [d294727, d50002, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32470 p hg
    simpa only [d294727, d50002, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32472 (p : Pattern) (guard : d131 p = 1) : d47630 p ≤ (1 : Int) + d47630 p := by
  omega
theorem compare32473 (p : Pattern) (guard : d25432 p = 1) : d49808 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d131 p = 1 := by simpa only [d25432, d49808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32472 p hg
    simpa only [d25432, d49808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25432, d49808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32105 p hg
    simpa only [d25432, d49808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32474 (p : Pattern) (guard : d25433 p = 1) : d49808 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d25432 p = 1 := by simpa only [d25433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32473 p hg
    simpa only [d25433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32103 p hg
    simpa only [d25433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32475 (p : Pattern) (guard : d25434 p = 1) : d49808 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d25433 p = 1 := by simpa only [d25434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32474 p hg
    simpa only [d25434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32103 p hg
    simpa only [d25434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32476 (p : Pattern) (guard : d205998 p = 1) : d49808 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d205998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32103 p hg
    simpa only [d205998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d25434 p = 1 := by simpa only [d205998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32475 p hg
    simpa only [d205998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32477 (p : Pattern) (guard : d294647 p = 1) : d49808 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32103 p hg
    simpa only [d294647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d205998 p = 1 := by simpa only [d294647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32476 p hg
    simpa only [d294647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32478 (p : Pattern) (guard : d294648 p = 1) : d49831 p ≤ (1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d294647 p = 1 := by simpa only [d294648, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32477 p hg
    simpa only [d294648, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294648, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32111 p hg
    simpa only [d294648, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32479 (p : Pattern) (guard : d294649 p = 1) : d49831 p ≤ (1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d294648 p = 1 := by simpa only [d294649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32478 p hg
    simpa only [d294649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32102 p hg
    simpa only [d294649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32480 (p : Pattern) (guard : d294728 p = 1) : d49831 p ≤ (1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32102 p hg
    simpa only [d294728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294649 p = 1 := by simpa only [d294728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32479 p hg
    simpa only [d294728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32481 (p : Pattern) (guard : d294650 p = 1) : d50030 p ≤ (1 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d294649 p = 1 := by simpa only [d294650, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32274 p hg
    simpa only [d294650, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294650, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32063 p hg
    simpa only [d294650, d50030, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32482 (p : Pattern) (guard : d294729 p = 1) : d50031 p ≤ (1 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d294728 p = 1 := by simpa only [d294729, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32480 p hg
    simpa only [d294729, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294650 p = 1 := by simpa only [d294729, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32481 p hg
    simpa only [d294729, d50031, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32483 (p : Pattern) (guard : d131 p = 1) : d47634 p ≤ (1 : Int) + d47634 p := by
  omega
theorem compare32484 (p : Pattern) (guard : d25432 p = 1) : d49811 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 224 with
  | false =>
    have hg : d131 p = 1 := by simpa only [d25432, d49811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32483 p hg
    simpa only [d25432, d49811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25432, d49811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32119 p hg
    simpa only [d25432, d49811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32485 (p : Pattern) (guard : d25433 p = 1) : d49811 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 223 with
  | false =>
    have hg : d25432 p = 1 := by simpa only [d25433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32484 p hg
    simpa only [d25433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32117 p hg
    simpa only [d25433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32486 (p : Pattern) (guard : d25434 p = 1) : d49811 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 204 with
  | false =>
    have hg : d25433 p = 1 := by simpa only [d25434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32485 p hg
    simpa only [d25434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32117 p hg
    simpa only [d25434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32487 (p : Pattern) (guard : d205998 p = 1) : d49811 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d205998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32117 p hg
    simpa only [d205998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d25434 p = 1 := by simpa only [d205998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32486 p hg
    simpa only [d205998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32488 (p : Pattern) (guard : d294647 p = 1) : d49811 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32117 p hg
    simpa only [d294647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d205998 p = 1 := by simpa only [d294647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32487 p hg
    simpa only [d294647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32489 (p : Pattern) (guard : d294648 p = 1) : d49857 p ≤ (1 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d294647 p = 1 := by simpa only [d294648, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32488 p hg
    simpa only [d294648, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294648, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32125 p hg
    simpa only [d294648, d49857, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32490 (p : Pattern) (guard : d294649 p = 1) : d49857 p ≤ (1 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d294648 p = 1 := by simpa only [d294649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32489 p hg
    simpa only [d294649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32127 p hg
    simpa only [d294649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32491 (p : Pattern) (guard : d294650 p = 1) : d49865 p ≤ (1 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d294649 p = 1 := by simpa only [d294650, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32490 p hg
    simpa only [d294650, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294650, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d294650, d49865, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32492 (p : Pattern) (guard : d294651 p = 1) : d49866 p ≤ (1 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d294650 p = 1 := by simpa only [d294651, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32491 p hg
    simpa only [d294651, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294651, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d294651, d49866, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32493 (p : Pattern) (guard : d294730 p = 1) : d50032 p ≤ (1 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d294729 p = 1 := by simpa only [d294730, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32482 p hg
    simpa only [d294730, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294651 p = 1 := by simpa only [d294730, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32492 p hg
    simpa only [d294730, d50032, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32494 (p : Pattern) (guard : d294731 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d294730 p = 1 := by simpa only [d294731, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32493 p hg
    simpa only [d294731, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294731, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32132 p hg
    simpa only [d294731, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32495 (p : Pattern) (guard : d294732 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32101 p hg
    simpa only [d294732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294731 p = 1 := by simpa only [d294732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32494 p hg
    simpa only [d294732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32496 (p : Pattern) (guard : d294733 p = 1) : d50036 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294732 p = 1 := by simpa only [d294733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32495 p hg
    simpa only [d294733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32101 p hg
    simpa only [d294733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32497 (p : Pattern) (guard : d205892 p = 1) : d49808 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d29090 p = 1 := by simpa only [d205892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32109 p hg
    simpa only [d205892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32103 p hg
    simpa only [d205892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32498 (p : Pattern) (guard : d205893 p = 1) : d49831 p ≤ (1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d205892 p = 1 := by simpa only [d205893, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32497 p hg
    simpa only [d205893, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205893, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32111 p hg
    simpa only [d205893, d49831, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare32499 (p : Pattern) (guard : d205894 p = 1) : d49831 p ≤ (1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d205893 p = 1 := by simpa only [d205894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32498 p hg
    simpa only [d205894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d205894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32102 p hg
    simpa only [d205894, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
