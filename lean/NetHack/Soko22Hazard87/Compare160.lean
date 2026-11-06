import NetHack.Soko22Hazard87.Compare159
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare40000 (p : Pattern) (guard : d324794 p = 1) : d50734 p ≤ (1 : Int) + d324548 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324794, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39939 p hg
    simpa only [d324794, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324793 p = 1 := by simpa only [d324794, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39999 p hg
    simpa only [d324794, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40001 (p : Pattern) (guard : d324795 p = 1) : d50735 p ≤ (1 : Int) + d324549 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324795, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39938 p hg
    simpa only [d324795, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324794 p = 1 := by simpa only [d324795, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40000 p hg
    simpa only [d324795, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40002 (p : Pattern) (guard : d324796 p = 1) : d50733 p ≤ (1 : Int) + d324547 p := by
  cases selected : p 159 with
  | false =>
    have hg : d324790 p = 1 := by simpa only [d324796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39996 p hg
    simpa only [d324796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39940 p hg
    simpa only [d324796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40003 (p : Pattern) (guard : d324797 p = 1) : d50733 p ≤ (1 : Int) + d324547 p := by
  cases selected : p 158 with
  | false =>
    have hg : d324791 p = 1 := by simpa only [d324797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39997 p hg
    simpa only [d324797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324796 p = 1 := by simpa only [d324797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40002 p hg
    simpa only [d324797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40004 (p : Pattern) (guard : d324798 p = 1) : d50733 p ≤ (1 : Int) + d324547 p := by
  cases selected : p 157 with
  | false =>
    have hg : d324792 p = 1 := by simpa only [d324798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39998 p hg
    simpa only [d324798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324797 p = 1 := by simpa only [d324798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40003 p hg
    simpa only [d324798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40005 (p : Pattern) (guard : d324799 p = 1) : d50734 p ≤ (1 : Int) + d324548 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324799, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39939 p hg
    simpa only [d324799, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324798 p = 1 := by simpa only [d324799, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40004 p hg
    simpa only [d324799, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40006 (p : Pattern) (guard : d324800 p = 1) : d50735 p ≤ (1 : Int) + d324549 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324800, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39938 p hg
    simpa only [d324800, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324799 p = 1 := by simpa only [d324800, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40005 p hg
    simpa only [d324800, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40007 (p : Pattern) (guard : d324801 p = 1) : d50735 p ≤ (1 : Int) + d324549 p := by
  cases selected : p 136 with
  | false =>
    have hg : d324795 p = 1 := by simpa only [d324801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40001 p hg
    simpa only [d324801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324800 p = 1 := by simpa only [d324801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40006 p hg
    simpa only [d324801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40008 (p : Pattern) (guard : d221101 p = 1) : d50560 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 180 with
  | false =>
    have hg : d221100 p = 1 := by simpa only [d221101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39979 p hg
    simpa only [d221101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39942 p hg
    simpa only [d221101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40009 (p : Pattern) (guard : d221342 p = 1) : d50726 p ≤ (1 : Int) + d324540 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d221342, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39941 p hg
    simpa only [d221342, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221101 p = 1 := by simpa only [d221342, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40008 p hg
    simpa only [d221342, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40010 (p : Pattern) (guard : d221102 p = 1) : d50727 p ≤ (1 : Int) + d324541 p := by
  cases selected : p 163 with
  | false =>
    have hg : d221101 p = 1 := by simpa only [d221102, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39664 p hg
    simpa only [d221102, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221102, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39826 p hg
    simpa only [d221102, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40011 (p : Pattern) (guard : d221343 p = 1) : d50728 p ≤ (1 : Int) + d324542 p := by
  cases selected : p 162 with
  | false =>
    have hg : d221342 p = 1 := by simpa only [d221343, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40009 p hg
    simpa only [d221343, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221102 p = 1 := by simpa only [d221343, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40010 p hg
    simpa only [d221343, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40012 (p : Pattern) (guard : d221101 p = 1) : d50562 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 180 with
  | false =>
    have hg : d221100 p = 1 := by simpa only [d221101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39991 p hg
    simpa only [d221101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39955 p hg
    simpa only [d221101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40013 (p : Pattern) (guard : d221102 p = 1) : d50573 p ≤ (1 : Int) + d324440 p := by
  cases selected : p 163 with
  | false =>
    have hg : d221101 p = 1 := by simpa only [d221102, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40012 p hg
    simpa only [d221102, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221102, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d221102, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40014 (p : Pattern) (guard : d221103 p = 1) : d50574 p ≤ (1 : Int) + d324441 p := by
  cases selected : p 162 with
  | false =>
    have hg : d221102 p = 1 := by simpa only [d221103, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40013 p hg
    simpa only [d221103, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221103, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d221103, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40015 (p : Pattern) (guard : d221344 p = 1) : d50729 p ≤ (1 : Int) + d324543 p := by
  cases selected : p 161 with
  | false =>
    have hg : d221343 p = 1 := by simpa only [d221344, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40011 p hg
    simpa only [d221344, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221103 p = 1 := by simpa only [d221344, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40014 p hg
    simpa only [d221344, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40016 (p : Pattern) (guard : d221345 p = 1) : d50733 p ≤ (1 : Int) + d324547 p := by
  cases selected : p 160 with
  | false =>
    have hg : d221344 p = 1 := by simpa only [d221345, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40015 p hg
    simpa only [d221345, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221345, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39968 p hg
    simpa only [d221345, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40017 (p : Pattern) (guard : d221346 p = 1) : d50733 p ≤ (1 : Int) + d324547 p := by
  cases selected : p 159 with
  | false =>
    have hg : d221345 p = 1 := by simpa only [d221346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40016 p hg
    simpa only [d221346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39940 p hg
    simpa only [d221346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40018 (p : Pattern) (guard : d324802 p = 1) : d50733 p ≤ (1 : Int) + d324547 p := by
  cases selected : p 158 with
  | false =>
    have hg : d324796 p = 1 := by simpa only [d324802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40002 p hg
    simpa only [d324802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221346 p = 1 := by simpa only [d324802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40017 p hg
    simpa only [d324802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40019 (p : Pattern) (guard : d324803 p = 1) : d50733 p ≤ (1 : Int) + d324547 p := by
  cases selected : p 157 with
  | false =>
    have hg : d324797 p = 1 := by simpa only [d324803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40003 p hg
    simpa only [d324803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324802 p = 1 := by simpa only [d324803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40018 p hg
    simpa only [d324803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40020 (p : Pattern) (guard : d324804 p = 1) : d50734 p ≤ (1 : Int) + d324548 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324804, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39939 p hg
    simpa only [d324804, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324803 p = 1 := by simpa only [d324804, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40019 p hg
    simpa only [d324804, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40021 (p : Pattern) (guard : d324805 p = 1) : d50735 p ≤ (1 : Int) + d324549 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324805, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39938 p hg
    simpa only [d324805, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324804 p = 1 := by simpa only [d324805, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40020 p hg
    simpa only [d324805, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40022 (p : Pattern) (guard : d324806 p = 1) : d50735 p ≤ (1 : Int) + d324549 p := by
  cases selected : p 136 with
  | false =>
    have hg : d324800 p = 1 := by simpa only [d324806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40006 p hg
    simpa only [d324806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324805 p = 1 := by simpa only [d324806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40021 p hg
    simpa only [d324806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40023 (p : Pattern) (guard : d324807 p = 1) : d50735 p ≤ (1 : Int) + d324549 p := by
  cases selected : p 135 with
  | false =>
    have hg : d324801 p = 1 := by simpa only [d324807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40007 p hg
    simpa only [d324807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324806 p = 1 := by simpa only [d324807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40022 p hg
    simpa only [d324807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40024 (p : Pattern) (guard : d0 p = 1) : d50735 p ≤ (1 : Int) + d324549 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40025 (p : Pattern) (guard : d324808 p = 1) : d50735 p ≤ (1 : Int) + d324549 p := by
  cases selected : p 119 with
  | false =>
    have hg : d324807 p = 1 := by simpa only [d324808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40023 p hg
    simpa only [d324808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40024 p hg
    simpa only [d324808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40026 (p : Pattern) (guard : d0 p = 1) : d50736 p ≤ (1 : Int) + d324550 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40027 (p : Pattern) (guard : d324809 p = 1) : d50737 p ≤ (1 : Int) + d324551 p := by
  cases selected : p 116 with
  | false =>
    have hg : d324808 p = 1 := by simpa only [d324809, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40025 p hg
    simpa only [d324809, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324809, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40026 p hg
    simpa only [d324809, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40028 (p : Pattern) (guard : d324810 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324810, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39621 p hg
    simpa only [d324810, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324809 p = 1 := by simpa only [d324810, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40027 p hg
    simpa only [d324810, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40029 (p : Pattern) (guard : d324811 p = 1) : d50735 p ≤ (1 : Int) + d324549 p := by
  cases selected : p 136 with
  | false =>
    have hg : d324805 p = 1 := by simpa only [d324811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40021 p hg
    simpa only [d324811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40024 p hg
    simpa only [d324811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40030 (p : Pattern) (guard : d324812 p = 1) : d50735 p ≤ (1 : Int) + d324549 p := by
  cases selected : p 135 with
  | false =>
    have hg : d324806 p = 1 := by simpa only [d324812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40022 p hg
    simpa only [d324812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324811 p = 1 := by simpa only [d324812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40029 p hg
    simpa only [d324812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40031 (p : Pattern) (guard : d324813 p = 1) : d50735 p ≤ (1 : Int) + d324549 p := by
  cases selected : p 119 with
  | false =>
    have hg : d324812 p = 1 := by simpa only [d324813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40030 p hg
    simpa only [d324813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40024 p hg
    simpa only [d324813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40032 (p : Pattern) (guard : d324814 p = 1) : d50737 p ≤ (1 : Int) + d324551 p := by
  cases selected : p 116 with
  | false =>
    have hg : d324813 p = 1 := by simpa only [d324814, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40031 p hg
    simpa only [d324814, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324814, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40026 p hg
    simpa only [d324814, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40033 (p : Pattern) (guard : d324815 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324815, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39621 p hg
    simpa only [d324815, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324814 p = 1 := by simpa only [d324815, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40032 p hg
    simpa only [d324815, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40034 (p : Pattern) (guard : d324816 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 113 with
  | false =>
    have hg : d324810 p = 1 := by simpa only [d324816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40028 p hg
    simpa only [d324816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324815 p = 1 := by simpa only [d324816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40033 p hg
    simpa only [d324816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40035 (p : Pattern) (guard : d324817 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 96 with
  | false =>
    have hg : d324816 p = 1 := by simpa only [d324817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40034 p hg
    simpa only [d324817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d324817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40036 (p : Pattern) (guard : d324818 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 95 with
  | false =>
    have hg : d324817 p = 1 := by simpa only [d324818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40035 p hg
    simpa only [d324818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d324818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40037 (p : Pattern) (guard : d324819 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 93 with
  | false =>
    have hg : d324818 p = 1 := by simpa only [d324819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40036 p hg
    simpa only [d324819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d324819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40038 (p : Pattern) (guard : d324820 p = 1) : d50735 p ≤ (1 : Int) + d324549 p := by
  cases selected : p 135 with
  | false =>
    have hg : d324811 p = 1 := by simpa only [d324820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40029 p hg
    simpa only [d324820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40024 p hg
    simpa only [d324820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40039 (p : Pattern) (guard : d324821 p = 1) : d50735 p ≤ (1 : Int) + d324549 p := by
  cases selected : p 119 with
  | false =>
    have hg : d324820 p = 1 := by simpa only [d324821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40038 p hg
    simpa only [d324821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40024 p hg
    simpa only [d324821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40040 (p : Pattern) (guard : d324822 p = 1) : d50737 p ≤ (1 : Int) + d324551 p := by
  cases selected : p 116 with
  | false =>
    have hg : d324821 p = 1 := by simpa only [d324822, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40039 p hg
    simpa only [d324822, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324822, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40026 p hg
    simpa only [d324822, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40041 (p : Pattern) (guard : d324823 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324823, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39621 p hg
    simpa only [d324823, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324822 p = 1 := by simpa only [d324823, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40040 p hg
    simpa only [d324823, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40042 (p : Pattern) (guard : d324824 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 113 with
  | false =>
    have hg : d324815 p = 1 := by simpa only [d324824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40033 p hg
    simpa only [d324824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324823 p = 1 := by simpa only [d324824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40041 p hg
    simpa only [d324824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40043 (p : Pattern) (guard : d324825 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 96 with
  | false =>
    have hg : d324824 p = 1 := by simpa only [d324825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40042 p hg
    simpa only [d324825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d324825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40044 (p : Pattern) (guard : d324826 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 95 with
  | false =>
    have hg : d324825 p = 1 := by simpa only [d324826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40043 p hg
    simpa only [d324826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d324826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40045 (p : Pattern) (guard : d324827 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 93 with
  | false =>
    have hg : d324826 p = 1 := by simpa only [d324827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40044 p hg
    simpa only [d324827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d324827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40046 (p : Pattern) (guard : d324828 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 91 with
  | false =>
    have hg : d324819 p = 1 := by simpa only [d324828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40037 p hg
    simpa only [d324828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324827 p = 1 := by simpa only [d324828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40045 p hg
    simpa only [d324828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40047 (p : Pattern) (guard : d324829 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 90 with
  | false =>
    have hg : d324828 p = 1 := by simpa only [d324829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40046 p hg
    simpa only [d324829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d324829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40048 (p : Pattern) (guard : d324707 p = 1) : d50560 p ≤ (1 : Int) + d49316 p := by
  cases selected : p 180 with
  | false =>
    have hg : d324615 p = 1 := by simpa only [d324707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39950 p hg
    simpa only [d324707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39942 p hg
    simpa only [d324707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40049 (p : Pattern) (guard : d324830 p = 1) : d50726 p ≤ (1 : Int) + d324540 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324830, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39941 p hg
    simpa only [d324830, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324707 p = 1 := by simpa only [d324830, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40048 p hg
    simpa only [d324830, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40050 (p : Pattern) (guard : d324708 p = 1) : d50727 p ≤ (1 : Int) + d324541 p := by
  cases selected : p 163 with
  | false =>
    have hg : d324707 p = 1 := by simpa only [d324708, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39745 p hg
    simpa only [d324708, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324708, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39826 p hg
    simpa only [d324708, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40051 (p : Pattern) (guard : d324831 p = 1) : d50728 p ≤ (1 : Int) + d324542 p := by
  cases selected : p 162 with
  | false =>
    have hg : d324830 p = 1 := by simpa only [d324831, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40049 p hg
    simpa only [d324831, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324708 p = 1 := by simpa only [d324831, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40050 p hg
    simpa only [d324831, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40052 (p : Pattern) (guard : d324707 p = 1) : d50562 p ≤ (1 : Int) + d49323 p := by
  cases selected : p 180 with
  | false =>
    have hg : d324615 p = 1 := by simpa only [d324707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39963 p hg
    simpa only [d324707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39955 p hg
    simpa only [d324707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40053 (p : Pattern) (guard : d324708 p = 1) : d50573 p ≤ (1 : Int) + d324440 p := by
  cases selected : p 163 with
  | false =>
    have hg : d324707 p = 1 := by simpa only [d324708, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40052 p hg
    simpa only [d324708, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324708, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d324708, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40054 (p : Pattern) (guard : d324709 p = 1) : d50574 p ≤ (1 : Int) + d324441 p := by
  cases selected : p 162 with
  | false =>
    have hg : d324708 p = 1 := by simpa only [d324709, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40053 p hg
    simpa only [d324709, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324709, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d324709, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40055 (p : Pattern) (guard : d324832 p = 1) : d50729 p ≤ (1 : Int) + d324543 p := by
  cases selected : p 161 with
  | false =>
    have hg : d324831 p = 1 := by simpa only [d324832, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40051 p hg
    simpa only [d324832, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324709 p = 1 := by simpa only [d324832, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40054 p hg
    simpa only [d324832, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40056 (p : Pattern) (guard : d324833 p = 1) : d50733 p ≤ (1 : Int) + d324547 p := by
  cases selected : p 160 with
  | false =>
    have hg : d324832 p = 1 := by simpa only [d324833, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40055 p hg
    simpa only [d324833, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324833, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39968 p hg
    simpa only [d324833, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40057 (p : Pattern) (guard : d324834 p = 1) : d50733 p ≤ (1 : Int) + d324547 p := by
  cases selected : p 159 with
  | false =>
    have hg : d324833 p = 1 := by simpa only [d324834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40056 p hg
    simpa only [d324834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39940 p hg
    simpa only [d324834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40058 (p : Pattern) (guard : d324835 p = 1) : d50733 p ≤ (1 : Int) + d324547 p := by
  cases selected : p 158 with
  | false =>
    have hg : d324791 p = 1 := by simpa only [d324835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39997 p hg
    simpa only [d324835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324834 p = 1 := by simpa only [d324835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40057 p hg
    simpa only [d324835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40059 (p : Pattern) (guard : d324836 p = 1) : d50733 p ≤ (1 : Int) + d324547 p := by
  cases selected : p 158 with
  | false =>
    have hg : d324834 p = 1 := by simpa only [d324836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40057 p hg
    simpa only [d324836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39940 p hg
    simpa only [d324836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40060 (p : Pattern) (guard : d324837 p = 1) : d50733 p ≤ (1 : Int) + d324547 p := by
  cases selected : p 157 with
  | false =>
    have hg : d324835 p = 1 := by simpa only [d324837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40058 p hg
    simpa only [d324837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324836 p = 1 := by simpa only [d324837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40059 p hg
    simpa only [d324837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40061 (p : Pattern) (guard : d324838 p = 1) : d50734 p ≤ (1 : Int) + d324548 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324838, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39939 p hg
    simpa only [d324838, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324837 p = 1 := by simpa only [d324838, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40060 p hg
    simpa only [d324838, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40062 (p : Pattern) (guard : d324839 p = 1) : d50735 p ≤ (1 : Int) + d324549 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324839, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39938 p hg
    simpa only [d324839, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324838 p = 1 := by simpa only [d324839, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40061 p hg
    simpa only [d324839, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40063 (p : Pattern) (guard : d324840 p = 1) : d50735 p ≤ (1 : Int) + d324549 p := by
  cases selected : p 136 with
  | false =>
    have hg : d324839 p = 1 := by simpa only [d324840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40062 p hg
    simpa only [d324840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40024 p hg
    simpa only [d324840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40064 (p : Pattern) (guard : d324841 p = 1) : d50735 p ≤ (1 : Int) + d324549 p := by
  cases selected : p 135 with
  | false =>
    have hg : d324806 p = 1 := by simpa only [d324841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40022 p hg
    simpa only [d324841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324840 p = 1 := by simpa only [d324841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40063 p hg
    simpa only [d324841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40065 (p : Pattern) (guard : d324842 p = 1) : d50735 p ≤ (1 : Int) + d324549 p := by
  cases selected : p 119 with
  | false =>
    have hg : d324841 p = 1 := by simpa only [d324842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40064 p hg
    simpa only [d324842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40024 p hg
    simpa only [d324842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40066 (p : Pattern) (guard : d324843 p = 1) : d50737 p ≤ (1 : Int) + d324551 p := by
  cases selected : p 116 with
  | false =>
    have hg : d324842 p = 1 := by simpa only [d324843, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40065 p hg
    simpa only [d324843, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324843, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40026 p hg
    simpa only [d324843, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40067 (p : Pattern) (guard : d324844 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324844, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39621 p hg
    simpa only [d324844, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324843 p = 1 := by simpa only [d324844, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40066 p hg
    simpa only [d324844, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40068 (p : Pattern) (guard : d324845 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 113 with
  | false =>
    have hg : d324844 p = 1 := by simpa only [d324845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40067 p hg
    simpa only [d324845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d324845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40069 (p : Pattern) (guard : d324846 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 96 with
  | false =>
    have hg : d324845 p = 1 := by simpa only [d324846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40068 p hg
    simpa only [d324846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d324846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40070 (p : Pattern) (guard : d324847 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 95 with
  | false =>
    have hg : d324846 p = 1 := by simpa only [d324847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40069 p hg
    simpa only [d324847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d324847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40071 (p : Pattern) (guard : d324848 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 93 with
  | false =>
    have hg : d324847 p = 1 := by simpa only [d324848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40070 p hg
    simpa only [d324848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d324848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40072 (p : Pattern) (guard : d324849 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 91 with
  | false =>
    have hg : d324848 p = 1 := by simpa only [d324849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40071 p hg
    simpa only [d324849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d324849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40073 (p : Pattern) (guard : d324850 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 90 with
  | false =>
    have hg : d324849 p = 1 := by simpa only [d324850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40072 p hg
    simpa only [d324850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d324850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40074 (p : Pattern) (guard : d324851 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 89 with
  | false =>
    have hg : d324829 p = 1 := by simpa only [d324851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40047 p hg
    simpa only [d324851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324850 p = 1 := by simpa only [d324851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40073 p hg
    simpa only [d324851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40075 (p : Pattern) (guard : d324852 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d324852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324851 p = 1 := by simpa only [d324852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40074 p hg
    simpa only [d324852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40076 (p : Pattern) (guard : d324853 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d324853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324852 p = 1 := by simpa only [d324853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40075 p hg
    simpa only [d324853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40077 (p : Pattern) (guard : d324854 p = 1) : d50739 p ≤ (1 : Int) + d324553 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324854, d50739, d324553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324854, d50739, d324553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324853 p = 1 := by simpa only [d324854, d50739, d324553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40076 p hg
    simpa only [d324854, d50739, d324553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40078 (p : Pattern) (guard : d324855 p = 1) : d50739 p ≤ (1 : Int) + d324553 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39936 p hg
    simpa only [d324855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324854 p = 1 := by simpa only [d324855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40077 p hg
    simpa only [d324855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40079 (p : Pattern) (guard : d324856 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 113 with
  | false =>
    have hg : d324823 p = 1 := by simpa only [d324856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40041 p hg
    simpa only [d324856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d324856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40080 (p : Pattern) (guard : d324857 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 96 with
  | false =>
    have hg : d324856 p = 1 := by simpa only [d324857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40079 p hg
    simpa only [d324857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d324857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40081 (p : Pattern) (guard : d324858 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 95 with
  | false =>
    have hg : d324857 p = 1 := by simpa only [d324858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40080 p hg
    simpa only [d324858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d324858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40082 (p : Pattern) (guard : d324859 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 93 with
  | false =>
    have hg : d324858 p = 1 := by simpa only [d324859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40081 p hg
    simpa only [d324859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d324859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40083 (p : Pattern) (guard : d324860 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 91 with
  | false =>
    have hg : d324859 p = 1 := by simpa only [d324860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40082 p hg
    simpa only [d324860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d324860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40084 (p : Pattern) (guard : d324861 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d324861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324860 p = 1 := by simpa only [d324861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40083 p hg
    simpa only [d324861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40085 (p : Pattern) (guard : d324862 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 89 with
  | false =>
    have hg : d324861 p = 1 := by simpa only [d324862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40084 p hg
    simpa only [d324862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d324862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40086 (p : Pattern) (guard : d324863 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d324863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324862 p = 1 := by simpa only [d324863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40085 p hg
    simpa only [d324863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40087 (p : Pattern) (guard : d324864 p = 1) : d50738 p ≤ (1 : Int) + d324552 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39937 p hg
    simpa only [d324864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324863 p = 1 := by simpa only [d324864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40086 p hg
    simpa only [d324864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40088 (p : Pattern) (guard : d324865 p = 1) : d50739 p ≤ (1 : Int) + d324553 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324865, d50739, d324553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324865, d50739, d324553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324864 p = 1 := by simpa only [d324865, d50739, d324553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40087 p hg
    simpa only [d324865, d50739, d324553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40089 (p : Pattern) (guard : d324866 p = 1) : d50739 p ≤ (1 : Int) + d324553 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39936 p hg
    simpa only [d324866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324865 p = 1 := by simpa only [d324866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40088 p hg
    simpa only [d324866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40090 (p : Pattern) (guard : d324867 p = 1) : d50739 p ≤ (1 : Int) + d324553 p := by
  cases selected : p 69 with
  | false =>
    have hg : d324855 p = 1 := by simpa only [d324867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40078 p hg
    simpa only [d324867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324866 p = 1 := by simpa only [d324867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40089 p hg
    simpa only [d324867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40091 (p : Pattern) (guard : d324868 p = 1) : d50739 p ≤ (1 : Int) + d324553 p := by
  cases selected : p 51 with
  | false =>
    have hg : d324867 p = 1 := by simpa only [d324868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40090 p hg
    simpa only [d324868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39936 p hg
    simpa only [d324868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40092 (p : Pattern) (guard : d324869 p = 1) : d50739 p ≤ (1 : Int) + d324553 p := by
  cases selected : p 50 with
  | false =>
    have hg : d324868 p = 1 := by simpa only [d324869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40091 p hg
    simpa only [d324869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39936 p hg
    simpa only [d324869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40093 (p : Pattern) (guard : d0 p = 1) : d50821 p ≤ (1 : Int) + d324609 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40094 (p : Pattern) (guard : d324870 p = 1) : d50822 p ≤ (1 : Int) + d324610 p := by
  cases selected : p 49 with
  | false =>
    have hg : d324869 p = 1 := by simpa only [d324870, d50822, d324610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40092 p hg
    simpa only [d324870, d50822, d324610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324870, d50822, d324610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40093 p hg
    simpa only [d324870, d50822, d324610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40095 (p : Pattern) (guard : d324871 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 48 with
  | false =>
    have hg : d324780 p = 1 := by simpa only [d324871, d50823, d324611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39935 p hg
    simpa only [d324871, d50823, d324611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324870 p = 1 := by simpa only [d324871, d50823, d324611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40094 p hg
    simpa only [d324871, d50823, d324611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40096 (p : Pattern) (guard : d324872 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d324872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324871 p = 1 := by simpa only [d324872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40095 p hg
    simpa only [d324872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40097 (p : Pattern) (guard : d324873 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d324873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324872 p = 1 := by simpa only [d324873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40096 p hg
    simpa only [d324873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40098 (p : Pattern) (guard : d324874 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d324874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324873 p = 1 := by simpa only [d324874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40097 p hg
    simpa only [d324874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40099 (p : Pattern) (guard : d324875 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d324875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324874 p = 1 := by simpa only [d324875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40098 p hg
    simpa only [d324875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40100 (p : Pattern) (guard : d324876 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d324876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324875 p = 1 := by simpa only [d324876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40099 p hg
    simpa only [d324876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40101 (p : Pattern) (guard : d324877 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d324877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324876 p = 1 := by simpa only [d324877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40100 p hg
    simpa only [d324877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40102 (p : Pattern) (guard : d324878 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d324878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324877 p = 1 := by simpa only [d324878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40101 p hg
    simpa only [d324878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40103 (p : Pattern) (guard : d324879 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d324879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324878 p = 1 := by simpa only [d324879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40102 p hg
    simpa only [d324879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40104 (p : Pattern) (guard : d324880 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d324880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324879 p = 1 := by simpa only [d324880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40103 p hg
    simpa only [d324880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40105 (p : Pattern) (guard : d324881 p = 1) : d50823 p ≤ (1 : Int) + d324611 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d324881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324880 p = 1 := by simpa only [d324881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40104 p hg
    simpa only [d324881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40106 (p : Pattern) (guard : d10055 p = 1) : d49396 p ≤ (1 : Int) + d49396 p := by
  omega
theorem compare40107 (p : Pattern) (guard : d38167 p = 1) : d50510 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38167, d50510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39627 p hg
    simpa only [d38167, d50510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10055 p = 1 := by simpa only [d38167, d50510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40106 p hg
    simpa only [d38167, d50510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40108 (p : Pattern) (guard : d38168 p = 1) : d50510 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 202 with
  | false =>
    have hg : d38167 p = 1 := by simpa only [d38168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40107 p hg
    simpa only [d38168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d38168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39630 p hg
    simpa only [d38168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40109 (p : Pattern) (guard : d38169 p = 1) : d50510 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 201 with
  | false =>
    have hg : d38168 p = 1 := by simpa only [d38169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40108 p hg
    simpa only [d38169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d38169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39630 p hg
    simpa only [d38169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40110 (p : Pattern) (guard : d38170 p = 1) : d50553 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 182 with
  | false =>
    have hg : d38169 p = 1 := by simpa only [d38170, d50553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40109 p hg
    simpa only [d38170, d50553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d38170, d50553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39633 p hg
    simpa only [d38170, d50553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40111 (p : Pattern) (guard : d38177 p = 1) : d50553 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39626 p hg
    simpa only [d38177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38170 p = 1 := by simpa only [d38177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40110 p hg
    simpa only [d38177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40112 (p : Pattern) (guard : d38178 p = 1) : d50570 p ≤ (1 : Int) + d324455 p := by
  cases selected : p 163 with
  | false =>
    have hg : d38177 p = 1 := by simpa only [d38178, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40111 p hg
    simpa only [d38178, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d38178, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39636 p hg
    simpa only [d38178, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40113 (p : Pattern) (guard : d38179 p = 1) : d50571 p ≤ (1 : Int) + d324456 p := by
  cases selected : p 162 with
  | false =>
    have hg : d38178 p = 1 := by simpa only [d38179, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40112 p hg
    simpa only [d38179, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d38179, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39638 p hg
    simpa only [d38179, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40114 (p : Pattern) (guard : d38180 p = 1) : d50572 p ≤ (1 : Int) + d324457 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38180, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39625 p hg
    simpa only [d38180, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38179 p = 1 := by simpa only [d38180, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40113 p hg
    simpa only [d38180, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40115 (p : Pattern) (guard : d38181 p = 1) : d50576 p ≤ (1 : Int) + d324458 p := by
  cases selected : p 160 with
  | false =>
    have hg : d38180 p = 1 := by simpa only [d38181, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40114 p hg
    simpa only [d38181, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d38181, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39641 p hg
    simpa only [d38181, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40116 (p : Pattern) (guard : d38302 p = 1) : d50576 p ≤ (1 : Int) + d324458 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39624 p hg
    simpa only [d38302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38181 p = 1 := by simpa only [d38302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40115 p hg
    simpa only [d38302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40117 (p : Pattern) (guard : d2043 p = 1) : d49396 p ≤ (1 : Int) + d49396 p := by
  omega
theorem compare40118 (p : Pattern) (guard : d221468 p = 1) : d50510 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d221468, d50510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39627 p hg
    simpa only [d221468, d50510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2043 p = 1 := by simpa only [d221468, d50510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40117 p hg
    simpa only [d221468, d50510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40119 (p : Pattern) (guard : d221488 p = 1) : d50510 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 202 with
  | false =>
    have hg : d221468 p = 1 := by simpa only [d221488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40118 p hg
    simpa only [d221488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39630 p hg
    simpa only [d221488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40120 (p : Pattern) (guard : d10406 p = 1) : d49396 p ≤ (1 : Int) + d49396 p := by
  omega
theorem compare40121 (p : Pattern) (guard : d221489 p = 1) : d50510 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d221489, d50510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39627 p hg
    simpa only [d221489, d50510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10406 p = 1 := by simpa only [d221489, d50510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40120 p hg
    simpa only [d221489, d50510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40122 (p : Pattern) (guard : d221490 p = 1) : d50510 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 202 with
  | false =>
    have hg : d221489 p = 1 := by simpa only [d221490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40121 p hg
    simpa only [d221490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39630 p hg
    simpa only [d221490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40123 (p : Pattern) (guard : d221491 p = 1) : d50510 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 201 with
  | false =>
    have hg : d221488 p = 1 := by simpa only [d221491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40119 p hg
    simpa only [d221491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221490 p = 1 := by simpa only [d221491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40122 p hg
    simpa only [d221491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40124 (p : Pattern) (guard : d221492 p = 1) : d50553 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 182 with
  | false =>
    have hg : d221491 p = 1 := by simpa only [d221492, d50553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40123 p hg
    simpa only [d221492, d50553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221492, d50553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39633 p hg
    simpa only [d221492, d50553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40125 (p : Pattern) (guard : d324882 p = 1) : d50553 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 180 with
  | false =>
    have hg : d38170 p = 1 := by simpa only [d324882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40110 p hg
    simpa only [d324882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221492 p = 1 := by simpa only [d324882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40124 p hg
    simpa only [d324882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40126 (p : Pattern) (guard : d324883 p = 1) : d50570 p ≤ (1 : Int) + d324455 p := by
  cases selected : p 163 with
  | false =>
    have hg : d324882 p = 1 := by simpa only [d324883, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40125 p hg
    simpa only [d324883, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324883, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39636 p hg
    simpa only [d324883, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40127 (p : Pattern) (guard : d324884 p = 1) : d50571 p ≤ (1 : Int) + d324456 p := by
  cases selected : p 162 with
  | false =>
    have hg : d324883 p = 1 := by simpa only [d324884, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40126 p hg
    simpa only [d324884, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324884, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39638 p hg
    simpa only [d324884, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40128 (p : Pattern) (guard : d324885 p = 1) : d50572 p ≤ (1 : Int) + d324457 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324885, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39625 p hg
    simpa only [d324885, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324884 p = 1 := by simpa only [d324885, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40127 p hg
    simpa only [d324885, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40129 (p : Pattern) (guard : d324886 p = 1) : d50576 p ≤ (1 : Int) + d324458 p := by
  cases selected : p 160 with
  | false =>
    have hg : d324885 p = 1 := by simpa only [d324886, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40128 p hg
    simpa only [d324886, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324886, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39641 p hg
    simpa only [d324886, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40130 (p : Pattern) (guard : d324887 p = 1) : d50576 p ≤ (1 : Int) + d324458 p := by
  cases selected : p 159 with
  | false =>
    have hg : d38181 p = 1 := by simpa only [d324887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40115 p hg
    simpa only [d324887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324886 p = 1 := by simpa only [d324887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40129 p hg
    simpa only [d324887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40131 (p : Pattern) (guard : d324888 p = 1) : d50576 p ≤ (1 : Int) + d324458 p := by
  cases selected : p 158 with
  | false =>
    have hg : d38302 p = 1 := by simpa only [d324888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40116 p hg
    simpa only [d324888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324887 p = 1 := by simpa only [d324888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40130 p hg
    simpa only [d324888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40132 (p : Pattern) (guard : d324889 p = 1) : d50576 p ≤ (1 : Int) + d324458 p := by
  cases selected : p 159 with
  | false =>
    have hg : d324886 p = 1 := by simpa only [d324889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40129 p hg
    simpa only [d324889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39624 p hg
    simpa only [d324889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40133 (p : Pattern) (guard : d324890 p = 1) : d50576 p ≤ (1 : Int) + d324458 p := by
  cases selected : p 158 with
  | false =>
    have hg : d324887 p = 1 := by simpa only [d324890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40130 p hg
    simpa only [d324890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324889 p = 1 := by simpa only [d324890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40132 p hg
    simpa only [d324890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40134 (p : Pattern) (guard : d324891 p = 1) : d50576 p ≤ (1 : Int) + d324458 p := by
  cases selected : p 157 with
  | false =>
    have hg : d324888 p = 1 := by simpa only [d324891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40131 p hg
    simpa only [d324891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324890 p = 1 := by simpa only [d324891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40133 p hg
    simpa only [d324891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40135 (p : Pattern) (guard : d324892 p = 1) : d50577 p ≤ (1 : Int) + d324459 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324892, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39623 p hg
    simpa only [d324892, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324891 p = 1 := by simpa only [d324892, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40134 p hg
    simpa only [d324892, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40136 (p : Pattern) (guard : d324893 p = 1) : d50578 p ≤ (1 : Int) + d324460 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324893, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39622 p hg
    simpa only [d324893, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324892 p = 1 := by simpa only [d324893, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40135 p hg
    simpa only [d324893, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40137 (p : Pattern) (guard : d221493 p = 1) : d50553 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 180 with
  | false =>
    have hg : d221492 p = 1 := by simpa only [d221493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40124 p hg
    simpa only [d221493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39626 p hg
    simpa only [d221493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40138 (p : Pattern) (guard : d221494 p = 1) : d50570 p ≤ (1 : Int) + d324455 p := by
  cases selected : p 163 with
  | false =>
    have hg : d221493 p = 1 := by simpa only [d221494, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40137 p hg
    simpa only [d221494, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221494, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39636 p hg
    simpa only [d221494, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40139 (p : Pattern) (guard : d221495 p = 1) : d50571 p ≤ (1 : Int) + d324456 p := by
  cases selected : p 162 with
  | false =>
    have hg : d221494 p = 1 := by simpa only [d221495, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40138 p hg
    simpa only [d221495, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221495, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39638 p hg
    simpa only [d221495, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40140 (p : Pattern) (guard : d221496 p = 1) : d50572 p ≤ (1 : Int) + d324457 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d221496, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39625 p hg
    simpa only [d221496, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221495 p = 1 := by simpa only [d221496, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40139 p hg
    simpa only [d221496, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40141 (p : Pattern) (guard : d221497 p = 1) : d50576 p ≤ (1 : Int) + d324458 p := by
  cases selected : p 160 with
  | false =>
    have hg : d221496 p = 1 := by simpa only [d221497, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40140 p hg
    simpa only [d221497, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221497, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39641 p hg
    simpa only [d221497, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40142 (p : Pattern) (guard : d221498 p = 1) : d50576 p ≤ (1 : Int) + d324458 p := by
  cases selected : p 159 with
  | false =>
    have hg : d221497 p = 1 := by simpa only [d221498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40141 p hg
    simpa only [d221498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39624 p hg
    simpa only [d221498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40143 (p : Pattern) (guard : d324894 p = 1) : d50576 p ≤ (1 : Int) + d324458 p := by
  cases selected : p 158 with
  | false =>
    have hg : d324889 p = 1 := by simpa only [d324894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40132 p hg
    simpa only [d324894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221498 p = 1 := by simpa only [d324894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40142 p hg
    simpa only [d324894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40144 (p : Pattern) (guard : d324895 p = 1) : d50576 p ≤ (1 : Int) + d324458 p := by
  cases selected : p 157 with
  | false =>
    have hg : d324890 p = 1 := by simpa only [d324895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40133 p hg
    simpa only [d324895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324894 p = 1 := by simpa only [d324895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40143 p hg
    simpa only [d324895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40145 (p : Pattern) (guard : d324896 p = 1) : d50577 p ≤ (1 : Int) + d324459 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324896, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39623 p hg
    simpa only [d324896, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324895 p = 1 := by simpa only [d324896, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40144 p hg
    simpa only [d324896, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40146 (p : Pattern) (guard : d324897 p = 1) : d50578 p ≤ (1 : Int) + d324460 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324897, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39622 p hg
    simpa only [d324897, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324896 p = 1 := by simpa only [d324897, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40145 p hg
    simpa only [d324897, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40147 (p : Pattern) (guard : d324898 p = 1) : d50578 p ≤ (1 : Int) + d324460 p := by
  cases selected : p 136 with
  | false =>
    have hg : d324893 p = 1 := by simpa only [d324898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40136 p hg
    simpa only [d324898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324897 p = 1 := by simpa only [d324898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40146 p hg
    simpa only [d324898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40148 (p : Pattern) (guard : d324899 p = 1) : d50578 p ≤ (1 : Int) + d324460 p := by
  cases selected : p 136 with
  | false =>
    have hg : d324897 p = 1 := by simpa only [d324899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40146 p hg
    simpa only [d324899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39675 p hg
    simpa only [d324899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40149 (p : Pattern) (guard : d324900 p = 1) : d50578 p ≤ (1 : Int) + d324460 p := by
  cases selected : p 135 with
  | false =>
    have hg : d324898 p = 1 := by simpa only [d324900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40147 p hg
    simpa only [d324900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324899 p = 1 := by simpa only [d324900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40148 p hg
    simpa only [d324900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40150 (p : Pattern) (guard : d324901 p = 1) : d50578 p ≤ (1 : Int) + d324460 p := by
  cases selected : p 119 with
  | false =>
    have hg : d324900 p = 1 := by simpa only [d324901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40149 p hg
    simpa only [d324901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39675 p hg
    simpa only [d324901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40151 (p : Pattern) (guard : d324902 p = 1) : d50590 p ≤ (1 : Int) + d324472 p := by
  cases selected : p 116 with
  | false =>
    have hg : d324901 p = 1 := by simpa only [d324902, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40150 p hg
    simpa only [d324902, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324902, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39679 p hg
    simpa only [d324902, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40152 (p : Pattern) (guard : d324903 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324903, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39621 p hg
    simpa only [d324903, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324902 p = 1 := by simpa only [d324903, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40151 p hg
    simpa only [d324903, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40153 (p : Pattern) (guard : d324904 p = 1) : d50578 p ≤ (1 : Int) + d324460 p := by
  cases selected : p 135 with
  | false =>
    have hg : d324899 p = 1 := by simpa only [d324904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40148 p hg
    simpa only [d324904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39675 p hg
    simpa only [d324904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40154 (p : Pattern) (guard : d324905 p = 1) : d50578 p ≤ (1 : Int) + d324460 p := by
  cases selected : p 119 with
  | false =>
    have hg : d324904 p = 1 := by simpa only [d324905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40153 p hg
    simpa only [d324905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39675 p hg
    simpa only [d324905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40155 (p : Pattern) (guard : d324906 p = 1) : d50590 p ≤ (1 : Int) + d324472 p := by
  cases selected : p 116 with
  | false =>
    have hg : d324905 p = 1 := by simpa only [d324906, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40154 p hg
    simpa only [d324906, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324906, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39679 p hg
    simpa only [d324906, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40156 (p : Pattern) (guard : d324907 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324907, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39621 p hg
    simpa only [d324907, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324906 p = 1 := by simpa only [d324907, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40155 p hg
    simpa only [d324907, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40157 (p : Pattern) (guard : d324908 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 113 with
  | false =>
    have hg : d324903 p = 1 := by simpa only [d324908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40152 p hg
    simpa only [d324908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324907 p = 1 := by simpa only [d324908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40156 p hg
    simpa only [d324908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40158 (p : Pattern) (guard : d324909 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 96 with
  | false =>
    have hg : d324908 p = 1 := by simpa only [d324909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40157 p hg
    simpa only [d324909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40159 (p : Pattern) (guard : d324910 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 95 with
  | false =>
    have hg : d324909 p = 1 := by simpa only [d324910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40158 p hg
    simpa only [d324910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40160 (p : Pattern) (guard : d324911 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324910 p = 1 := by simpa only [d324911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40159 p hg
    simpa only [d324911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40161 (p : Pattern) (guard : d324912 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 113 with
  | false =>
    have hg : d324907 p = 1 := by simpa only [d324912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40156 p hg
    simpa only [d324912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40162 (p : Pattern) (guard : d324913 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 96 with
  | false =>
    have hg : d324912 p = 1 := by simpa only [d324913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40161 p hg
    simpa only [d324913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40163 (p : Pattern) (guard : d324914 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 95 with
  | false =>
    have hg : d324913 p = 1 := by simpa only [d324914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40162 p hg
    simpa only [d324914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40164 (p : Pattern) (guard : d324915 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324914 p = 1 := by simpa only [d324915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40163 p hg
    simpa only [d324915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40165 (p : Pattern) (guard : d324916 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 91 with
  | false =>
    have hg : d324911 p = 1 := by simpa only [d324916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40160 p hg
    simpa only [d324916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324915 p = 1 := by simpa only [d324916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40164 p hg
    simpa only [d324916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40166 (p : Pattern) (guard : d324917 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324916 p = 1 := by simpa only [d324917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40165 p hg
    simpa only [d324917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40167 (p : Pattern) (guard : d324918 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 89 with
  | false =>
    have hg : d324917 p = 1 := by simpa only [d324918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40166 p hg
    simpa only [d324918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40168 (p : Pattern) (guard : d324919 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324918 p = 1 := by simpa only [d324919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40167 p hg
    simpa only [d324919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40169 (p : Pattern) (guard : d324920 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324919 p = 1 := by simpa only [d324920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40168 p hg
    simpa only [d324920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40170 (p : Pattern) (guard : d324921 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324920 p = 1 := by simpa only [d324921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40169 p hg
    simpa only [d324921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40171 (p : Pattern) (guard : d324922 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324921 p = 1 := by simpa only [d324922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40170 p hg
    simpa only [d324922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40172 (p : Pattern) (guard : d324923 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 69 with
  | false =>
    have hg : d324922 p = 1 := by simpa only [d324923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40171 p hg
    simpa only [d324923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40173 (p : Pattern) (guard : d324924 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 93 with
  | false =>
    have hg : d324910 p = 1 := by simpa only [d324924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40159 p hg
    simpa only [d324924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40174 (p : Pattern) (guard : d324925 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 93 with
  | false =>
    have hg : d324914 p = 1 := by simpa only [d324925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40163 p hg
    simpa only [d324925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40175 (p : Pattern) (guard : d324926 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 91 with
  | false =>
    have hg : d324924 p = 1 := by simpa only [d324926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40173 p hg
    simpa only [d324926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324925 p = 1 := by simpa only [d324926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40174 p hg
    simpa only [d324926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40176 (p : Pattern) (guard : d324927 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324926 p = 1 := by simpa only [d324927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40175 p hg
    simpa only [d324927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40177 (p : Pattern) (guard : d324928 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 89 with
  | false =>
    have hg : d324927 p = 1 := by simpa only [d324928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40176 p hg
    simpa only [d324928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40178 (p : Pattern) (guard : d324929 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324928 p = 1 := by simpa only [d324929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40177 p hg
    simpa only [d324929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40179 (p : Pattern) (guard : d324930 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324929 p = 1 := by simpa only [d324930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40178 p hg
    simpa only [d324930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40180 (p : Pattern) (guard : d324931 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 71 with
  | false =>
    have hg : d324920 p = 1 := by simpa only [d324931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40169 p hg
    simpa only [d324931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324930 p = 1 := by simpa only [d324931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40179 p hg
    simpa only [d324931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40181 (p : Pattern) (guard : d324932 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 70 with
  | false =>
    have hg : d324921 p = 1 := by simpa only [d324932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40170 p hg
    simpa only [d324932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324931 p = 1 := by simpa only [d324932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40180 p hg
    simpa only [d324932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40182 (p : Pattern) (guard : d324933 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 69 with
  | false =>
    have hg : d324932 p = 1 := by simpa only [d324933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40181 p hg
    simpa only [d324933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40183 (p : Pattern) (guard : d324934 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 51 with
  | false =>
    have hg : d324923 p = 1 := by simpa only [d324934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40172 p hg
    simpa only [d324934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324933 p = 1 := by simpa only [d324934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40182 p hg
    simpa only [d324934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40184 (p : Pattern) (guard : d324935 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324909 p = 1 := by simpa only [d324935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40158 p hg
    simpa only [d324935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40185 (p : Pattern) (guard : d324936 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324935 p = 1 := by simpa only [d324936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40184 p hg
    simpa only [d324936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40186 (p : Pattern) (guard : d324937 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324913 p = 1 := by simpa only [d324937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40162 p hg
    simpa only [d324937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40187 (p : Pattern) (guard : d324938 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324937 p = 1 := by simpa only [d324938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40186 p hg
    simpa only [d324938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40188 (p : Pattern) (guard : d324939 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 91 with
  | false =>
    have hg : d324936 p = 1 := by simpa only [d324939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40185 p hg
    simpa only [d324939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324938 p = 1 := by simpa only [d324939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40187 p hg
    simpa only [d324939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40189 (p : Pattern) (guard : d324940 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324939 p = 1 := by simpa only [d324940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40188 p hg
    simpa only [d324940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40190 (p : Pattern) (guard : d324941 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 89 with
  | false =>
    have hg : d324940 p = 1 := by simpa only [d324941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40189 p hg
    simpa only [d324941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40191 (p : Pattern) (guard : d324942 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324941 p = 1 := by simpa only [d324942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40190 p hg
    simpa only [d324942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40192 (p : Pattern) (guard : d324943 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324908 p = 1 := by simpa only [d324943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40157 p hg
    simpa only [d324943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40193 (p : Pattern) (guard : d324944 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 95 with
  | false =>
    have hg : d324943 p = 1 := by simpa only [d324944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40192 p hg
    simpa only [d324944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40194 (p : Pattern) (guard : d324945 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324944 p = 1 := by simpa only [d324945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40193 p hg
    simpa only [d324945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40195 (p : Pattern) (guard : d324946 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324912 p = 1 := by simpa only [d324946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40161 p hg
    simpa only [d324946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40196 (p : Pattern) (guard : d324947 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 95 with
  | false =>
    have hg : d324946 p = 1 := by simpa only [d324947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40195 p hg
    simpa only [d324947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40197 (p : Pattern) (guard : d324948 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324947 p = 1 := by simpa only [d324948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40196 p hg
    simpa only [d324948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40198 (p : Pattern) (guard : d324949 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 91 with
  | false =>
    have hg : d324945 p = 1 := by simpa only [d324949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40194 p hg
    simpa only [d324949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324948 p = 1 := by simpa only [d324949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40197 p hg
    simpa only [d324949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40199 (p : Pattern) (guard : d324950 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324949 p = 1 := by simpa only [d324950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40198 p hg
    simpa only [d324950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40200 (p : Pattern) (guard : d324951 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 89 with
  | false =>
    have hg : d324950 p = 1 := by simpa only [d324951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40199 p hg
    simpa only [d324951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40201 (p : Pattern) (guard : d38303 p = 1) : d50576 p ≤ (1 : Int) + d324458 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39624 p hg
    simpa only [d38303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38302 p = 1 := by simpa only [d38303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40116 p hg
    simpa only [d38303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40202 (p : Pattern) (guard : d324952 p = 1) : d50576 p ≤ (1 : Int) + d324458 p := by
  cases selected : p 157 with
  | false =>
    have hg : d38303 p = 1 := by simpa only [d324952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40201 p hg
    simpa only [d324952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324888 p = 1 := by simpa only [d324952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40131 p hg
    simpa only [d324952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40203 (p : Pattern) (guard : d324953 p = 1) : d50577 p ≤ (1 : Int) + d324459 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324953, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39623 p hg
    simpa only [d324953, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324952 p = 1 := by simpa only [d324953, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40202 p hg
    simpa only [d324953, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40204 (p : Pattern) (guard : d324954 p = 1) : d50578 p ≤ (1 : Int) + d324460 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324954, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39622 p hg
    simpa only [d324954, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324953 p = 1 := by simpa only [d324954, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40203 p hg
    simpa only [d324954, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40205 (p : Pattern) (guard : d324955 p = 1) : d50578 p ≤ (1 : Int) + d324460 p := by
  cases selected : p 136 with
  | false =>
    have hg : d324954 p = 1 := by simpa only [d324955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40204 p hg
    simpa only [d324955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324893 p = 1 := by simpa only [d324955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40136 p hg
    simpa only [d324955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40206 (p : Pattern) (guard : d324956 p = 1) : d50578 p ≤ (1 : Int) + d324460 p := by
  cases selected : p 135 with
  | false =>
    have hg : d324955 p = 1 := by simpa only [d324956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40205 p hg
    simpa only [d324956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324898 p = 1 := by simpa only [d324956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40147 p hg
    simpa only [d324956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40207 (p : Pattern) (guard : d324957 p = 1) : d50578 p ≤ (1 : Int) + d324460 p := by
  cases selected : p 119 with
  | false =>
    have hg : d324956 p = 1 := by simpa only [d324957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40206 p hg
    simpa only [d324957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39675 p hg
    simpa only [d324957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40208 (p : Pattern) (guard : d324958 p = 1) : d50590 p ≤ (1 : Int) + d324472 p := by
  cases selected : p 116 with
  | false =>
    have hg : d324957 p = 1 := by simpa only [d324958, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40207 p hg
    simpa only [d324958, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324958, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39679 p hg
    simpa only [d324958, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40209 (p : Pattern) (guard : d324959 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324959, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39621 p hg
    simpa only [d324959, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324958 p = 1 := by simpa only [d324959, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40208 p hg
    simpa only [d324959, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40210 (p : Pattern) (guard : d324960 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 113 with
  | false =>
    have hg : d324959 p = 1 := by simpa only [d324960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40209 p hg
    simpa only [d324960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324903 p = 1 := by simpa only [d324960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40152 p hg
    simpa only [d324960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40211 (p : Pattern) (guard : d324961 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 96 with
  | false =>
    have hg : d324960 p = 1 := by simpa only [d324961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40210 p hg
    simpa only [d324961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40212 (p : Pattern) (guard : d324962 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 95 with
  | false =>
    have hg : d324961 p = 1 := by simpa only [d324962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40211 p hg
    simpa only [d324962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40213 (p : Pattern) (guard : d324963 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324962 p = 1 := by simpa only [d324963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40212 p hg
    simpa only [d324963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40214 (p : Pattern) (guard : d324964 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 91 with
  | false =>
    have hg : d324963 p = 1 := by simpa only [d324964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40213 p hg
    simpa only [d324964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324911 p = 1 := by simpa only [d324964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40160 p hg
    simpa only [d324964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40215 (p : Pattern) (guard : d324965 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 90 with
  | false =>
    have hg : d324964 p = 1 := by simpa only [d324965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40214 p hg
    simpa only [d324965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40216 (p : Pattern) (guard : d324966 p = 1) : d50553 p ≤ (1 : Int) + d49396 p := by
  cases selected : p 180 with
  | false =>
    have hg : d38170 p = 1 := by simpa only [d324966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40110 p hg
    simpa only [d324966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39626 p hg
    simpa only [d324966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40217 (p : Pattern) (guard : d324967 p = 1) : d50570 p ≤ (1 : Int) + d324455 p := by
  cases selected : p 163 with
  | false =>
    have hg : d324966 p = 1 := by simpa only [d324967, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40216 p hg
    simpa only [d324967, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324967, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39636 p hg
    simpa only [d324967, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40218 (p : Pattern) (guard : d324968 p = 1) : d50571 p ≤ (1 : Int) + d324456 p := by
  cases selected : p 162 with
  | false =>
    have hg : d324967 p = 1 := by simpa only [d324968, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40217 p hg
    simpa only [d324968, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324968, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39638 p hg
    simpa only [d324968, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40219 (p : Pattern) (guard : d324969 p = 1) : d50572 p ≤ (1 : Int) + d324457 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324969, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39625 p hg
    simpa only [d324969, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324968 p = 1 := by simpa only [d324969, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40218 p hg
    simpa only [d324969, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40220 (p : Pattern) (guard : d324970 p = 1) : d50576 p ≤ (1 : Int) + d324458 p := by
  cases selected : p 160 with
  | false =>
    have hg : d324969 p = 1 := by simpa only [d324970, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40219 p hg
    simpa only [d324970, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324970, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39641 p hg
    simpa only [d324970, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40221 (p : Pattern) (guard : d324971 p = 1) : d50576 p ≤ (1 : Int) + d324458 p := by
  cases selected : p 159 with
  | false =>
    have hg : d324970 p = 1 := by simpa only [d324971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40220 p hg
    simpa only [d324971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39624 p hg
    simpa only [d324971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40222 (p : Pattern) (guard : d324972 p = 1) : d50576 p ≤ (1 : Int) + d324458 p := by
  cases selected : p 158 with
  | false =>
    have hg : d324887 p = 1 := by simpa only [d324972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40130 p hg
    simpa only [d324972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324971 p = 1 := by simpa only [d324972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40221 p hg
    simpa only [d324972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40223 (p : Pattern) (guard : d324973 p = 1) : d50576 p ≤ (1 : Int) + d324458 p := by
  cases selected : p 158 with
  | false =>
    have hg : d324971 p = 1 := by simpa only [d324973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40221 p hg
    simpa only [d324973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39624 p hg
    simpa only [d324973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40224 (p : Pattern) (guard : d324974 p = 1) : d50576 p ≤ (1 : Int) + d324458 p := by
  cases selected : p 157 with
  | false =>
    have hg : d324972 p = 1 := by simpa only [d324974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40222 p hg
    simpa only [d324974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324973 p = 1 := by simpa only [d324974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40223 p hg
    simpa only [d324974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40225 (p : Pattern) (guard : d324975 p = 1) : d50577 p ≤ (1 : Int) + d324459 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324975, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39623 p hg
    simpa only [d324975, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324974 p = 1 := by simpa only [d324975, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40224 p hg
    simpa only [d324975, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40226 (p : Pattern) (guard : d324976 p = 1) : d50578 p ≤ (1 : Int) + d324460 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324976, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39622 p hg
    simpa only [d324976, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324975 p = 1 := by simpa only [d324976, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40225 p hg
    simpa only [d324976, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40227 (p : Pattern) (guard : d324977 p = 1) : d50578 p ≤ (1 : Int) + d324460 p := by
  cases selected : p 136 with
  | false =>
    have hg : d324976 p = 1 := by simpa only [d324977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40226 p hg
    simpa only [d324977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39675 p hg
    simpa only [d324977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40228 (p : Pattern) (guard : d324978 p = 1) : d50578 p ≤ (1 : Int) + d324460 p := by
  cases selected : p 135 with
  | false =>
    have hg : d324898 p = 1 := by simpa only [d324978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40147 p hg
    simpa only [d324978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324977 p = 1 := by simpa only [d324978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40227 p hg
    simpa only [d324978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40229 (p : Pattern) (guard : d324979 p = 1) : d50578 p ≤ (1 : Int) + d324460 p := by
  cases selected : p 119 with
  | false =>
    have hg : d324978 p = 1 := by simpa only [d324979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40228 p hg
    simpa only [d324979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39675 p hg
    simpa only [d324979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40230 (p : Pattern) (guard : d324980 p = 1) : d50590 p ≤ (1 : Int) + d324472 p := by
  cases selected : p 116 with
  | false =>
    have hg : d324979 p = 1 := by simpa only [d324980, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40229 p hg
    simpa only [d324980, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324980, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39679 p hg
    simpa only [d324980, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40231 (p : Pattern) (guard : d324981 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324981, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39621 p hg
    simpa only [d324981, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324980 p = 1 := by simpa only [d324981, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40230 p hg
    simpa only [d324981, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40232 (p : Pattern) (guard : d324982 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 113 with
  | false =>
    have hg : d324981 p = 1 := by simpa only [d324982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40231 p hg
    simpa only [d324982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40233 (p : Pattern) (guard : d324983 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 96 with
  | false =>
    have hg : d324982 p = 1 := by simpa only [d324983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40232 p hg
    simpa only [d324983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324983, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40234 (p : Pattern) (guard : d324984 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 95 with
  | false =>
    have hg : d324983 p = 1 := by simpa only [d324984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40233 p hg
    simpa only [d324984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40235 (p : Pattern) (guard : d324985 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324984 p = 1 := by simpa only [d324985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40234 p hg
    simpa only [d324985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40236 (p : Pattern) (guard : d324986 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 91 with
  | false =>
    have hg : d324985 p = 1 := by simpa only [d324986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40235 p hg
    simpa only [d324986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40237 (p : Pattern) (guard : d324987 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 90 with
  | false =>
    have hg : d324986 p = 1 := by simpa only [d324987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40236 p hg
    simpa only [d324987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40238 (p : Pattern) (guard : d324988 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 89 with
  | false =>
    have hg : d324965 p = 1 := by simpa only [d324988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40215 p hg
    simpa only [d324988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324987 p = 1 := by simpa only [d324988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40237 p hg
    simpa only [d324988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40239 (p : Pattern) (guard : d324989 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 74 with
  | false =>
    have hg : d324951 p = 1 := by simpa only [d324989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40200 p hg
    simpa only [d324989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324988 p = 1 := by simpa only [d324989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40238 p hg
    simpa only [d324989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40240 (p : Pattern) (guard : d324990 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 73 with
  | false =>
    have hg : d324942 p = 1 := by simpa only [d324990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40191 p hg
    simpa only [d324990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324989 p = 1 := by simpa only [d324990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40239 p hg
    simpa only [d324990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40241 (p : Pattern) (guard : d324991 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324990 p = 1 := by simpa only [d324991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40240 p hg
    simpa only [d324991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40242 (p : Pattern) (guard : d324992 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 93 with
  | false =>
    have hg : d324935 p = 1 := by simpa only [d324992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40184 p hg
    simpa only [d324992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40243 (p : Pattern) (guard : d324993 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 93 with
  | false =>
    have hg : d324937 p = 1 := by simpa only [d324993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40186 p hg
    simpa only [d324993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40244 (p : Pattern) (guard : d324994 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 91 with
  | false =>
    have hg : d324992 p = 1 := by simpa only [d324994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40242 p hg
    simpa only [d324994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324993 p = 1 := by simpa only [d324994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40243 p hg
    simpa only [d324994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40245 (p : Pattern) (guard : d324995 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324994 p = 1 := by simpa only [d324995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40244 p hg
    simpa only [d324995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40246 (p : Pattern) (guard : d324996 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 89 with
  | false =>
    have hg : d324995 p = 1 := by simpa only [d324996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40245 p hg
    simpa only [d324996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40247 (p : Pattern) (guard : d324997 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324997, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324996 p = 1 := by simpa only [d324997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40246 p hg
    simpa only [d324997, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40248 (p : Pattern) (guard : d324998 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 93 with
  | false =>
    have hg : d324944 p = 1 := by simpa only [d324998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40193 p hg
    simpa only [d324998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40249 (p : Pattern) (guard : d324999 p = 1) : d50591 p ≤ (1 : Int) + d324473 p := by
  cases selected : p 93 with
  | false =>
    have hg : d324947 p = 1 := by simpa only [d324999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40196 p hg
    simpa only [d324999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d324999, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
