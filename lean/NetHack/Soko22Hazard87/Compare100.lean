import NetHack.Soko22Hazard87.Compare099
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare25000 (p : Pattern) (guard : d181628 p = 1) : d48707 p ≤ (2 : Int) + d130454 p := by
  cases selected : p 50 with
  | false =>
    have hg : d181627 p = 1 := by simpa only [d181628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24999 p hg
    simpa only [d181628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24925 p hg
    simpa only [d181628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25001 (p : Pattern) (guard : d181629 p = 1) : d48748 p ≤ (2 : Int) + d130478 p := by
  cases selected : p 49 with
  | false =>
    have hg : d181628 p = 1 := by simpa only [d181629, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25000 p hg
    simpa only [d181629, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181629, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24965 p hg
    simpa only [d181629, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25002 (p : Pattern) (guard : d181630 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181630, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24924 p hg
    simpa only [d181630, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181629 p = 1 := by simpa only [d181630, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25001 p hg
    simpa only [d181630, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25003 (p : Pattern) (guard : d181631 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181630 p = 1 := by simpa only [d181631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25002 p hg
    simpa only [d181631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25004 (p : Pattern) (guard : d181632 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181631 p = 1 := by simpa only [d181632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25003 p hg
    simpa only [d181632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25005 (p : Pattern) (guard : d181633 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181632 p = 1 := by simpa only [d181633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25004 p hg
    simpa only [d181633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25006 (p : Pattern) (guard : d181634 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181633 p = 1 := by simpa only [d181634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25005 p hg
    simpa only [d181634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25007 (p : Pattern) (guard : d181635 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181634 p = 1 := by simpa only [d181635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25006 p hg
    simpa only [d181635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25008 (p : Pattern) (guard : d181636 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d181619 p = 1 := by simpa only [d181636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24972 p hg
    simpa only [d181636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181635 p = 1 := by simpa only [d181636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25007 p hg
    simpa only [d181636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25009 (p : Pattern) (guard : d412 p = 1) : d47652 p ≤ (2 : Int) + d47652 p := by
  omega
theorem compare25010 (p : Pattern) (guard : d18631 p = 1) : d48567 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d412 p = 1 := by simpa only [d18631, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25009 p hg
    simpa only [d18631, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18631, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24932 p hg
    simpa only [d18631, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25011 (p : Pattern) (guard : d180974 p = 1) : d48698 p ≤ (2 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d18631 p = 1 := by simpa only [d180974, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25010 p hg
    simpa only [d180974, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180974, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24934 p hg
    simpa only [d180974, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25012 (p : Pattern) (guard : d180975 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d180974 p = 1 := by simpa only [d180975, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25011 p hg
    simpa only [d180975, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180975, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24936 p hg
    simpa only [d180975, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25013 (p : Pattern) (guard : d180976 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d180975 p = 1 := by simpa only [d180976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25012 p hg
    simpa only [d180976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180942 p = 1 := by simpa only [d180976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24976 p hg
    simpa only [d180976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25014 (p : Pattern) (guard : d12599 p = 1) : d47652 p ≤ (2 : Int) + d47652 p := by
  omega
theorem compare25015 (p : Pattern) (guard : d18635 p = 1) : d48567 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d12599 p = 1 := by simpa only [d18635, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25014 p hg
    simpa only [d18635, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18635, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24932 p hg
    simpa only [d18635, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25016 (p : Pattern) (guard : d180977 p = 1) : d48698 p ≤ (2 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d18635 p = 1 := by simpa only [d180977, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25015 p hg
    simpa only [d180977, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180977, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24934 p hg
    simpa only [d180977, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25017 (p : Pattern) (guard : d180978 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d180977 p = 1 := by simpa only [d180978, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25016 p hg
    simpa only [d180978, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180978, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24936 p hg
    simpa only [d180978, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25018 (p : Pattern) (guard : d180979 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d180978 p = 1 := by simpa only [d180979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25017 p hg
    simpa only [d180979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180910 p = 1 := by simpa only [d180979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24937 p hg
    simpa only [d180979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25019 (p : Pattern) (guard : d180980 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d180976 p = 1 := by simpa only [d180980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25013 p hg
    simpa only [d180980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180979 p = 1 := by simpa only [d180980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25018 p hg
    simpa only [d180980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25020 (p : Pattern) (guard : d180981 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 157 with
  | false =>
    have hg : d180980 p = 1 := by simpa only [d180981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25019 p hg
    simpa only [d180981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180944 p = 1 := by simpa only [d180981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24978 p hg
    simpa only [d180981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25021 (p : Pattern) (guard : d180982 p = 1) : d48702 p ≤ (2 : Int) + d130449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180982, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24930 p hg
    simpa only [d180982, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180981 p = 1 := by simpa only [d180982, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25020 p hg
    simpa only [d180982, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25022 (p : Pattern) (guard : d180983 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180983, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24929 p hg
    simpa only [d180983, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180982 p = 1 := by simpa only [d180983, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25021 p hg
    simpa only [d180983, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25023 (p : Pattern) (guard : d180984 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 136 with
  | false =>
    have hg : d180983 p = 1 := by simpa only [d180984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25022 p hg
    simpa only [d180984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180947 p = 1 := by simpa only [d180984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24981 p hg
    simpa only [d180984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25024 (p : Pattern) (guard : d181044 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 136 with
  | false =>
    have hg : d180947 p = 1 := by simpa only [d181044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24981 p hg
    simpa only [d181044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24944 p hg
    simpa only [d181044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25025 (p : Pattern) (guard : d181045 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 135 with
  | false =>
    have hg : d180984 p = 1 := by simpa only [d181045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25023 p hg
    simpa only [d181045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181044 p = 1 := by simpa only [d181045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25024 p hg
    simpa only [d181045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25026 (p : Pattern) (guard : d181046 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 119 with
  | false =>
    have hg : d181045 p = 1 := by simpa only [d181046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25025 p hg
    simpa only [d181046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24944 p hg
    simpa only [d181046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25027 (p : Pattern) (guard : d181047 p = 1) : d48705 p ≤ (2 : Int) + d130452 p := by
  cases selected : p 116 with
  | false =>
    have hg : d181046 p = 1 := by simpa only [d181047, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25026 p hg
    simpa only [d181047, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181047, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24948 p hg
    simpa only [d181047, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25028 (p : Pattern) (guard : d181048 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181048, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24928 p hg
    simpa only [d181048, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181047 p = 1 := by simpa only [d181048, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25027 p hg
    simpa only [d181048, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25029 (p : Pattern) (guard : d181053 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 135 with
  | false =>
    have hg : d181044 p = 1 := by simpa only [d181053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25024 p hg
    simpa only [d181053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24944 p hg
    simpa only [d181053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25030 (p : Pattern) (guard : d181054 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 119 with
  | false =>
    have hg : d181053 p = 1 := by simpa only [d181054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25029 p hg
    simpa only [d181054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24944 p hg
    simpa only [d181054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25031 (p : Pattern) (guard : d181055 p = 1) : d48705 p ≤ (2 : Int) + d130452 p := by
  cases selected : p 116 with
  | false =>
    have hg : d181054 p = 1 := by simpa only [d181055, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25030 p hg
    simpa only [d181055, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181055, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24948 p hg
    simpa only [d181055, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25032 (p : Pattern) (guard : d181056 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181056, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24928 p hg
    simpa only [d181056, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181055 p = 1 := by simpa only [d181056, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25031 p hg
    simpa only [d181056, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25033 (p : Pattern) (guard : d181057 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 113 with
  | false =>
    have hg : d181048 p = 1 := by simpa only [d181057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25028 p hg
    simpa only [d181057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181056 p = 1 := by simpa only [d181057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25032 p hg
    simpa only [d181057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25034 (p : Pattern) (guard : d181058 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 96 with
  | false =>
    have hg : d181057 p = 1 := by simpa only [d181058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25033 p hg
    simpa only [d181058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25035 (p : Pattern) (guard : d181059 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 95 with
  | false =>
    have hg : d181058 p = 1 := by simpa only [d181059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25034 p hg
    simpa only [d181059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25036 (p : Pattern) (guard : d181060 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 93 with
  | false =>
    have hg : d181059 p = 1 := by simpa only [d181060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25035 p hg
    simpa only [d181060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25037 (p : Pattern) (guard : d181074 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 113 with
  | false =>
    have hg : d181056 p = 1 := by simpa only [d181074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25032 p hg
    simpa only [d181074, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181074, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25038 (p : Pattern) (guard : d181075 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 96 with
  | false =>
    have hg : d181074 p = 1 := by simpa only [d181075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25037 p hg
    simpa only [d181075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25039 (p : Pattern) (guard : d181076 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 95 with
  | false =>
    have hg : d181075 p = 1 := by simpa only [d181076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25038 p hg
    simpa only [d181076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25040 (p : Pattern) (guard : d181077 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 93 with
  | false =>
    have hg : d181076 p = 1 := by simpa only [d181077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25039 p hg
    simpa only [d181077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25041 (p : Pattern) (guard : d181637 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 91 with
  | false =>
    have hg : d181060 p = 1 := by simpa only [d181637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25036 p hg
    simpa only [d181637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181077 p = 1 := by simpa only [d181637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25040 p hg
    simpa only [d181637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25042 (p : Pattern) (guard : d181638 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181637 p = 1 := by simpa only [d181638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25041 p hg
    simpa only [d181638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25043 (p : Pattern) (guard : d181639 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 89 with
  | false =>
    have hg : d181638 p = 1 := by simpa only [d181639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25042 p hg
    simpa only [d181639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25044 (p : Pattern) (guard : d181640 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181639 p = 1 := by simpa only [d181640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25043 p hg
    simpa only [d181640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25045 (p : Pattern) (guard : d181641 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181640 p = 1 := by simpa only [d181641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25044 p hg
    simpa only [d181641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25046 (p : Pattern) (guard : d181642 p = 1) : d48707 p ≤ (2 : Int) + d130454 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181642, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24926 p hg
    simpa only [d181642, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181641 p = 1 := by simpa only [d181642, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25045 p hg
    simpa only [d181642, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25047 (p : Pattern) (guard : d181643 p = 1) : d48707 p ≤ (2 : Int) + d130454 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24925 p hg
    simpa only [d181643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181642 p = 1 := by simpa only [d181643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25046 p hg
    simpa only [d181643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25048 (p : Pattern) (guard : d181644 p = 1) : d48707 p ≤ (2 : Int) + d130454 p := by
  cases selected : p 69 with
  | false =>
    have hg : d181643 p = 1 := by simpa only [d181644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25047 p hg
    simpa only [d181644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24925 p hg
    simpa only [d181644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25049 (p : Pattern) (guard : d181645 p = 1) : d48707 p ≤ (2 : Int) + d130454 p := by
  cases selected : p 51 with
  | false =>
    have hg : d181644 p = 1 := by simpa only [d181645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25048 p hg
    simpa only [d181645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24925 p hg
    simpa only [d181645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25050 (p : Pattern) (guard : d181646 p = 1) : d48707 p ≤ (2 : Int) + d130454 p := by
  cases selected : p 50 with
  | false =>
    have hg : d181645 p = 1 := by simpa only [d181646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25049 p hg
    simpa only [d181646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24925 p hg
    simpa only [d181646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25051 (p : Pattern) (guard : d181647 p = 1) : d48748 p ≤ (2 : Int) + d130478 p := by
  cases selected : p 49 with
  | false =>
    have hg : d181646 p = 1 := by simpa only [d181647, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25050 p hg
    simpa only [d181647, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181647, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24965 p hg
    simpa only [d181647, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25052 (p : Pattern) (guard : d181648 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181648, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24924 p hg
    simpa only [d181648, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181647 p = 1 := by simpa only [d181648, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25051 p hg
    simpa only [d181648, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25053 (p : Pattern) (guard : d181649 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181648 p = 1 := by simpa only [d181649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25052 p hg
    simpa only [d181649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25054 (p : Pattern) (guard : d181650 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181649 p = 1 := by simpa only [d181650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25053 p hg
    simpa only [d181650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25055 (p : Pattern) (guard : d181651 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181650 p = 1 := by simpa only [d181651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25054 p hg
    simpa only [d181651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25056 (p : Pattern) (guard : d181652 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181651 p = 1 := by simpa only [d181652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25055 p hg
    simpa only [d181652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25057 (p : Pattern) (guard : d181653 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181652 p = 1 := by simpa only [d181653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25056 p hg
    simpa only [d181653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25058 (p : Pattern) (guard : d181654 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181653 p = 1 := by simpa only [d181654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25057 p hg
    simpa only [d181654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25059 (p : Pattern) (guard : d181655 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d181636 p = 1 := by simpa only [d181655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25008 p hg
    simpa only [d181655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181654 p = 1 := by simpa only [d181655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25058 p hg
    simpa only [d181655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25060 (p : Pattern) (guard : d659 p = 1) : d47652 p ≤ (2 : Int) + d47652 p := by
  omega
theorem compare25061 (p : Pattern) (guard : d18708 p = 1) : d48567 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d659 p = 1 := by simpa only [d18708, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25060 p hg
    simpa only [d18708, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18708, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24932 p hg
    simpa only [d18708, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25062 (p : Pattern) (guard : d181023 p = 1) : d48698 p ≤ (2 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d18708 p = 1 := by simpa only [d181023, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25061 p hg
    simpa only [d181023, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181023, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24934 p hg
    simpa only [d181023, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25063 (p : Pattern) (guard : d181024 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181023 p = 1 := by simpa only [d181024, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25062 p hg
    simpa only [d181024, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181024, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24936 p hg
    simpa only [d181024, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25064 (p : Pattern) (guard : d16156 p = 1) : d47652 p ≤ (2 : Int) + d47652 p := by
  omega
theorem compare25065 (p : Pattern) (guard : d18711 p = 1) : d48567 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d16156 p = 1 := by simpa only [d18711, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25064 p hg
    simpa only [d18711, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18711, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24932 p hg
    simpa only [d18711, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25066 (p : Pattern) (guard : d181025 p = 1) : d48698 p ≤ (2 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d18711 p = 1 := by simpa only [d181025, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25065 p hg
    simpa only [d181025, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181025, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24934 p hg
    simpa only [d181025, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25067 (p : Pattern) (guard : d181026 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181025 p = 1 := by simpa only [d181026, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25066 p hg
    simpa only [d181026, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181026, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24936 p hg
    simpa only [d181026, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25068 (p : Pattern) (guard : d181027 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181024 p = 1 := by simpa only [d181027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25063 p hg
    simpa only [d181027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181026 p = 1 := by simpa only [d181027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25067 p hg
    simpa only [d181027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25069 (p : Pattern) (guard : d12858 p = 1) : d47652 p ≤ (2 : Int) + d47652 p := by
  omega
theorem compare25070 (p : Pattern) (guard : d18715 p = 1) : d48567 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d12858 p = 1 := by simpa only [d18715, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25069 p hg
    simpa only [d18715, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18715, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24932 p hg
    simpa only [d18715, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25071 (p : Pattern) (guard : d181028 p = 1) : d48698 p ≤ (2 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d18715 p = 1 := by simpa only [d181028, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25070 p hg
    simpa only [d181028, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181028, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24934 p hg
    simpa only [d181028, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25072 (p : Pattern) (guard : d181029 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181028 p = 1 := by simpa only [d181029, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25071 p hg
    simpa only [d181029, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181029, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24936 p hg
    simpa only [d181029, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25073 (p : Pattern) (guard : d971 p = 1) : d47652 p ≤ (2 : Int) + d47652 p := by
  omega
theorem compare25074 (p : Pattern) (guard : d18843 p = 1) : d48567 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d971 p = 1 := by simpa only [d18843, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25073 p hg
    simpa only [d18843, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18843, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24932 p hg
    simpa only [d18843, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25075 (p : Pattern) (guard : d181106 p = 1) : d48698 p ≤ (2 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d18843 p = 1 := by simpa only [d181106, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25074 p hg
    simpa only [d181106, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181106, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24934 p hg
    simpa only [d181106, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25076 (p : Pattern) (guard : d181107 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181106 p = 1 := by simpa only [d181107, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25075 p hg
    simpa only [d181107, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181107, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24936 p hg
    simpa only [d181107, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25077 (p : Pattern) (guard : d181108 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181029 p = 1 := by simpa only [d181108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25072 p hg
    simpa only [d181108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181107 p = 1 := by simpa only [d181108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25076 p hg
    simpa only [d181108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25078 (p : Pattern) (guard : d181109 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d181027 p = 1 := by simpa only [d181109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25068 p hg
    simpa only [d181109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181108 p = 1 := by simpa only [d181109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25077 p hg
    simpa only [d181109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25079 (p : Pattern) (guard : d181119 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d180975 p = 1 := by simpa only [d181119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25012 p hg
    simpa only [d181119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181107 p = 1 := by simpa only [d181119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25076 p hg
    simpa only [d181119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25080 (p : Pattern) (guard : d181113 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181107 p = 1 := by simpa only [d181113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25076 p hg
    simpa only [d181113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24938 p hg
    simpa only [d181113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25081 (p : Pattern) (guard : d181120 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d181119 p = 1 := by simpa only [d181120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25079 p hg
    simpa only [d181120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181113 p = 1 := by simpa only [d181120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25080 p hg
    simpa only [d181120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25082 (p : Pattern) (guard : d181121 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 157 with
  | false =>
    have hg : d181109 p = 1 := by simpa only [d181121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25078 p hg
    simpa only [d181121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181120 p = 1 := by simpa only [d181121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25081 p hg
    simpa only [d181121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25083 (p : Pattern) (guard : d181122 p = 1) : d48702 p ≤ (2 : Int) + d130449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181122, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24930 p hg
    simpa only [d181122, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181121 p = 1 := by simpa only [d181122, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25082 p hg
    simpa only [d181122, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25084 (p : Pattern) (guard : d181123 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181123, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24929 p hg
    simpa only [d181123, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181122 p = 1 := by simpa only [d181123, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25083 p hg
    simpa only [d181123, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25085 (p : Pattern) (guard : d181124 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d181113 p = 1 := by simpa only [d181124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25080 p hg
    simpa only [d181124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24938 p hg
    simpa only [d181124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25086 (p : Pattern) (guard : d181125 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 157 with
  | false =>
    have hg : d181120 p = 1 := by simpa only [d181125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25081 p hg
    simpa only [d181125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181124 p = 1 := by simpa only [d181125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25085 p hg
    simpa only [d181125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25087 (p : Pattern) (guard : d181126 p = 1) : d48702 p ≤ (2 : Int) + d130449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181126, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24930 p hg
    simpa only [d181126, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181125 p = 1 := by simpa only [d181126, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25086 p hg
    simpa only [d181126, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25088 (p : Pattern) (guard : d181127 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181127, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24929 p hg
    simpa only [d181127, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181126 p = 1 := by simpa only [d181127, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25087 p hg
    simpa only [d181127, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25089 (p : Pattern) (guard : d181128 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 136 with
  | false =>
    have hg : d181123 p = 1 := by simpa only [d181128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25084 p hg
    simpa only [d181128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181127 p = 1 := by simpa only [d181128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25088 p hg
    simpa only [d181128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25090 (p : Pattern) (guard : d181133 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 136 with
  | false =>
    have hg : d181127 p = 1 := by simpa only [d181133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25088 p hg
    simpa only [d181133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24944 p hg
    simpa only [d181133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25091 (p : Pattern) (guard : d181134 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 135 with
  | false =>
    have hg : d181128 p = 1 := by simpa only [d181134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25089 p hg
    simpa only [d181134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181133 p = 1 := by simpa only [d181134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25090 p hg
    simpa only [d181134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25092 (p : Pattern) (guard : d181135 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 119 with
  | false =>
    have hg : d181134 p = 1 := by simpa only [d181135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25091 p hg
    simpa only [d181135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24944 p hg
    simpa only [d181135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25093 (p : Pattern) (guard : d181136 p = 1) : d48705 p ≤ (2 : Int) + d130452 p := by
  cases selected : p 116 with
  | false =>
    have hg : d181135 p = 1 := by simpa only [d181136, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25092 p hg
    simpa only [d181136, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181136, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24948 p hg
    simpa only [d181136, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25094 (p : Pattern) (guard : d181137 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181137, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24928 p hg
    simpa only [d181137, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181136 p = 1 := by simpa only [d181137, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25093 p hg
    simpa only [d181137, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25095 (p : Pattern) (guard : d181142 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 135 with
  | false =>
    have hg : d181133 p = 1 := by simpa only [d181142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25090 p hg
    simpa only [d181142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24944 p hg
    simpa only [d181142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25096 (p : Pattern) (guard : d181143 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 119 with
  | false =>
    have hg : d181142 p = 1 := by simpa only [d181143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25095 p hg
    simpa only [d181143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24944 p hg
    simpa only [d181143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25097 (p : Pattern) (guard : d181144 p = 1) : d48705 p ≤ (2 : Int) + d130452 p := by
  cases selected : p 116 with
  | false =>
    have hg : d181143 p = 1 := by simpa only [d181144, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25096 p hg
    simpa only [d181144, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181144, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24948 p hg
    simpa only [d181144, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25098 (p : Pattern) (guard : d181145 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181145, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24928 p hg
    simpa only [d181145, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181144 p = 1 := by simpa only [d181145, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25097 p hg
    simpa only [d181145, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25099 (p : Pattern) (guard : d181146 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 113 with
  | false =>
    have hg : d181137 p = 1 := by simpa only [d181146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25094 p hg
    simpa only [d181146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181145 p = 1 := by simpa only [d181146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25098 p hg
    simpa only [d181146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25100 (p : Pattern) (guard : d181147 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 96 with
  | false =>
    have hg : d181146 p = 1 := by simpa only [d181147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25099 p hg
    simpa only [d181147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25101 (p : Pattern) (guard : d181148 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 95 with
  | false =>
    have hg : d181147 p = 1 := by simpa only [d181148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25100 p hg
    simpa only [d181148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25102 (p : Pattern) (guard : d181149 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 93 with
  | false =>
    have hg : d181148 p = 1 := by simpa only [d181149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25101 p hg
    simpa only [d181149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25103 (p : Pattern) (guard : d181163 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 113 with
  | false =>
    have hg : d181145 p = 1 := by simpa only [d181163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25098 p hg
    simpa only [d181163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25104 (p : Pattern) (guard : d181164 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 96 with
  | false =>
    have hg : d181163 p = 1 := by simpa only [d181164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25103 p hg
    simpa only [d181164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25105 (p : Pattern) (guard : d181165 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 95 with
  | false =>
    have hg : d181164 p = 1 := by simpa only [d181165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25104 p hg
    simpa only [d181165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25106 (p : Pattern) (guard : d181166 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 93 with
  | false =>
    have hg : d181165 p = 1 := by simpa only [d181166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25105 p hg
    simpa only [d181166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25107 (p : Pattern) (guard : d181656 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 91 with
  | false =>
    have hg : d181149 p = 1 := by simpa only [d181656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25102 p hg
    simpa only [d181656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181166 p = 1 := by simpa only [d181656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25106 p hg
    simpa only [d181656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25108 (p : Pattern) (guard : d181657 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181656 p = 1 := by simpa only [d181657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25107 p hg
    simpa only [d181657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25109 (p : Pattern) (guard : d181658 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 89 with
  | false =>
    have hg : d181657 p = 1 := by simpa only [d181658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25108 p hg
    simpa only [d181658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25110 (p : Pattern) (guard : d181659 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181658 p = 1 := by simpa only [d181659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25109 p hg
    simpa only [d181659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25111 (p : Pattern) (guard : d181660 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181659 p = 1 := by simpa only [d181660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25110 p hg
    simpa only [d181660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25112 (p : Pattern) (guard : d181661 p = 1) : d48707 p ≤ (2 : Int) + d130454 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181661, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24926 p hg
    simpa only [d181661, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181660 p = 1 := by simpa only [d181661, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25111 p hg
    simpa only [d181661, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25113 (p : Pattern) (guard : d181662 p = 1) : d48707 p ≤ (2 : Int) + d130454 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24925 p hg
    simpa only [d181662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181661 p = 1 := by simpa only [d181662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25112 p hg
    simpa only [d181662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25114 (p : Pattern) (guard : d181663 p = 1) : d48707 p ≤ (2 : Int) + d130454 p := by
  cases selected : p 69 with
  | false =>
    have hg : d181662 p = 1 := by simpa only [d181663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25113 p hg
    simpa only [d181663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24925 p hg
    simpa only [d181663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25115 (p : Pattern) (guard : d181664 p = 1) : d48707 p ≤ (2 : Int) + d130454 p := by
  cases selected : p 51 with
  | false =>
    have hg : d181663 p = 1 := by simpa only [d181664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25114 p hg
    simpa only [d181664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24925 p hg
    simpa only [d181664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25116 (p : Pattern) (guard : d181665 p = 1) : d48707 p ≤ (2 : Int) + d130454 p := by
  cases selected : p 50 with
  | false =>
    have hg : d181664 p = 1 := by simpa only [d181665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25115 p hg
    simpa only [d181665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24925 p hg
    simpa only [d181665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25117 (p : Pattern) (guard : d181666 p = 1) : d48748 p ≤ (2 : Int) + d130478 p := by
  cases selected : p 49 with
  | false =>
    have hg : d181665 p = 1 := by simpa only [d181666, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25116 p hg
    simpa only [d181666, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181666, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24965 p hg
    simpa only [d181666, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25118 (p : Pattern) (guard : d181667 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181667, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24924 p hg
    simpa only [d181667, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181666 p = 1 := by simpa only [d181667, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25117 p hg
    simpa only [d181667, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25119 (p : Pattern) (guard : d181668 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181667 p = 1 := by simpa only [d181668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25118 p hg
    simpa only [d181668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25120 (p : Pattern) (guard : d181669 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181668 p = 1 := by simpa only [d181669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25119 p hg
    simpa only [d181669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25121 (p : Pattern) (guard : d181670 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181669 p = 1 := by simpa only [d181670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25120 p hg
    simpa only [d181670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25122 (p : Pattern) (guard : d181671 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181670 p = 1 := by simpa only [d181671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25121 p hg
    simpa only [d181671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25123 (p : Pattern) (guard : d181672 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181671 p = 1 := by simpa only [d181672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25122 p hg
    simpa only [d181672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25124 (p : Pattern) (guard : d181673 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181672 p = 1 := by simpa only [d181673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25123 p hg
    simpa only [d181673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25125 (p : Pattern) (guard : d181674 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181673 p = 1 := by simpa only [d181674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25124 p hg
    simpa only [d181674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25126 (p : Pattern) (guard : d181675 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d181655 p = 1 := by simpa only [d181675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25059 p hg
    simpa only [d181675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181674 p = 1 := by simpa only [d181675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25125 p hg
    simpa only [d181675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25127 (p : Pattern) (guard : d1380 p = 1) : d47652 p ≤ (2 : Int) + d47652 p := by
  omega
theorem compare25128 (p : Pattern) (guard : d19006 p = 1) : d48567 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1380 p = 1 := by simpa only [d19006, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25127 p hg
    simpa only [d19006, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19006, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24932 p hg
    simpa only [d19006, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25129 (p : Pattern) (guard : d181198 p = 1) : d48698 p ≤ (2 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19006 p = 1 := by simpa only [d181198, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25128 p hg
    simpa only [d181198, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181198, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24934 p hg
    simpa only [d181198, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25130 (p : Pattern) (guard : d181199 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181198 p = 1 := by simpa only [d181199, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25129 p hg
    simpa only [d181199, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181199, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24936 p hg
    simpa only [d181199, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25131 (p : Pattern) (guard : d16656 p = 1) : d47652 p ≤ (2 : Int) + d47652 p := by
  omega
theorem compare25132 (p : Pattern) (guard : d19009 p = 1) : d48567 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d16656 p = 1 := by simpa only [d19009, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25131 p hg
    simpa only [d19009, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19009, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24932 p hg
    simpa only [d19009, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25133 (p : Pattern) (guard : d181200 p = 1) : d48698 p ≤ (2 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19009 p = 1 := by simpa only [d181200, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25132 p hg
    simpa only [d181200, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181200, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24934 p hg
    simpa only [d181200, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25134 (p : Pattern) (guard : d181201 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181200 p = 1 := by simpa only [d181201, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25133 p hg
    simpa only [d181201, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181201, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24936 p hg
    simpa only [d181201, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25135 (p : Pattern) (guard : d181202 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181199 p = 1 := by simpa only [d181202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25130 p hg
    simpa only [d181202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181201 p = 1 := by simpa only [d181202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25134 p hg
    simpa only [d181202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25136 (p : Pattern) (guard : d14994 p = 1) : d47652 p ≤ (2 : Int) + d47652 p := by
  omega
theorem compare25137 (p : Pattern) (guard : d19001 p = 1) : d48567 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d14994 p = 1 := by simpa only [d19001, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25136 p hg
    simpa only [d19001, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19001, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24932 p hg
    simpa only [d19001, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25138 (p : Pattern) (guard : d181194 p = 1) : d48698 p ≤ (2 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19001 p = 1 := by simpa only [d181194, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25137 p hg
    simpa only [d181194, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181194, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24934 p hg
    simpa only [d181194, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25139 (p : Pattern) (guard : d181195 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181194 p = 1 := by simpa only [d181195, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25138 p hg
    simpa only [d181195, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181195, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24936 p hg
    simpa only [d181195, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25140 (p : Pattern) (guard : d15004 p = 1) : d47652 p ≤ (2 : Int) + d47652 p := by
  omega
theorem compare25141 (p : Pattern) (guard : d19013 p = 1) : d48567 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d15004 p = 1 := by simpa only [d19013, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25140 p hg
    simpa only [d19013, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19013, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24932 p hg
    simpa only [d19013, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25142 (p : Pattern) (guard : d181203 p = 1) : d48698 p ≤ (2 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19013 p = 1 := by simpa only [d181203, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25141 p hg
    simpa only [d181203, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181203, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24934 p hg
    simpa only [d181203, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25143 (p : Pattern) (guard : d181204 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181203 p = 1 := by simpa only [d181204, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25142 p hg
    simpa only [d181204, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181204, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24936 p hg
    simpa only [d181204, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25144 (p : Pattern) (guard : d181205 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181195 p = 1 := by simpa only [d181205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25139 p hg
    simpa only [d181205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181204 p = 1 := by simpa only [d181205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25143 p hg
    simpa only [d181205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25145 (p : Pattern) (guard : d181206 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d181202 p = 1 := by simpa only [d181206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25135 p hg
    simpa only [d181206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181205 p = 1 := by simpa only [d181206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25144 p hg
    simpa only [d181206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25146 (p : Pattern) (guard : d1385 p = 1) : d47652 p ≤ (2 : Int) + d47652 p := by
  omega
theorem compare25147 (p : Pattern) (guard : d19031 p = 1) : d48567 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1385 p = 1 := by simpa only [d19031, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25146 p hg
    simpa only [d19031, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19031, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24932 p hg
    simpa only [d19031, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25148 (p : Pattern) (guard : d181219 p = 1) : d48698 p ≤ (2 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19031 p = 1 := by simpa only [d181219, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25147 p hg
    simpa only [d181219, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181219, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24934 p hg
    simpa only [d181219, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25149 (p : Pattern) (guard : d181220 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181219 p = 1 := by simpa only [d181220, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25148 p hg
    simpa only [d181220, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181220, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24936 p hg
    simpa only [d181220, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25150 (p : Pattern) (guard : d1391 p = 1) : d47652 p ≤ (2 : Int) + d47652 p := by
  omega
theorem compare25151 (p : Pattern) (guard : d19034 p = 1) : d48567 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1391 p = 1 := by simpa only [d19034, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25150 p hg
    simpa only [d19034, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19034, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24932 p hg
    simpa only [d19034, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25152 (p : Pattern) (guard : d181221 p = 1) : d48698 p ≤ (2 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19034 p = 1 := by simpa only [d181221, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25151 p hg
    simpa only [d181221, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181221, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24934 p hg
    simpa only [d181221, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25153 (p : Pattern) (guard : d181222 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181221 p = 1 := by simpa only [d181222, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25152 p hg
    simpa only [d181222, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181222, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24936 p hg
    simpa only [d181222, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25154 (p : Pattern) (guard : d181223 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181220 p = 1 := by simpa only [d181223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25149 p hg
    simpa only [d181223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181222 p = 1 := by simpa only [d181223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25153 p hg
    simpa only [d181223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25155 (p : Pattern) (guard : d181213 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181204 p = 1 := by simpa only [d181213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25143 p hg
    simpa only [d181213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24938 p hg
    simpa only [d181213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25156 (p : Pattern) (guard : d181224 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d181223 p = 1 := by simpa only [d181224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25154 p hg
    simpa only [d181224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181213 p = 1 := by simpa only [d181224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25155 p hg
    simpa only [d181224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25157 (p : Pattern) (guard : d181225 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 157 with
  | false =>
    have hg : d181206 p = 1 := by simpa only [d181225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25145 p hg
    simpa only [d181225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181224 p = 1 := by simpa only [d181225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25156 p hg
    simpa only [d181225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25158 (p : Pattern) (guard : d181226 p = 1) : d48702 p ≤ (2 : Int) + d130449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181226, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24930 p hg
    simpa only [d181226, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181225 p = 1 := by simpa only [d181226, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25157 p hg
    simpa only [d181226, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25159 (p : Pattern) (guard : d181227 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181227, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24929 p hg
    simpa only [d181227, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181226 p = 1 := by simpa only [d181227, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25158 p hg
    simpa only [d181227, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25160 (p : Pattern) (guard : d6350 p = 1) : d47652 p ≤ (2 : Int) + d47652 p := by
  omega
theorem compare25161 (p : Pattern) (guard : d19042 p = 1) : d48567 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d6350 p = 1 := by simpa only [d19042, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25160 p hg
    simpa only [d19042, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19042, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24932 p hg
    simpa only [d19042, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25162 (p : Pattern) (guard : d181228 p = 1) : d48698 p ≤ (2 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19042 p = 1 := by simpa only [d181228, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25161 p hg
    simpa only [d181228, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181228, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24934 p hg
    simpa only [d181228, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25163 (p : Pattern) (guard : d181229 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181228 p = 1 := by simpa only [d181229, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25162 p hg
    simpa only [d181229, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181229, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24936 p hg
    simpa only [d181229, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25164 (p : Pattern) (guard : d181230 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181229 p = 1 := by simpa only [d181230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25163 p hg
    simpa only [d181230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24938 p hg
    simpa only [d181230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25165 (p : Pattern) (guard : d15019 p = 1) : d47652 p ≤ (2 : Int) + d47652 p := by
  omega
theorem compare25166 (p : Pattern) (guard : d19046 p = 1) : d48567 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d15019 p = 1 := by simpa only [d19046, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25165 p hg
    simpa only [d19046, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19046, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24932 p hg
    simpa only [d19046, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25167 (p : Pattern) (guard : d181231 p = 1) : d48698 p ≤ (2 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19046 p = 1 := by simpa only [d181231, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25166 p hg
    simpa only [d181231, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181231, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24934 p hg
    simpa only [d181231, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25168 (p : Pattern) (guard : d181232 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181231 p = 1 := by simpa only [d181232, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25167 p hg
    simpa only [d181232, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181232, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24936 p hg
    simpa only [d181232, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25169 (p : Pattern) (guard : d181233 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181232 p = 1 := by simpa only [d181233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25168 p hg
    simpa only [d181233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24938 p hg
    simpa only [d181233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25170 (p : Pattern) (guard : d181234 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d181230 p = 1 := by simpa only [d181234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25164 p hg
    simpa only [d181234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181233 p = 1 := by simpa only [d181234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25169 p hg
    simpa only [d181234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25171 (p : Pattern) (guard : d181235 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 157 with
  | false =>
    have hg : d181224 p = 1 := by simpa only [d181235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25156 p hg
    simpa only [d181235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181234 p = 1 := by simpa only [d181235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25170 p hg
    simpa only [d181235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25172 (p : Pattern) (guard : d181236 p = 1) : d48702 p ≤ (2 : Int) + d130449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181236, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24930 p hg
    simpa only [d181236, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181235 p = 1 := by simpa only [d181236, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25171 p hg
    simpa only [d181236, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25173 (p : Pattern) (guard : d181237 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181237, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24929 p hg
    simpa only [d181237, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181236 p = 1 := by simpa only [d181237, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25172 p hg
    simpa only [d181237, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25174 (p : Pattern) (guard : d181238 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 136 with
  | false =>
    have hg : d181227 p = 1 := by simpa only [d181238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25159 p hg
    simpa only [d181238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181237 p = 1 := by simpa only [d181238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25173 p hg
    simpa only [d181238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25175 (p : Pattern) (guard : d181252 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181222 p = 1 := by simpa only [d181252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25153 p hg
    simpa only [d181252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24938 p hg
    simpa only [d181252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25176 (p : Pattern) (guard : d181253 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d181252 p = 1 := by simpa only [d181253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25175 p hg
    simpa only [d181253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181233 p = 1 := by simpa only [d181253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25169 p hg
    simpa only [d181253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25177 (p : Pattern) (guard : d181254 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 157 with
  | false =>
    have hg : d181224 p = 1 := by simpa only [d181254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25156 p hg
    simpa only [d181254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181253 p = 1 := by simpa only [d181254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25176 p hg
    simpa only [d181254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25178 (p : Pattern) (guard : d181255 p = 1) : d48702 p ≤ (2 : Int) + d130449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181255, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24930 p hg
    simpa only [d181255, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181254 p = 1 := by simpa only [d181255, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25177 p hg
    simpa only [d181255, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25179 (p : Pattern) (guard : d181256 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181256, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24929 p hg
    simpa only [d181256, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181255 p = 1 := by simpa only [d181256, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25178 p hg
    simpa only [d181256, d48703, d130450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25180 (p : Pattern) (guard : d181257 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 136 with
  | false =>
    have hg : d181256 p = 1 := by simpa only [d181257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25179 p hg
    simpa only [d181257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24944 p hg
    simpa only [d181257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25181 (p : Pattern) (guard : d181676 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 135 with
  | false =>
    have hg : d181238 p = 1 := by simpa only [d181676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25174 p hg
    simpa only [d181676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181257 p = 1 := by simpa only [d181676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25180 p hg
    simpa only [d181676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25182 (p : Pattern) (guard : d181677 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 119 with
  | false =>
    have hg : d181676 p = 1 := by simpa only [d181677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25181 p hg
    simpa only [d181677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24944 p hg
    simpa only [d181677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25183 (p : Pattern) (guard : d181678 p = 1) : d48705 p ≤ (2 : Int) + d130452 p := by
  cases selected : p 116 with
  | false =>
    have hg : d181677 p = 1 := by simpa only [d181678, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25182 p hg
    simpa only [d181678, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181678, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24948 p hg
    simpa only [d181678, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25184 (p : Pattern) (guard : d181679 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181679, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24928 p hg
    simpa only [d181679, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181678 p = 1 := by simpa only [d181679, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25183 p hg
    simpa only [d181679, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25185 (p : Pattern) (guard : d181258 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 135 with
  | false =>
    have hg : d181257 p = 1 := by simpa only [d181258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25180 p hg
    simpa only [d181258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24944 p hg
    simpa only [d181258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25186 (p : Pattern) (guard : d181259 p = 1) : d48703 p ≤ (2 : Int) + d130450 p := by
  cases selected : p 119 with
  | false =>
    have hg : d181258 p = 1 := by simpa only [d181259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25185 p hg
    simpa only [d181259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24944 p hg
    simpa only [d181259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25187 (p : Pattern) (guard : d181260 p = 1) : d48705 p ≤ (2 : Int) + d130452 p := by
  cases selected : p 116 with
  | false =>
    have hg : d181259 p = 1 := by simpa only [d181260, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25186 p hg
    simpa only [d181260, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181260, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24948 p hg
    simpa only [d181260, d48705, d130452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25188 (p : Pattern) (guard : d181261 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181261, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24928 p hg
    simpa only [d181261, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181260 p = 1 := by simpa only [d181261, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25187 p hg
    simpa only [d181261, d48706, d130453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25189 (p : Pattern) (guard : d181680 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 113 with
  | false =>
    have hg : d181679 p = 1 := by simpa only [d181680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25184 p hg
    simpa only [d181680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181261 p = 1 := by simpa only [d181680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25188 p hg
    simpa only [d181680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25190 (p : Pattern) (guard : d181681 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 96 with
  | false =>
    have hg : d181680 p = 1 := by simpa only [d181681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25189 p hg
    simpa only [d181681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25191 (p : Pattern) (guard : d181682 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 95 with
  | false =>
    have hg : d181681 p = 1 := by simpa only [d181682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25190 p hg
    simpa only [d181682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25192 (p : Pattern) (guard : d181683 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 93 with
  | false =>
    have hg : d181682 p = 1 := by simpa only [d181683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25191 p hg
    simpa only [d181683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25193 (p : Pattern) (guard : d181288 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 113 with
  | false =>
    have hg : d181261 p = 1 := by simpa only [d181288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25188 p hg
    simpa only [d181288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25194 (p : Pattern) (guard : d181289 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 96 with
  | false =>
    have hg : d181288 p = 1 := by simpa only [d181289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25193 p hg
    simpa only [d181289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25195 (p : Pattern) (guard : d181290 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 95 with
  | false =>
    have hg : d181289 p = 1 := by simpa only [d181290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25194 p hg
    simpa only [d181290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25196 (p : Pattern) (guard : d181291 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 93 with
  | false =>
    have hg : d181290 p = 1 := by simpa only [d181291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25195 p hg
    simpa only [d181291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25197 (p : Pattern) (guard : d181684 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 91 with
  | false =>
    have hg : d181683 p = 1 := by simpa only [d181684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25192 p hg
    simpa only [d181684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181291 p = 1 := by simpa only [d181684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25196 p hg
    simpa only [d181684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25198 (p : Pattern) (guard : d181685 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181684 p = 1 := by simpa only [d181685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25197 p hg
    simpa only [d181685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25199 (p : Pattern) (guard : d181686 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 89 with
  | false =>
    have hg : d181685 p = 1 := by simpa only [d181686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25198 p hg
    simpa only [d181686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25200 (p : Pattern) (guard : d181687 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181686 p = 1 := by simpa only [d181687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25199 p hg
    simpa only [d181687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25201 (p : Pattern) (guard : d181688 p = 1) : d48706 p ≤ (2 : Int) + d130453 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24927 p hg
    simpa only [d181688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181687 p = 1 := by simpa only [d181688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25200 p hg
    simpa only [d181688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25202 (p : Pattern) (guard : d181689 p = 1) : d48707 p ≤ (2 : Int) + d130454 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181689, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24926 p hg
    simpa only [d181689, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181688 p = 1 := by simpa only [d181689, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25201 p hg
    simpa only [d181689, d48707, d130454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25203 (p : Pattern) (guard : d181690 p = 1) : d48707 p ≤ (2 : Int) + d130454 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24925 p hg
    simpa only [d181690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181689 p = 1 := by simpa only [d181690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25202 p hg
    simpa only [d181690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25204 (p : Pattern) (guard : d181691 p = 1) : d48707 p ≤ (2 : Int) + d130454 p := by
  cases selected : p 69 with
  | false =>
    have hg : d181690 p = 1 := by simpa only [d181691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25203 p hg
    simpa only [d181691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24925 p hg
    simpa only [d181691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25205 (p : Pattern) (guard : d181692 p = 1) : d48707 p ≤ (2 : Int) + d130454 p := by
  cases selected : p 51 with
  | false =>
    have hg : d181691 p = 1 := by simpa only [d181692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25204 p hg
    simpa only [d181692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24925 p hg
    simpa only [d181692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25206 (p : Pattern) (guard : d181693 p = 1) : d48707 p ≤ (2 : Int) + d130454 p := by
  cases selected : p 50 with
  | false =>
    have hg : d181692 p = 1 := by simpa only [d181693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25205 p hg
    simpa only [d181693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24925 p hg
    simpa only [d181693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25207 (p : Pattern) (guard : d181694 p = 1) : d48748 p ≤ (2 : Int) + d130478 p := by
  cases selected : p 49 with
  | false =>
    have hg : d181693 p = 1 := by simpa only [d181694, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25206 p hg
    simpa only [d181694, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181694, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24965 p hg
    simpa only [d181694, d48748, d130478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25208 (p : Pattern) (guard : d181695 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181695, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24924 p hg
    simpa only [d181695, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181694 p = 1 := by simpa only [d181695, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25207 p hg
    simpa only [d181695, d48749, d130479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25209 (p : Pattern) (guard : d181696 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181695 p = 1 := by simpa only [d181696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25208 p hg
    simpa only [d181696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25210 (p : Pattern) (guard : d181697 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181696 p = 1 := by simpa only [d181697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25209 p hg
    simpa only [d181697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25211 (p : Pattern) (guard : d181698 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181697 p = 1 := by simpa only [d181698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25210 p hg
    simpa only [d181698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25212 (p : Pattern) (guard : d181699 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181698 p = 1 := by simpa only [d181699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25211 p hg
    simpa only [d181699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25213 (p : Pattern) (guard : d181700 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181699 p = 1 := by simpa only [d181700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25212 p hg
    simpa only [d181700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25214 (p : Pattern) (guard : d181701 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181700 p = 1 := by simpa only [d181701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25213 p hg
    simpa only [d181701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25215 (p : Pattern) (guard : d181702 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181701 p = 1 := by simpa only [d181702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25214 p hg
    simpa only [d181702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25216 (p : Pattern) (guard : d181703 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24923 p hg
    simpa only [d181703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181702 p = 1 := by simpa only [d181703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25215 p hg
    simpa only [d181703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25217 (p : Pattern) (guard : d181704 p = 1) : d48749 p ≤ (2 : Int) + d130479 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d181675 p = 1 := by simpa only [d181704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25126 p hg
    simpa only [d181704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181703 p = 1 := by simpa only [d181704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25216 p hg
    simpa only [d181704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25218 (p : Pattern) (guard : d1857 p = 1) : d47652 p ≤ (2 : Int) + d47652 p := by
  omega
theorem compare25219 (p : Pattern) (guard : d19238 p = 1) : d48567 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1857 p = 1 := by simpa only [d19238, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25218 p hg
    simpa only [d19238, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19238, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24932 p hg
    simpa only [d19238, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25220 (p : Pattern) (guard : d181324 p = 1) : d48698 p ≤ (2 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19238 p = 1 := by simpa only [d181324, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25219 p hg
    simpa only [d181324, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181324, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24934 p hg
    simpa only [d181324, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25221 (p : Pattern) (guard : d181325 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181324 p = 1 := by simpa only [d181325, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25220 p hg
    simpa only [d181325, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181325, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24936 p hg
    simpa only [d181325, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25222 (p : Pattern) (guard : d17011 p = 1) : d47652 p ≤ (2 : Int) + d47652 p := by
  omega
theorem compare25223 (p : Pattern) (guard : d19241 p = 1) : d48567 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d17011 p = 1 := by simpa only [d19241, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25222 p hg
    simpa only [d19241, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19241, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24932 p hg
    simpa only [d19241, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25224 (p : Pattern) (guard : d181326 p = 1) : d48698 p ≤ (2 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19241 p = 1 := by simpa only [d181326, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25223 p hg
    simpa only [d181326, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181326, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24934 p hg
    simpa only [d181326, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25225 (p : Pattern) (guard : d181327 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181326 p = 1 := by simpa only [d181327, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25224 p hg
    simpa only [d181327, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181327, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24936 p hg
    simpa only [d181327, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25226 (p : Pattern) (guard : d181328 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181325 p = 1 := by simpa only [d181328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25221 p hg
    simpa only [d181328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181327 p = 1 := by simpa only [d181328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25225 p hg
    simpa only [d181328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25227 (p : Pattern) (guard : d15387 p = 1) : d47652 p ≤ (2 : Int) + d47652 p := by
  omega
theorem compare25228 (p : Pattern) (guard : d19233 p = 1) : d48567 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d15387 p = 1 := by simpa only [d19233, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25227 p hg
    simpa only [d19233, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19233, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24932 p hg
    simpa only [d19233, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25229 (p : Pattern) (guard : d181320 p = 1) : d48698 p ≤ (2 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19233 p = 1 := by simpa only [d181320, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25228 p hg
    simpa only [d181320, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181320, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24934 p hg
    simpa only [d181320, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25230 (p : Pattern) (guard : d181321 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181320 p = 1 := by simpa only [d181321, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25229 p hg
    simpa only [d181321, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181321, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24936 p hg
    simpa only [d181321, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25231 (p : Pattern) (guard : d15397 p = 1) : d47652 p ≤ (2 : Int) + d47652 p := by
  omega
theorem compare25232 (p : Pattern) (guard : d19245 p = 1) : d48567 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d15397 p = 1 := by simpa only [d19245, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25231 p hg
    simpa only [d19245, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19245, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24932 p hg
    simpa only [d19245, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25233 (p : Pattern) (guard : d181329 p = 1) : d48698 p ≤ (2 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19245 p = 1 := by simpa only [d181329, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25232 p hg
    simpa only [d181329, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181329, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24934 p hg
    simpa only [d181329, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25234 (p : Pattern) (guard : d181330 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181329 p = 1 := by simpa only [d181330, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25233 p hg
    simpa only [d181330, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181330, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24936 p hg
    simpa only [d181330, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25235 (p : Pattern) (guard : d181331 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181321 p = 1 := by simpa only [d181331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25230 p hg
    simpa only [d181331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181330 p = 1 := by simpa only [d181331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25234 p hg
    simpa only [d181331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25236 (p : Pattern) (guard : d181332 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d181328 p = 1 := by simpa only [d181332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25226 p hg
    simpa only [d181332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181331 p = 1 := by simpa only [d181332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25235 p hg
    simpa only [d181332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25237 (p : Pattern) (guard : d1862 p = 1) : d47652 p ≤ (2 : Int) + d47652 p := by
  omega
theorem compare25238 (p : Pattern) (guard : d19263 p = 1) : d48567 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1862 p = 1 := by simpa only [d19263, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25237 p hg
    simpa only [d19263, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19263, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24932 p hg
    simpa only [d19263, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25239 (p : Pattern) (guard : d181345 p = 1) : d48698 p ≤ (2 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19263 p = 1 := by simpa only [d181345, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25238 p hg
    simpa only [d181345, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181345, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24934 p hg
    simpa only [d181345, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25240 (p : Pattern) (guard : d181346 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181345 p = 1 := by simpa only [d181346, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25239 p hg
    simpa only [d181346, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181346, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24936 p hg
    simpa only [d181346, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25241 (p : Pattern) (guard : d17027 p = 1) : d47652 p ≤ (2 : Int) + d47652 p := by
  omega
theorem compare25242 (p : Pattern) (guard : d19266 p = 1) : d48567 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 162 with
  | false =>
    have hg : d17027 p = 1 := by simpa only [d19266, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25241 p hg
    simpa only [d19266, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19266, d48567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24932 p hg
    simpa only [d19266, d48567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25243 (p : Pattern) (guard : d181347 p = 1) : d48698 p ≤ (2 : Int) + d130447 p := by
  cases selected : p 161 with
  | false =>
    have hg : d19266 p = 1 := by simpa only [d181347, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25242 p hg
    simpa only [d181347, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181347, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24934 p hg
    simpa only [d181347, d48698, d130447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25244 (p : Pattern) (guard : d181348 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 160 with
  | false =>
    have hg : d181347 p = 1 := by simpa only [d181348, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25243 p hg
    simpa only [d181348, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181348, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24936 p hg
    simpa only [d181348, d48701, d130448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25245 (p : Pattern) (guard : d181349 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181346 p = 1 := by simpa only [d181349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25240 p hg
    simpa only [d181349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181348 p = 1 := by simpa only [d181349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25244 p hg
    simpa only [d181349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25246 (p : Pattern) (guard : d181339 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 159 with
  | false =>
    have hg : d181330 p = 1 := by simpa only [d181339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25234 p hg
    simpa only [d181339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d181339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24938 p hg
    simpa only [d181339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25247 (p : Pattern) (guard : d181350 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 158 with
  | false =>
    have hg : d181349 p = 1 := by simpa only [d181350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25245 p hg
    simpa only [d181350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181339 p = 1 := by simpa only [d181350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25246 p hg
    simpa only [d181350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25248 (p : Pattern) (guard : d181351 p = 1) : d48701 p ≤ (2 : Int) + d130448 p := by
  cases selected : p 157 with
  | false =>
    have hg : d181332 p = 1 := by simpa only [d181351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25236 p hg
    simpa only [d181351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181350 p = 1 := by simpa only [d181351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25247 p hg
    simpa only [d181351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare25249 (p : Pattern) (guard : d181352 p = 1) : d48702 p ≤ (2 : Int) + d130449 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d181352, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24930 p hg
    simpa only [d181352, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d181351 p = 1 := by simpa only [d181352, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25248 p hg
    simpa only [d181352, d48702, d130449, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
