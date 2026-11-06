/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons064
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare9100 (p : Pattern) (guard : d985 p = 1) : d56 p ≤ (2 : Int) + d1006 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d56, d1006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9097 p hg
    simpa only [d56, d1006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d56, d1006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9099 p hg
    simpa only [d56, d1006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9101 (p : Pattern) (guard : d985 p = 1) : d57 p ≤ (2 : Int) + d1007 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d57, d1007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9097 p hg
    simpa only [d57, d1007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d57, d1007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9100 p hg
    simpa only [d57, d1007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9102 (p : Pattern) (guard : d985 p = 1) : d58 p ≤ (2 : Int) + d1008 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d58, d1008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9077 p hg
    simpa only [d58, d1008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d58, d1008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8740 p hg
    simpa only [d58, d1008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9103 (p : Pattern) (guard : d985 p = 1) : d59 p ≤ (2 : Int) + d1009 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d59, d1009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9078 p hg
    simpa only [d59, d1009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d59, d1009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9102 p hg
    simpa only [d59, d1009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9104 (p : Pattern) (guard : d985 p = 1) : d60 p ≤ (2 : Int) + d1010 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d60, d1010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9097 p hg
    simpa only [d60, d1010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d60, d1010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9103 p hg
    simpa only [d60, d1010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9105 (p : Pattern) (guard : d985 p = 1) : d61 p ≤ (2 : Int) + d701 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d61, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9082 p hg
    simpa only [d61, d701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d61, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8740 p hg
    simpa only [d61, d701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9106 (p : Pattern) (guard : d985 p = 1) : d62 p ≤ (2 : Int) + d702 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d62, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9085 p hg
    simpa only [d62, d702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d62, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9105 p hg
    simpa only [d62, d702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9107 (p : Pattern) (guard : d985 p = 1) : d63 p ≤ (2 : Int) + d1006 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d63, d1006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9106 p hg
    simpa only [d63, d1006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d63, d1006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9099 p hg
    simpa only [d63, d1006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9108 (p : Pattern) (guard : d985 p = 1) : d64 p ≤ (2 : Int) + d1011 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d64, d1011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9104 p hg
    simpa only [d64, d1011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d64, d1011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9107 p hg
    simpa only [d64, d1011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9109 (p : Pattern) (guard : d985 p = 1) : d65 p ≤ (2 : Int) + d1012 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d65, d1012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9101 p hg
    simpa only [d65, d1012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d65, d1012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9108 p hg
    simpa only [d65, d1012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9110 (p : Pattern) (guard : d985 p = 1) : d66 p ≤ (2 : Int) + d1013 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d66, d1013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9095 p hg
    simpa only [d66, d1013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d66, d1013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9109 p hg
    simpa only [d66, d1013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9111 (p : Pattern) (guard : d985 p = 1) : d67 p ≤ (2 : Int) + d1014 p := by
  cases selected : p 112 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d67, d1014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9089 p hg
    simpa only [d67, d1014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d67, d1014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9110 p hg
    simpa only [d67, d1014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9112 (p : Pattern) (guard : d985 p = 1) : d68 p ≤ (2 : Int) + d705 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d68, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9084 p hg
    simpa only [d68, d705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d68, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8740 p hg
    simpa only [d68, d705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9113 (p : Pattern) (guard : d985 p = 1) : d69 p ≤ (2 : Int) + d706 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d69, d706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9084 p hg
    simpa only [d69, d706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d69, d706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9112 p hg
    simpa only [d69, d706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9114 (p : Pattern) (guard : d985 p = 1) : d70 p ≤ (2 : Int) + d1015 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d70, d1015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9067 p hg
    simpa only [d70, d1015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d70, d1015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8740 p hg
    simpa only [d70, d1015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9115 (p : Pattern) (guard : d985 p = 1) : d71 p ≤ (2 : Int) + d1016 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d71, d1016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9067 p hg
    simpa only [d71, d1016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d71, d1016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9114 p hg
    simpa only [d71, d1016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9116 (p : Pattern) (guard : d985 p = 1) : d72 p ≤ (2 : Int) + d1017 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d72, d1017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9113 p hg
    simpa only [d72, d1017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d72, d1017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9115 p hg
    simpa only [d72, d1017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9117 (p : Pattern) (guard : d985 p = 1) : d73 p ≤ (2 : Int) + d1018 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d73, d1018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9070 p hg
    simpa only [d73, d1018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d73, d1018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9116 p hg
    simpa only [d73, d1018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9118 (p : Pattern) (guard : d985 p = 1) : d74 p ≤ (2 : Int) + d1019 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d74, d1019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9071 p hg
    simpa only [d74, d1019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d74, d1019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9117 p hg
    simpa only [d74, d1019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9119 (p : Pattern) (guard : d985 p = 1) : d75 p ≤ (2 : Int) + d1020 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d75, d1020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9112 p hg
    simpa only [d75, d1020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d75, d1020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9114 p hg
    simpa only [d75, d1020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9120 (p : Pattern) (guard : d985 p = 1) : d76 p ≤ (2 : Int) + d1021 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d76, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9070 p hg
    simpa only [d76, d1021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d76, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9119 p hg
    simpa only [d76, d1021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9121 (p : Pattern) (guard : d985 p = 1) : d77 p ≤ (2 : Int) + d1022 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d77, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9071 p hg
    simpa only [d77, d1022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d77, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9120 p hg
    simpa only [d77, d1022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9122 (p : Pattern) (guard : d985 p = 1) : d78 p ≤ (2 : Int) + d1023 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d78, d1023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9118 p hg
    simpa only [d78, d1023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d78, d1023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9121 p hg
    simpa only [d78, d1023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9123 (p : Pattern) (guard : d985 p = 1) : d79 p ≤ (2 : Int) + d1024 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d79, d1024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9090 p hg
    simpa only [d79, d1024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d79, d1024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9119 p hg
    simpa only [d79, d1024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9124 (p : Pattern) (guard : d985 p = 1) : d80 p ≤ (2 : Int) + d1025 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d80, d1025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9091 p hg
    simpa only [d80, d1025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d80, d1025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9123 p hg
    simpa only [d80, d1025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9125 (p : Pattern) (guard : d985 p = 1) : d81 p ≤ (2 : Int) + d1026 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d81, d1026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9100 p hg
    simpa only [d81, d1026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d81, d1026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9119 p hg
    simpa only [d81, d1026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9126 (p : Pattern) (guard : d985 p = 1) : d82 p ≤ (2 : Int) + d1027 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d82, d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9101 p hg
    simpa only [d82, d1027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d82, d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9125 p hg
    simpa only [d82, d1027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9127 (p : Pattern) (guard : d985 p = 1) : d83 p ≤ (2 : Int) + d1028 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d83, d1028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9124 p hg
    simpa only [d83, d1028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d83, d1028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9126 p hg
    simpa only [d83, d1028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9128 (p : Pattern) (guard : d985 p = 1) : d84 p ≤ (2 : Int) + d1029 p := by
  cases selected : p 112 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d84, d1029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9122 p hg
    simpa only [d84, d1029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d84, d1029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9127 p hg
    simpa only [d84, d1029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9129 (p : Pattern) (guard : d985 p = 1) : d85 p ≤ (2 : Int) + d1030 p := by
  cases selected : p 106 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d85, d1030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9111 p hg
    simpa only [d85, d1030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d85, d1030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9128 p hg
    simpa only [d85, d1030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9130 (p : Pattern) (guard : d985 p = 1) : d86 p ≤ (2 : Int) + d719 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d86, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9051 p hg
    simpa only [d86, d719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d86, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9096 p hg
    simpa only [d86, d719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9131 (p : Pattern) (guard : d985 p = 1) : d87 p ≤ (2 : Int) + d1031 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d87, d1031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9063 p hg
    simpa only [d87, d1031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d87, d1031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9098 p hg
    simpa only [d87, d1031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9132 (p : Pattern) (guard : d985 p = 1) : d88 p ≤ (2 : Int) + d1032 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d88, d1032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9130 p hg
    simpa only [d88, d1032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d88, d1032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9131 p hg
    simpa only [d88, d1032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9133 (p : Pattern) (guard : d985 p = 1) : d89 p ≤ (2 : Int) + d1033 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d89, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9130 p hg
    simpa only [d89, d1033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d89, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9132 p hg
    simpa only [d89, d1033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9134 (p : Pattern) (guard : d985 p = 1) : d90 p ≤ (2 : Int) + d1034 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d90, d1034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9077 p hg
    simpa only [d90, d1034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d90, d1034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9102 p hg
    simpa only [d90, d1034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9135 (p : Pattern) (guard : d985 p = 1) : d91 p ≤ (2 : Int) + d1035 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d91, d1035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9130 p hg
    simpa only [d91, d1035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d91, d1035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9134 p hg
    simpa only [d91, d1035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9136 (p : Pattern) (guard : d985 p = 1) : d92 p ≤ (2 : Int) + d719 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d92, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9082 p hg
    simpa only [d92, d719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d92, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9105 p hg
    simpa only [d92, d719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9137 (p : Pattern) (guard : d985 p = 1) : d93 p ≤ (2 : Int) + d1032 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d93, d1032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9136 p hg
    simpa only [d93, d1032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d93, d1032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9131 p hg
    simpa only [d93, d1032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9138 (p : Pattern) (guard : d985 p = 1) : d94 p ≤ (2 : Int) + d1036 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d94, d1036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9135 p hg
    simpa only [d94, d1036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d94, d1036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9137 p hg
    simpa only [d94, d1036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9139 (p : Pattern) (guard : d985 p = 1) : d95 p ≤ (2 : Int) + d1037 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d95, d1037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9133 p hg
    simpa only [d95, d1037, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d95, d1037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9138 p hg
    simpa only [d95, d1037, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9140 (p : Pattern) (guard : d985 p = 1) : d96 p ≤ (2 : Int) + d1038 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d96, d1038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9089 p hg
    simpa only [d96, d1038, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d96, d1038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9139 p hg
    simpa only [d96, d1038, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9141 (p : Pattern) (guard : d985 p = 1) : d97 p ≤ (2 : Int) + d705 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d97, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9057 p hg
    simpa only [d97, d705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d97, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8740 p hg
    simpa only [d97, d705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9142 (p : Pattern) (guard : d985 p = 1) : d98 p ≤ (2 : Int) + d706 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d98, d706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9057 p hg
    simpa only [d98, d706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d98, d706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9141 p hg
    simpa only [d98, d706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9143 (p : Pattern) (guard : d985 p = 1) : d99 p ≤ (2 : Int) + d1017 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d99, d1017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9142 p hg
    simpa only [d99, d1017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d99, d1017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9115 p hg
    simpa only [d99, d1017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9144 (p : Pattern) (guard : d985 p = 1) : d100 p ≤ (2 : Int) + d1039 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d100, d1039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9142 p hg
    simpa only [d100, d1039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d100, d1039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9143 p hg
    simpa only [d100, d1039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9145 (p : Pattern) (guard : d985 p = 1) : d101 p ≤ (2 : Int) + d1017 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9143 p hg
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9116 p hg
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9146 (p : Pattern) (guard : d985 p = 1) : d102 p ≤ (2 : Int) + d1040 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d102, d1040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9144 p hg
    simpa only [d102, d1040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d102, d1040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9145 p hg
    simpa only [d102, d1040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9147 (p : Pattern) (guard : d985 p = 1) : d103 p ≤ (2 : Int) + d1041 p := by
  cases selected : p 112 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d103, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9140 p hg
    simpa only [d103, d1041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d103, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9146 p hg
    simpa only [d103, d1041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9148 (p : Pattern) (guard : d985 p = 1) : d104 p ≤ (2 : Int) + d1042 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d104, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9132 p hg
    simpa only [d104, d1042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d104, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9119 p hg
    simpa only [d104, d1042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9149 (p : Pattern) (guard : d985 p = 1) : d105 p ≤ (2 : Int) + d1043 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d105, d1043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9133 p hg
    simpa only [d105, d1043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d105, d1043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9148 p hg
    simpa only [d105, d1043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9150 (p : Pattern) (guard : d985 p = 1) : d106 p ≤ (2 : Int) + d1044 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d106, d1044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9121 p hg
    simpa only [d106, d1044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d106, d1044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9149 p hg
    simpa only [d106, d1044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9151 (p : Pattern) (guard : d985 p = 1) : d107 p ≤ (2 : Int) + d1045 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d107, d1045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9143 p hg
    simpa only [d107, d1045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d107, d1045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8740 p hg
    simpa only [d107, d1045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9152 (p : Pattern) (guard : d985 p = 1) : d108 p ≤ (2 : Int) + d1046 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d108, d1046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9144 p hg
    simpa only [d108, d1046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d108, d1046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9151 p hg
    simpa only [d108, d1046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9153 (p : Pattern) (guard : d985 p = 1) : d109 p ≤ (2 : Int) + d1020 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d109, d1020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9141 p hg
    simpa only [d109, d1020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d109, d1020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9114 p hg
    simpa only [d109, d1020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9154 (p : Pattern) (guard : d985 p = 1) : d110 p ≤ (2 : Int) + d1047 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d110, d1047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9141 p hg
    simpa only [d110, d1047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d110, d1047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9153 p hg
    simpa only [d110, d1047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9155 (p : Pattern) (guard : d985 p = 1) : d111 p ≤ (2 : Int) + d1048 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d111, d1048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9153 p hg
    simpa only [d111, d1048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d111, d1048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8740 p hg
    simpa only [d111, d1048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9156 (p : Pattern) (guard : d985 p = 1) : d112 p ≤ (2 : Int) + d1049 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d112, d1049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9154 p hg
    simpa only [d112, d1049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d112, d1049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9155 p hg
    simpa only [d112, d1049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9157 (p : Pattern) (guard : d985 p = 1) : d113 p ≤ (2 : Int) + d1050 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d113, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9152 p hg
    simpa only [d113, d1050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d113, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9156 p hg
    simpa only [d113, d1050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9158 (p : Pattern) (guard : d985 p = 1) : d114 p ≤ (2 : Int) + d1051 p := by
  cases selected : p 112 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d114, d1051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9150 p hg
    simpa only [d114, d1051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d114, d1051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9157 p hg
    simpa only [d114, d1051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9159 (p : Pattern) (guard : d985 p = 1) : d115 p ≤ (2 : Int) + d1052 p := by
  cases selected : p 106 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d115, d1052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9147 p hg
    simpa only [d115, d1052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d115, d1052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9158 p hg
    simpa only [d115, d1052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9160 (p : Pattern) (guard : d985 p = 1) : d116 p ≤ (2 : Int) + d1053 p := by
  cases selected : p 86 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d116, d1053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9129 p hg
    simpa only [d116, d1053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d116, d1053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9159 p hg
    simpa only [d116, d1053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9161 (p : Pattern) (guard : d985 p = 1) : d117 p ≤ (2 : Int) + d1054 p := by
  cases selected : p 112 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d117, d1054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9121 p hg
    simpa only [d117, d1054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d117, d1054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9127 p hg
    simpa only [d117, d1054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9162 (p : Pattern) (guard : d985 p = 1) : d118 p ≤ (2 : Int) + d1055 p := by
  cases selected : p 106 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d118, d1055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9111 p hg
    simpa only [d118, d1055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d118, d1055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9161 p hg
    simpa only [d118, d1055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9163 (p : Pattern) (guard : d985 p = 1) : d119 p ≤ (2 : Int) + d1056 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d119, d1056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9077 p hg
    simpa only [d119, d1056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d119, d1056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9063 p hg
    simpa only [d119, d1056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9164 (p : Pattern) (guard : d985 p = 1) : d120 p ≤ (2 : Int) + d1057 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d120, d1057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9163 p hg
    simpa only [d120, d1057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d120, d1057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9102 p hg
    simpa only [d120, d1057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9165 (p : Pattern) (guard : d985 p = 1) : d121 p ≤ (2 : Int) + d1058 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d121, d1058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9130 p hg
    simpa only [d121, d1058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d121, d1058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9164 p hg
    simpa only [d121, d1058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9166 (p : Pattern) (guard : d985 p = 1) : d122 p ≤ (2 : Int) + d1059 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d122, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9165 p hg
    simpa only [d122, d1059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d122, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9137 p hg
    simpa only [d122, d1059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9167 (p : Pattern) (guard : d985 p = 1) : d123 p ≤ (2 : Int) + d1060 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d123, d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9133 p hg
    simpa only [d123, d1060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d123, d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9166 p hg
    simpa only [d123, d1060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9168 (p : Pattern) (guard : d985 p = 1) : d124 p ≤ (2 : Int) + d1061 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d124, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9089 p hg
    simpa only [d124, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d124, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9167 p hg
    simpa only [d124, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9169 (p : Pattern) (guard : d985 p = 1) : d125 p ≤ (2 : Int) + d1020 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9153 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9119 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9170 (p : Pattern) (guard : d985 p = 1) : d126 p ≤ (2 : Int) + d1062 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d126, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9154 p hg
    simpa only [d126, d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d126, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9169 p hg
    simpa only [d126, d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9171 (p : Pattern) (guard : d985 p = 1) : d127 p ≤ (2 : Int) + d1063 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d127, d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9146 p hg
    simpa only [d127, d1063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d127, d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9170 p hg
    simpa only [d127, d1063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9172 (p : Pattern) (guard : d985 p = 1) : d128 p ≤ (2 : Int) + d1064 p := by
  cases selected : p 112 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d128, d1064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9168 p hg
    simpa only [d128, d1064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d128, d1064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9171 p hg
    simpa only [d128, d1064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9173 (p : Pattern) (guard : d985 p = 1) : d129 p ≤ (2 : Int) + d1065 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d129, d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9121 p hg
    simpa only [d129, d1065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d129, d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9126 p hg
    simpa only [d129, d1065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9174 (p : Pattern) (guard : d985 p = 1) : d130 p ≤ (2 : Int) + d1066 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d130, d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9156 p hg
    simpa only [d130, d1066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d130, d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8740 p hg
    simpa only [d130, d1066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9175 (p : Pattern) (guard : d985 p = 1) : d131 p ≤ (2 : Int) + d1067 p := by
  cases selected : p 112 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d131, d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9173 p hg
    simpa only [d131, d1067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d131, d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9174 p hg
    simpa only [d131, d1067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9176 (p : Pattern) (guard : d985 p = 1) : d132 p ≤ (2 : Int) + d1068 p := by
  cases selected : p 106 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d132, d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9172 p hg
    simpa only [d132, d1068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d132, d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9175 p hg
    simpa only [d132, d1068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9177 (p : Pattern) (guard : d985 p = 1) : d133 p ≤ (2 : Int) + d1069 p := by
  cases selected : p 86 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d133, d1069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9162 p hg
    simpa only [d133, d1069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d133, d1069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9176 p hg
    simpa only [d133, d1069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9178 (p : Pattern) (guard : d985 p = 1) : d134 p ≤ (2 : Int) + d1070 p := by
  cases selected : p 80 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d134, d1070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9160 p hg
    simpa only [d134, d1070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d134, d1070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9177 p hg
    simpa only [d134, d1070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9179 (p : Pattern) (guard : d1088 p = 1) : d53 p ≤ (0 : Int) + d460 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d53, d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1794 p hg
    simpa only [d53, d460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d53, d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5813 p hg
    simpa only [d53, d460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9180 (p : Pattern) (guard : d1088 p = 1) : d53 p ≤ (0 : Int) + d52 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1581 p hg
    simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5813 p hg
    simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9181 (p : Pattern) (guard : d1088 p = 1) : d53 p ≤ (0 : Int) + d469 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9179 p hg
    simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9180 p hg
    simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9182 (p : Pattern) (guard : d1088 p = 1) : d55 p ≤ (0 : Int) + d54 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1593 p hg
    simpa only [d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5817 p hg
    simpa only [d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9183 (p : Pattern) (guard : d1088 p = 1) : d56 p ≤ (0 : Int) + d470 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d56, d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9180 p hg
    simpa only [d56, d470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d56, d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9182 p hg
    simpa only [d56, d470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9184 (p : Pattern) (guard : d1088 p = 1) : d57 p ≤ (0 : Int) + d471 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d57, d471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9181 p hg
    simpa only [d57, d471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d57, d471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9183 p hg
    simpa only [d57, d471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9185 (p : Pattern) (guard : d1088 p = 1) : d59 p ≤ (0 : Int) + d58 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1599 p hg
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5821 p hg
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9186 (p : Pattern) (guard : d1088 p = 1) : d60 p ≤ (0 : Int) + d472 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d60, d472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9179 p hg
    simpa only [d60, d472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d60, d472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9185 p hg
    simpa only [d60, d472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9187 (p : Pattern) (guard : d1088 p = 1) : d62 p ≤ (0 : Int) + d61 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1605 p hg
    simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5824 p hg
    simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9188 (p : Pattern) (guard : d1088 p = 1) : d63 p ≤ (0 : Int) + d473 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d63, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9187 p hg
    simpa only [d63, d473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d63, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9182 p hg
    simpa only [d63, d473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9189 (p : Pattern) (guard : d1088 p = 1) : d64 p ≤ (0 : Int) + d474 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d64, d474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9186 p hg
    simpa only [d64, d474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d64, d474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9188 p hg
    simpa only [d64, d474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9190 (p : Pattern) (guard : d1088 p = 1) : d65 p ≤ (0 : Int) + d475 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d65, d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9184 p hg
    simpa only [d65, d475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d65, d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9189 p hg
    simpa only [d65, d475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9191 (p : Pattern) (guard : d1088 p = 1) : d66 p ≤ (0 : Int) + d475 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1802 p hg
    simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9190 p hg
    simpa only [d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9192 (p : Pattern) (guard : d1088 p = 1) : d67 p ≤ (0 : Int) + d476 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d67, d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1609 p hg
    simpa only [d67, d476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d67, d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9191 p hg
    simpa only [d67, d476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9193 (p : Pattern) (guard : d1088 p = 1) : d78 p ≤ (0 : Int) + d488 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d78, d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1640 p hg
    simpa only [d78, d488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d78, d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1679 p hg
    simpa only [d78, d488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9194 (p : Pattern) (guard : d1088 p = 1) : d81 p ≤ (0 : Int) + d491 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d81, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9183 p hg
    simpa only [d81, d491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d81, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1677 p hg
    simpa only [d81, d491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9195 (p : Pattern) (guard : d1088 p = 1) : d82 p ≤ (0 : Int) + d492 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d82, d492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9184 p hg
    simpa only [d82, d492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d82, d492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9194 p hg
    simpa only [d82, d492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9196 (p : Pattern) (guard : d1088 p = 1) : d83 p ≤ (0 : Int) + d493 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d83, d493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1809 p hg
    simpa only [d83, d493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d83, d493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9195 p hg
    simpa only [d83, d493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9197 (p : Pattern) (guard : d1088 p = 1) : d84 p ≤ (0 : Int) + d494 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d84, d494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9193 p hg
    simpa only [d84, d494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d84, d494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9196 p hg
    simpa only [d84, d494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9198 (p : Pattern) (guard : d1088 p = 1) : d85 p ≤ (0 : Int) + d495 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d85, d495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9192 p hg
    simpa only [d85, d495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d85, d495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9197 p hg
    simpa only [d85, d495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9199 (p : Pattern) (guard : d1088 p = 1) : d86 p ≤ (0 : Int) + d457 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d86, d457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1579 p hg
    simpa only [d86, d457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d86, d457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5813 p hg
    simpa only [d86, d457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9200 (p : Pattern) (guard : d1088 p = 1) : d86 p ≤ (0 : Int) + d52 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1584 p hg
    simpa only [d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5813 p hg
    simpa only [d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9201 (p : Pattern) (guard : d1088 p = 1) : d86 p ≤ (0 : Int) + d458 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9199 p hg
    simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9200 p hg
    simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9202 (p : Pattern) (guard : d1088 p = 1) : d86 p ≤ (0 : Int) + d460 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d86, d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1588 p hg
    simpa only [d86, d460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d86, d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5813 p hg
    simpa only [d86, d460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9203 (p : Pattern) (guard : d1088 p = 1) : d87 p ≤ (0 : Int) + d54 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1591 p hg
    simpa only [d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5817 p hg
    simpa only [d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9204 (p : Pattern) (guard : d1088 p = 1) : d88 p ≤ (0 : Int) + d461 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d88, d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9202 p hg
    simpa only [d88, d461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d88, d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9203 p hg
    simpa only [d88, d461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9205 (p : Pattern) (guard : d1088 p = 1) : d89 p ≤ (0 : Int) + d462 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d89, d462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9201 p hg
    simpa only [d89, d462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d89, d462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9204 p hg
    simpa only [d89, d462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9206 (p : Pattern) (guard : d1088 p = 1) : d86 p ≤ (0 : Int) + d484 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d86, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1642 p hg
    simpa only [d86, d484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d86, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5813 p hg
    simpa only [d86, d484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9207 (p : Pattern) (guard : d1088 p = 1) : d90 p ≤ (0 : Int) + d58 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1598 p hg
    simpa only [d90, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5821 p hg
    simpa only [d90, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9208 (p : Pattern) (guard : d1088 p = 1) : d91 p ≤ (0 : Int) + d496 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d91, d496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9206 p hg
    simpa only [d91, d496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d91, d496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9207 p hg
    simpa only [d91, d496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9209 (p : Pattern) (guard : d1088 p = 1) : d92 p ≤ (0 : Int) + d61 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1666 p hg
    simpa only [d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5824 p hg
    simpa only [d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9210 (p : Pattern) (guard : d1088 p = 1) : d93 p ≤ (0 : Int) + d473 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d93, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9209 p hg
    simpa only [d93, d473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d93, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9203 p hg
    simpa only [d93, d473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9211 (p : Pattern) (guard : d1088 p = 1) : d94 p ≤ (0 : Int) + d497 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d94, d497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9208 p hg
    simpa only [d94, d497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d94, d497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9210 p hg
    simpa only [d94, d497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9212 (p : Pattern) (guard : d1088 p = 1) : d95 p ≤ (0 : Int) + d498 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d95, d498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9205 p hg
    simpa only [d95, d498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d95, d498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9211 p hg
    simpa only [d95, d498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9213 (p : Pattern) (guard : d1088 p = 1) : d96 p ≤ (0 : Int) + d499 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d96, d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1609 p hg
    simpa only [d96, d499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d96, d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9212 p hg
    simpa only [d96, d499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9214 (p : Pattern) (guard : d1088 p = 1) : d102 p ≤ (0 : Int) + d508 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1830 p hg
    simpa only [d508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1856 p hg
    simpa only [d508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9215 (p : Pattern) (guard : d1088 p = 1) : d103 p ≤ (0 : Int) + d509 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d103, d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9213 p hg
    simpa only [d103, d509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d103, d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9214 p hg
    simpa only [d103, d509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9216 (p : Pattern) (guard : d1088 p = 1) : d86 p ≤ (0 : Int) + d510 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9206 p hg
    simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9200 p hg
    simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9217 (p : Pattern) (guard : d1088 p = 1) : d88 p ≤ (0 : Int) + d470 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d88, d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9200 p hg
    simpa only [d88, d470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d88, d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9203 p hg
    simpa only [d88, d470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9218 (p : Pattern) (guard : d1088 p = 1) : d89 p ≤ (0 : Int) + d511 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d89, d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9216 p hg
    simpa only [d89, d511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d89, d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9217 p hg
    simpa only [d89, d511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9219 (p : Pattern) (guard : d1088 p = 1) : d104 p ≤ (0 : Int) + d491 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d104, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9217 p hg
    simpa only [d104, d491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d104, d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1677 p hg
    simpa only [d104, d491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9220 (p : Pattern) (guard : d1088 p = 1) : d105 p ≤ (0 : Int) + d512 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d105, d512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9218 p hg
    simpa only [d105, d512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d105, d512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9219 p hg
    simpa only [d105, d512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9221 (p : Pattern) (guard : d1088 p = 1) : d106 p ≤ (0 : Int) + d513 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d106, d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1679 p hg
    simpa only [d106, d513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d106, d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9220 p hg
    simpa only [d106, d513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9222 (p : Pattern) (guard : d1088 p = 1) : d113 p ≤ (0 : Int) + d515 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d113, d515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1838 p hg
    simpa only [d113, d515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d113, d515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5860 p hg
    simpa only [d113, d515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9223 (p : Pattern) (guard : d1088 p = 1) : d114 p ≤ (0 : Int) + d516 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d114, d516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9221 p hg
    simpa only [d114, d516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d114, d516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9222 p hg
    simpa only [d114, d516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9224 (p : Pattern) (guard : d1088 p = 1) : d115 p ≤ (0 : Int) + d517 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d115, d517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9215 p hg
    simpa only [d115, d517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d115, d517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9223 p hg
    simpa only [d115, d517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9225 (p : Pattern) (guard : d1088 p = 1) : d116 p ≤ (0 : Int) + d518 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d116, d518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9198 p hg
    simpa only [d116, d518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d116, d518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9224 p hg
    simpa only [d116, d518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9226 (p : Pattern) (guard : d1088 p = 1) : d45 p ≤ (0 : Int) + d499 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1609 p hg
    simpa only [d499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1716 p hg
    simpa only [d499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9227 (p : Pattern) (guard : d1088 p = 1) : d60 p ≤ (0 : Int) + d519 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d60, d519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9180 p hg
    simpa only [d60, d519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d60, d519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9185 p hg
    simpa only [d60, d519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9228 (p : Pattern) (guard : d1088 p = 1) : d64 p ≤ (0 : Int) + d520 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d64, d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9227 p hg
    simpa only [d64, d520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d64, d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9188 p hg
    simpa only [d64, d520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9229 (p : Pattern) (guard : d1088 p = 1) : d65 p ≤ (0 : Int) + d521 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d65, d521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9184 p hg
    simpa only [d65, d521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d65, d521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9228 p hg
    simpa only [d65, d521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9230 (p : Pattern) (guard : d1088 p = 1) : d66 p ≤ (0 : Int) + d522 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d66, d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1802 p hg
    simpa only [d66, d522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d66, d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9229 p hg
    simpa only [d66, d522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9231 (p : Pattern) (guard : d1088 p = 1) : d67 p ≤ (0 : Int) + d523 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d67, d523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9226 p hg
    simpa only [d67, d523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d67, d523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9230 p hg
    simpa only [d67, d523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9232 (p : Pattern) (guard : d1088 p = 1) : d77 p ≤ (0 : Int) + d513 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1679 p hg
    simpa only [d513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1729 p hg
    simpa only [d513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9233 (p : Pattern) (guard : d1088 p = 1) : d57 p ≤ (0 : Int) + d524 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d57, d524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9180 p hg
    simpa only [d57, d524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d57, d524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9183 p hg
    simpa only [d57, d524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9234 (p : Pattern) (guard : d1088 p = 1) : d82 p ≤ (0 : Int) + d525 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d82, d525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9233 p hg
    simpa only [d82, d525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d82, d525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9194 p hg
    simpa only [d82, d525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9235 (p : Pattern) (guard : d1088 p = 1) : d83 p ≤ (0 : Int) + d526 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d83, d526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1848 p hg
    simpa only [d83, d526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d83, d526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9234 p hg
    simpa only [d83, d526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9236 (p : Pattern) (guard : d1088 p = 1) : d117 p ≤ (0 : Int) + d527 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d117, d527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9232 p hg
    simpa only [d117, d527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d117, d527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9235 p hg
    simpa only [d117, d527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9237 (p : Pattern) (guard : d1088 p = 1) : d118 p ≤ (0 : Int) + d528 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d118, d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9231 p hg
    simpa only [d118, d528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d118, d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9236 p hg
    simpa only [d118, d528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9238 (p : Pattern) (guard : d1088 p = 1) : d120 p ≤ (0 : Int) + d58 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1717 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5821 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9239 (p : Pattern) (guard : d1088 p = 1) : d121 p ≤ (0 : Int) + d519 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d121, d519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9200 p hg
    simpa only [d121, d519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1088 p = 1 := by simpa only [d121, d519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9238 p hg
    simpa only [d121, d519, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
