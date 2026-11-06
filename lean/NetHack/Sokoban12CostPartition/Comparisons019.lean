/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons018
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare2660 (p : Pattern) (guard : d853 p = 1) : d62 p ≤ (2 : Int) + d1057 p := by
  cases selected : p 168 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d62, d1057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2648 p hg
    simpa only [d62, d1057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d62, d1057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2659 p hg
    simpa only [d62, d1057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2661 (p : Pattern) (guard : d853 p = 1) : d63 p ≤ (2 : Int) + d1058 p := by
  cases selected : p 160 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d63, d1058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2654 p hg
    simpa only [d63, d1058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d63, d1058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2660 p hg
    simpa only [d63, d1058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2662 (p : Pattern) (guard : d853 p = 1) : d64 p ≤ (2 : Int) + d1059 p := by
  cases selected : p 141 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d64, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2649 p hg
    simpa only [d64, d1059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d64, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2661 p hg
    simpa only [d64, d1059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2663 (p : Pattern) (guard : d853 p = 1) : d106 p ≤ (2 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d106, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2643 p hg
    simpa only [d106, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d106, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2647 p hg
    simpa only [d106, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2664 (p : Pattern) (guard : d853 p = 1) : d119 p ≤ (2 : Int) + d82 p := by
  cases selected : p 187 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d119, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2643 p hg
    simpa only [d119, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d119, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2647 p hg
    simpa only [d119, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2665 (p : Pattern) (guard : d853 p = 1) : d120 p ≤ (2 : Int) + d83 p := by
  cases selected : p 186 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d120, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2643 p hg
    simpa only [d120, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d120, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2664 p hg
    simpa only [d120, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2666 (p : Pattern) (guard : d853 p = 1) : d121 p ≤ (2 : Int) + d84 p := by
  cases selected : p 160 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d121, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2665 p hg
    simpa only [d121, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d121, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2647 p hg
    simpa only [d121, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2667 (p : Pattern) (guard : d853 p = 1) : d122 p ≤ (2 : Int) + d85 p := by
  cases selected : p 159 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d122, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2663 p hg
    simpa only [d122, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d122, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2666 p hg
    simpa only [d122, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2668 (p : Pattern) (guard : d853 p = 1) : d179 p ≤ (2 : Int) + d162 p := by
  cases selected : p 158 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d179, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2663 p hg
    simpa only [d179, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d179, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2667 p hg
    simpa only [d179, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2669 (p : Pattern) (guard : d853 p = 1) : d65 p ≤ (2 : Int) + d1060 p := by
  cases selected : p 168 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d65, d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2647 p hg
    simpa only [d65, d1060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d65, d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2658 p hg
    simpa only [d65, d1060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2670 (p : Pattern) (guard : d853 p = 1) : d109 p ≤ (2 : Int) + d1061 p := by
  cases selected : p 160 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d109, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2654 p hg
    simpa only [d109, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d109, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2669 p hg
    simpa only [d109, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2671 (p : Pattern) (guard : d853 p = 1) : d125 p ≤ (2 : Int) + d1062 p := by
  cases selected : p 187 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d125, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2653 p hg
    simpa only [d125, d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d125, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2658 p hg
    simpa only [d125, d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2672 (p : Pattern) (guard : d853 p = 1) : d126 p ≤ (2 : Int) + d1063 p := by
  cases selected : p 186 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d126, d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2653 p hg
    simpa only [d126, d1063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d126, d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2671 p hg
    simpa only [d126, d1063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2673 (p : Pattern) (guard : d853 p = 1) : d127 p ≤ (2 : Int) + d1064 p := by
  cases selected : p 168 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d127, d1064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2665 p hg
    simpa only [d127, d1064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d127, d1064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2672 p hg
    simpa only [d127, d1064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2674 (p : Pattern) (guard : d853 p = 1) : d128 p ≤ (2 : Int) + d1065 p := by
  cases selected : p 160 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d128, d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2673 p hg
    simpa only [d128, d1065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d128, d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2669 p hg
    simpa only [d128, d1065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2675 (p : Pattern) (guard : d853 p = 1) : d129 p ≤ (2 : Int) + d1066 p := by
  cases selected : p 159 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d129, d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2670 p hg
    simpa only [d129, d1066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d129, d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2674 p hg
    simpa only [d129, d1066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2676 (p : Pattern) (guard : d853 p = 1) : d237 p ≤ (2 : Int) + d1067 p := by
  cases selected : p 158 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d237, d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2670 p hg
    simpa only [d237, d1067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d237, d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2675 p hg
    simpa only [d237, d1067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2677 (p : Pattern) (guard : d853 p = 1) : d238 p ≤ (2 : Int) + d1068 p := by
  cases selected : p 141 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d238, d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2668 p hg
    simpa only [d238, d1068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d238, d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2676 p hg
    simpa only [d238, d1068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2678 (p : Pattern) (guard : d853 p = 1) : d239 p ≤ (2 : Int) + d1069 p := by
  cases selected : p 134 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d239, d1069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2662 p hg
    simpa only [d239, d1069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d239, d1069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2677 p hg
    simpa only [d239, d1069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2679 (p : Pattern) (guard : d853 p = 1) : d68 p ≤ (2 : Int) + d48 p := by
  cases selected : p 158 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d68, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2649 p hg
    simpa only [d68, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d68, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2647 p hg
    simpa only [d68, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2680 (p : Pattern) (guard : d853 p = 1) : d69 p ≤ (2 : Int) + d1070 p := by
  cases selected : p 158 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d69, d1070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2661 p hg
    simpa only [d69, d1070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d69, d1070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2669 p hg
    simpa only [d69, d1070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2681 (p : Pattern) (guard : d853 p = 1) : d70 p ≤ (2 : Int) + d1071 p := by
  cases selected : p 141 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d70, d1071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2679 p hg
    simpa only [d70, d1071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d70, d1071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2680 p hg
    simpa only [d70, d1071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2682 (p : Pattern) (guard : d853 p = 1) : d181 p ≤ (2 : Int) + d164 p := by
  cases selected : p 158 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d181, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2667 p hg
    simpa only [d181, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d181, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2647 p hg
    simpa only [d181, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2683 (p : Pattern) (guard : d853 p = 1) : d240 p ≤ (2 : Int) + d1072 p := by
  cases selected : p 158 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d240, d1072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2675 p hg
    simpa only [d240, d1072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d240, d1072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2669 p hg
    simpa only [d240, d1072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2684 (p : Pattern) (guard : d853 p = 1) : d241 p ≤ (2 : Int) + d1073 p := by
  cases selected : p 141 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d241, d1073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2682 p hg
    simpa only [d241, d1073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d241, d1073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2683 p hg
    simpa only [d241, d1073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2685 (p : Pattern) (guard : d853 p = 1) : d242 p ≤ (2 : Int) + d1074 p := by
  cases selected : p 134 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d242, d1074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2681 p hg
    simpa only [d242, d1074, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d242, d1074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2684 p hg
    simpa only [d242, d1074, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2686 (p : Pattern) (guard : d853 p = 1) : d243 p ≤ (2 : Int) + d1075 p := by
  cases selected : p 133 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d243, d1075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2678 p hg
    simpa only [d243, d1075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d243, d1075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2685 p hg
    simpa only [d243, d1075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2687 (p : Pattern) (guard : d853 p = 1) : d66 p ≤ (2 : Int) + d1076 p := by
  cases selected : p 141 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d66, d1076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2647 p hg
    simpa only [d66, d1076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d66, d1076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2669 p hg
    simpa only [d66, d1076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2688 (p : Pattern) (guard : d853 p = 1) : d244 p ≤ (2 : Int) + d1077 p := by
  cases selected : p 133 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d244, d1077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2685 p hg
    simpa only [d244, d1077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d244, d1077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2687 p hg
    simpa only [d244, d1077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2689 (p : Pattern) (guard : d853 p = 1) : d245 p ≤ (2 : Int) + d1078 p := by
  cases selected : p 132 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d245, d1078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2686 p hg
    simpa only [d245, d1078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d245, d1078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2688 p hg
    simpa only [d245, d1078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2690 (p : Pattern) (guard : d853 p = 1) : d137 p ≤ (2 : Int) + d92 p := by
  cases selected : p 186 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d137, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2664 p hg
    simpa only [d137, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d137, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2647 p hg
    simpa only [d137, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2691 (p : Pattern) (guard : d853 p = 1) : d139 p ≤ (2 : Int) + d94 p := by
  cases selected : p 160 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d139, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2665 p hg
    simpa only [d139, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d139, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2690 p hg
    simpa only [d139, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2692 (p : Pattern) (guard : d853 p = 1) : d153 p ≤ (2 : Int) + d100 p := by
  cases selected : p 159 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d153, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2649 p hg
    simpa only [d153, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d153, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2691 p hg
    simpa only [d153, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2693 (p : Pattern) (guard : d853 p = 1) : d186 p ≤ (2 : Int) + d169 p := by
  cases selected : p 158 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d186, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2649 p hg
    simpa only [d186, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d186, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2692 p hg
    simpa only [d186, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2694 (p : Pattern) (guard : d853 p = 1) : d143 p ≤ (2 : Int) + d1079 p := by
  cases selected : p 186 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d143, d1079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2671 p hg
    simpa only [d143, d1079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d143, d1079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2658 p hg
    simpa only [d143, d1079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2695 (p : Pattern) (guard : d853 p = 1) : d144 p ≤ (2 : Int) + d1080 p := by
  cases selected : p 168 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d144, d1080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2690 p hg
    simpa only [d144, d1080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d144, d1080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2694 p hg
    simpa only [d144, d1080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2696 (p : Pattern) (guard : d853 p = 1) : d146 p ≤ (2 : Int) + d1081 p := by
  cases selected : p 160 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d146, d1081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2673 p hg
    simpa only [d146, d1081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d146, d1081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2695 p hg
    simpa only [d146, d1081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2697 (p : Pattern) (guard : d853 p = 1) : d155 p ≤ (2 : Int) + d1082 p := by
  cases selected : p 159 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d155, d1082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2661 p hg
    simpa only [d155, d1082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d155, d1082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2696 p hg
    simpa only [d155, d1082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2698 (p : Pattern) (guard : d853 p = 1) : d246 p ≤ (2 : Int) + d1083 p := by
  cases selected : p 158 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d246, d1083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2661 p hg
    simpa only [d246, d1083, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d246, d1083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2697 p hg
    simpa only [d246, d1083, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2699 (p : Pattern) (guard : d853 p = 1) : d247 p ≤ (2 : Int) + d1084 p := by
  cases selected : p 141 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d247, d1084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2693 p hg
    simpa only [d247, d1084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d247, d1084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2698 p hg
    simpa only [d247, d1084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2700 (p : Pattern) (guard : d853 p = 1) : d248 p ≤ (2 : Int) + d1085 p := by
  cases selected : p 134 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d248, d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2699 p hg
    simpa only [d248, d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d248, d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2687 p hg
    simpa only [d248, d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2701 (p : Pattern) (guard : d853 p = 1) : d138 p ≤ (2 : Int) + d93 p := by
  cases selected : p 160 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d138, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2643 p hg
    simpa only [d138, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d138, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2690 p hg
    simpa only [d138, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2702 (p : Pattern) (guard : d853 p = 1) : d140 p ≤ (2 : Int) + d95 p := by
  cases selected : p 159 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d140, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2701 p hg
    simpa only [d140, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d140, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2691 p hg
    simpa only [d140, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2703 (p : Pattern) (guard : d853 p = 1) : d188 p ≤ (2 : Int) + d171 p := by
  cases selected : p 158 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d188, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2702 p hg
    simpa only [d188, d171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d188, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2647 p hg
    simpa only [d188, d171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2704 (p : Pattern) (guard : d853 p = 1) : d145 p ≤ (2 : Int) + d1086 p := by
  cases selected : p 160 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d145, d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2654 p hg
    simpa only [d145, d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d145, d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2695 p hg
    simpa only [d145, d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2705 (p : Pattern) (guard : d853 p = 1) : d147 p ≤ (2 : Int) + d1087 p := by
  cases selected : p 159 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d147, d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2704 p hg
    simpa only [d147, d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d147, d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2696 p hg
    simpa only [d147, d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2706 (p : Pattern) (guard : d853 p = 1) : d249 p ≤ (2 : Int) + d1088 p := by
  cases selected : p 158 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d249, d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2705 p hg
    simpa only [d249, d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d249, d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2669 p hg
    simpa only [d249, d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2707 (p : Pattern) (guard : d853 p = 1) : d250 p ≤ (2 : Int) + d1089 p := by
  cases selected : p 141 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d250, d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2703 p hg
    simpa only [d250, d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d250, d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2706 p hg
    simpa only [d250, d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2708 (p : Pattern) (guard : d853 p = 1) : d251 p ≤ (2 : Int) + d1090 p := by
  cases selected : p 134 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d251, d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2707 p hg
    simpa only [d251, d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d251, d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2687 p hg
    simpa only [d251, d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2709 (p : Pattern) (guard : d853 p = 1) : d252 p ≤ (2 : Int) + d1091 p := by
  cases selected : p 133 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d252, d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2700 p hg
    simpa only [d252, d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d252, d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2708 p hg
    simpa only [d252, d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2710 (p : Pattern) (guard : d853 p = 1) : d191 p ≤ (2 : Int) + d174 p := by
  cases selected : p 158 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d191, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2692 p hg
    simpa only [d191, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d191, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2647 p hg
    simpa only [d191, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2711 (p : Pattern) (guard : d853 p = 1) : d253 p ≤ (2 : Int) + d1092 p := by
  cases selected : p 158 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d253, d1092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2697 p hg
    simpa only [d253, d1092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d253, d1092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2669 p hg
    simpa only [d253, d1092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2712 (p : Pattern) (guard : d853 p = 1) : d254 p ≤ (2 : Int) + d1093 p := by
  cases selected : p 141 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d254, d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2710 p hg
    simpa only [d254, d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d254, d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2711 p hg
    simpa only [d254, d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2713 (p : Pattern) (guard : d853 p = 1) : d255 p ≤ (2 : Int) + d1094 p := by
  cases selected : p 134 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d255, d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2712 p hg
    simpa only [d255, d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d255, d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2687 p hg
    simpa only [d255, d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2714 (p : Pattern) (guard : d853 p = 1) : d256 p ≤ (2 : Int) + d1095 p := by
  cases selected : p 133 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d256, d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2713 p hg
    simpa only [d256, d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d256, d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2687 p hg
    simpa only [d256, d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2715 (p : Pattern) (guard : d853 p = 1) : d257 p ≤ (2 : Int) + d1096 p := by
  cases selected : p 132 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d257, d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2709 p hg
    simpa only [d257, d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d257, d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2714 p hg
    simpa only [d257, d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2716 (p : Pattern) (guard : d853 p = 1) : d258 p ≤ (2 : Int) + d1097 p := by
  cases selected : p 108 with
  | false =>
    have hg : d853 p = 1 := by simpa only [d258, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2689 p hg
    simpa only [d258, d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d853 p = 1 := by simpa only [d258, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2715 p hg
    simpa only [d258, d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2717 (p : Pattern) (guard : d770 p = 1) : d57 p ≤ (2 : Int) + d57 p := by
  omega
theorem compare2718 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (2 : Int) + d1 p := by
  change (0 : Int) ≤ (2 : Int) + 1
  decide
theorem compare2719 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (2 : Int) + d8 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2641 p hg
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2718 p hg
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2720 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (2 : Int) + d3 p := by
  change (2 : Int) ≤ (2 : Int) + 3
  decide
theorem compare2721 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (2 : Int) + d9 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2645 p hg
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2720 p hg
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2722 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (2 : Int) + d10 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d6, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2719 p hg
    simpa only [d6, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d6, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2721 p hg
    simpa only [d6, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2723 (p : Pattern) (guard : d1 p = 1) : d7 p ≤ (2 : Int) + d11 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2719 p hg
    simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2722 p hg
    simpa only [d7, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2724 (p : Pattern) (guard : d0 p = 1) : d11 p ≤ (2 : Int) + d11 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2725 (p : Pattern) (guard : d770 p = 1) : d12 p ≤ (2 : Int) + d11 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2723 p hg
    simpa only [d770, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2724 p hg
    simpa only [d770, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2726 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (2 : Int) + d4 p := by
  omega
theorem compare2727 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (2 : Int) + d5 p := by
  change (4 : Int) ≤ (2 : Int) + 5
  decide
theorem compare2728 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (2 : Int) + d58 p := by
  cases selected : p 271 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2726 p hg
    simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2727 p hg
    simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2729 (p : Pattern) (guard : d1 p = 1) : d54 p ≤ (2 : Int) + d59 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d54, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2721 p hg
    simpa only [d54, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d54, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2728 p hg
    simpa only [d54, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2730 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (2 : Int) + d60 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d55, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2721 p hg
    simpa only [d55, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d55, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2729 p hg
    simpa only [d55, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2731 (p : Pattern) (guard : d1 p = 1) : d56 p ≤ (2 : Int) + d61 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d56, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2723 p hg
    simpa only [d56, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d56, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2730 p hg
    simpa only [d56, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2732 (p : Pattern) (guard : d0 p = 1) : d61 p ≤ (2 : Int) + d61 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2733 (p : Pattern) (guard : d770 p = 1) : d62 p ≤ (2 : Int) + d61 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2731 p hg
    simpa only [d770, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2732 p hg
    simpa only [d770, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2734 (p : Pattern) (guard : d770 p = 1) : d63 p ≤ (2 : Int) + d1098 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d63, d1098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2725 p hg
    simpa only [d63, d1098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d63, d1098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2733 p hg
    simpa only [d63, d1098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2735 (p : Pattern) (guard : d770 p = 1) : d64 p ≤ (2 : Int) + d1099 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d64, d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2717 p hg
    simpa only [d64, d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d64, d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2734 p hg
    simpa only [d64, d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2736 (p : Pattern) (guard : d770 p = 1) : d179 p ≤ (2 : Int) + d179 p := by
  omega
theorem compare2737 (p : Pattern) (guard : d0 p = 1) : d60 p ≤ (2 : Int) + d60 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2738 (p : Pattern) (guard : d770 p = 1) : d65 p ≤ (2 : Int) + d60 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2730 p hg
    simpa only [d770, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2737 p hg
    simpa only [d770, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2739 (p : Pattern) (guard : d770 p = 1) : d109 p ≤ (2 : Int) + d1100 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d109, d1100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2725 p hg
    simpa only [d109, d1100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d109, d1100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2738 p hg
    simpa only [d109, d1100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2740 (p : Pattern) (guard : d1 p = 1) : d119 p ≤ (2 : Int) + d125 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d119, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2723 p hg
    simpa only [d119, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d119, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2730 p hg
    simpa only [d119, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2741 (p : Pattern) (guard : d1 p = 1) : d120 p ≤ (2 : Int) + d126 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d120, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2723 p hg
    simpa only [d120, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d120, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2740 p hg
    simpa only [d120, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2742 (p : Pattern) (guard : d0 p = 1) : d126 p ≤ (2 : Int) + d126 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2743 (p : Pattern) (guard : d770 p = 1) : d127 p ≤ (2 : Int) + d126 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2741 p hg
    simpa only [d770, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2742 p hg
    simpa only [d770, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2744 (p : Pattern) (guard : d770 p = 1) : d128 p ≤ (2 : Int) + d1101 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d128, d1101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2743 p hg
    simpa only [d128, d1101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d128, d1101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2738 p hg
    simpa only [d128, d1101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2745 (p : Pattern) (guard : d770 p = 1) : d129 p ≤ (2 : Int) + d1102 p := by
  cases selected : p 159 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d129, d1102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2739 p hg
    simpa only [d129, d1102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d129, d1102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2744 p hg
    simpa only [d129, d1102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2746 (p : Pattern) (guard : d770 p = 1) : d237 p ≤ (2 : Int) + d1103 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d237, d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2739 p hg
    simpa only [d237, d1103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d237, d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2745 p hg
    simpa only [d237, d1103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2747 (p : Pattern) (guard : d770 p = 1) : d238 p ≤ (2 : Int) + d1104 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d238, d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2736 p hg
    simpa only [d238, d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d238, d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2746 p hg
    simpa only [d238, d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2748 (p : Pattern) (guard : d770 p = 1) : d239 p ≤ (2 : Int) + d1105 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d239, d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2735 p hg
    simpa only [d239, d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d239, d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2747 p hg
    simpa only [d239, d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2749 (p : Pattern) (guard : d770 p = 1) : d68 p ≤ (2 : Int) + d68 p := by
  omega
theorem compare2750 (p : Pattern) (guard : d770 p = 1) : d69 p ≤ (2 : Int) + d1106 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d69, d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2734 p hg
    simpa only [d69, d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d69, d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2738 p hg
    simpa only [d69, d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2751 (p : Pattern) (guard : d770 p = 1) : d70 p ≤ (2 : Int) + d1107 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d70, d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2749 p hg
    simpa only [d70, d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d70, d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2750 p hg
    simpa only [d70, d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2752 (p : Pattern) (guard : d770 p = 1) : d181 p ≤ (2 : Int) + d181 p := by
  omega
theorem compare2753 (p : Pattern) (guard : d770 p = 1) : d240 p ≤ (2 : Int) + d1108 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d240, d1108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2745 p hg
    simpa only [d240, d1108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d240, d1108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2738 p hg
    simpa only [d240, d1108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2754 (p : Pattern) (guard : d770 p = 1) : d241 p ≤ (2 : Int) + d1109 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d241, d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2752 p hg
    simpa only [d241, d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d241, d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2753 p hg
    simpa only [d241, d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2755 (p : Pattern) (guard : d770 p = 1) : d242 p ≤ (2 : Int) + d1110 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d242, d1110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2751 p hg
    simpa only [d242, d1110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d242, d1110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2754 p hg
    simpa only [d242, d1110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2756 (p : Pattern) (guard : d770 p = 1) : d243 p ≤ (2 : Int) + d1111 p := by
  cases selected : p 133 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d243, d1111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2748 p hg
    simpa only [d243, d1111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d243, d1111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2755 p hg
    simpa only [d243, d1111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2757 (p : Pattern) (guard : d770 p = 1) : d55 p ≤ (2 : Int) + d55 p := by
  omega
theorem compare2758 (p : Pattern) (guard : d770 p = 1) : d66 p ≤ (2 : Int) + d1112 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d66, d1112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2757 p hg
    simpa only [d66, d1112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d66, d1112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2738 p hg
    simpa only [d66, d1112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2759 (p : Pattern) (guard : d770 p = 1) : d244 p ≤ (2 : Int) + d1113 p := by
  cases selected : p 133 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d244, d1113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2755 p hg
    simpa only [d244, d1113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d244, d1113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2758 p hg
    simpa only [d244, d1113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2760 (p : Pattern) (guard : d770 p = 1) : d245 p ≤ (2 : Int) + d1114 p := by
  cases selected : p 132 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d245, d1114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2756 p hg
    simpa only [d245, d1114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d245, d1114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2759 p hg
    simpa only [d245, d1114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2761 (p : Pattern) (guard : d770 p = 1) : d186 p ≤ (2 : Int) + d186 p := by
  omega
theorem compare2762 (p : Pattern) (guard : d1 p = 1) : d137 p ≤ (2 : Int) + d143 p := by
  cases selected : p 186 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d137, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2740 p hg
    simpa only [d137, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d137, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2730 p hg
    simpa only [d137, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2763 (p : Pattern) (guard : d0 p = 1) : d143 p ≤ (2 : Int) + d143 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2764 (p : Pattern) (guard : d770 p = 1) : d144 p ≤ (2 : Int) + d143 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d770, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2762 p hg
    simpa only [d770, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2763 p hg
    simpa only [d770, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2765 (p : Pattern) (guard : d770 p = 1) : d146 p ≤ (2 : Int) + d1115 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d146, d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2743 p hg
    simpa only [d146, d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d146, d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2764 p hg
    simpa only [d146, d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2766 (p : Pattern) (guard : d770 p = 1) : d155 p ≤ (2 : Int) + d1116 p := by
  cases selected : p 159 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d155, d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2734 p hg
    simpa only [d155, d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d155, d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2765 p hg
    simpa only [d155, d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2767 (p : Pattern) (guard : d770 p = 1) : d246 p ≤ (2 : Int) + d1117 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d246, d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2734 p hg
    simpa only [d246, d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d246, d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2766 p hg
    simpa only [d246, d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2768 (p : Pattern) (guard : d770 p = 1) : d247 p ≤ (2 : Int) + d1118 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d247, d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2761 p hg
    simpa only [d247, d1118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d247, d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2767 p hg
    simpa only [d247, d1118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2769 (p : Pattern) (guard : d770 p = 1) : d248 p ≤ (2 : Int) + d1119 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d248, d1119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2768 p hg
    simpa only [d248, d1119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d248, d1119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2758 p hg
    simpa only [d248, d1119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2770 (p : Pattern) (guard : d770 p = 1) : d188 p ≤ (2 : Int) + d188 p := by
  omega
theorem compare2771 (p : Pattern) (guard : d770 p = 1) : d145 p ≤ (2 : Int) + d1120 p := by
  cases selected : p 160 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d145, d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2725 p hg
    simpa only [d145, d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d145, d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2764 p hg
    simpa only [d145, d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2772 (p : Pattern) (guard : d770 p = 1) : d147 p ≤ (2 : Int) + d1121 p := by
  cases selected : p 159 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d147, d1121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2771 p hg
    simpa only [d147, d1121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d147, d1121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2765 p hg
    simpa only [d147, d1121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2773 (p : Pattern) (guard : d770 p = 1) : d249 p ≤ (2 : Int) + d1122 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d249, d1122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2772 p hg
    simpa only [d249, d1122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d249, d1122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2738 p hg
    simpa only [d249, d1122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2774 (p : Pattern) (guard : d770 p = 1) : d250 p ≤ (2 : Int) + d1123 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d250, d1123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2770 p hg
    simpa only [d250, d1123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d250, d1123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2773 p hg
    simpa only [d250, d1123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2775 (p : Pattern) (guard : d770 p = 1) : d251 p ≤ (2 : Int) + d1124 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d251, d1124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2774 p hg
    simpa only [d251, d1124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d251, d1124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2758 p hg
    simpa only [d251, d1124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2776 (p : Pattern) (guard : d770 p = 1) : d252 p ≤ (2 : Int) + d1125 p := by
  cases selected : p 133 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d252, d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2769 p hg
    simpa only [d252, d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d252, d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2775 p hg
    simpa only [d252, d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2777 (p : Pattern) (guard : d770 p = 1) : d191 p ≤ (2 : Int) + d191 p := by
  omega
theorem compare2778 (p : Pattern) (guard : d770 p = 1) : d253 p ≤ (2 : Int) + d1126 p := by
  cases selected : p 158 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d253, d1126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2766 p hg
    simpa only [d253, d1126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d253, d1126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2738 p hg
    simpa only [d253, d1126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2779 (p : Pattern) (guard : d770 p = 1) : d254 p ≤ (2 : Int) + d1127 p := by
  cases selected : p 141 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d254, d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2777 p hg
    simpa only [d254, d1127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d254, d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2778 p hg
    simpa only [d254, d1127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2780 (p : Pattern) (guard : d770 p = 1) : d255 p ≤ (2 : Int) + d1128 p := by
  cases selected : p 134 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d255, d1128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2779 p hg
    simpa only [d255, d1128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d255, d1128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2758 p hg
    simpa only [d255, d1128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2781 (p : Pattern) (guard : d770 p = 1) : d256 p ≤ (2 : Int) + d1129 p := by
  cases selected : p 133 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d256, d1129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2780 p hg
    simpa only [d256, d1129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d256, d1129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2758 p hg
    simpa only [d256, d1129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2782 (p : Pattern) (guard : d770 p = 1) : d257 p ≤ (2 : Int) + d1130 p := by
  cases selected : p 132 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d257, d1130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2776 p hg
    simpa only [d257, d1130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d257, d1130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2781 p hg
    simpa only [d257, d1130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2783 (p : Pattern) (guard : d770 p = 1) : d258 p ≤ (2 : Int) + d1131 p := by
  cases selected : p 108 with
  | false =>
    have hg : d770 p = 1 := by simpa only [d258, d1131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2760 p hg
    simpa only [d258, d1131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d258, d1131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2782 p hg
    simpa only [d258, d1131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2784 (p : Pattern) (guard : d0 p = 1) : d0 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2785 (p : Pattern) (guard : d917 p = 1) : d0 p ≤ (0 : Int) + d6 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare898 p hg
    simpa only [d917, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2784 p hg
    simpa only [d917, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2786 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d3 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2787 (p : Pattern) (guard : d917 p = 1) : d6 p ≤ (0 : Int) + d28 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d6, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare898 p hg
    simpa only [d917, d6, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d6, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2786 p hg
    simpa only [d917, d6, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2788 (p : Pattern) (guard : d917 p = 1) : d7 p ≤ (0 : Int) + d29 p := by
  cases selected : p 192 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d7, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2785 p hg
    simpa only [d7, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d7, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2787 p hg
    simpa only [d7, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2789 (p : Pattern) (guard : d0 p = 1) : d0 p ≤ (0 : Int) + d9 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2790 (p : Pattern) (guard : d917 p = 1) : d0 p ≤ (0 : Int) + d14 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare898 p hg
    simpa only [d917, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2789 p hg
    simpa only [d917, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2791 (p : Pattern) (guard : d917 p = 1) : d7 p ≤ (0 : Int) + d30 p := by
  cases selected : p 192 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d7, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2790 p hg
    simpa only [d7, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d7, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2787 p hg
    simpa only [d7, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2792 (p : Pattern) (guard : d917 p = 1) : d7 p ≤ (0 : Int) + d31 p := by
  cases selected : p 168 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2788 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2791 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2793 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d4 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2794 (p : Pattern) (guard : d917 p = 1) : d2 p ≤ (0 : Int) + d54 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare902 p hg
    simpa only [d917, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2793 p hg
    simpa only [d917, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2795 (p : Pattern) (guard : d0 p = 1) : d4 p ≤ (0 : Int) + d5 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare2796 (p : Pattern) (guard : d917 p = 1) : d54 p ≤ (0 : Int) + d587 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d54, d587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare902 p hg
    simpa only [d917, d54, d587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d54, d587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2795 p hg
    simpa only [d917, d54, d587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2797 (p : Pattern) (guard : d917 p = 1) : d55 p ≤ (0 : Int) + d588 p := by
  cases selected : p 192 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d55, d588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2794 p hg
    simpa only [d55, d588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d55, d588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2796 p hg
    simpa only [d55, d588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2798 (p : Pattern) (guard : d917 p = 1) : d56 p ≤ (0 : Int) + d589 p := by
  cases selected : p 186 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d56, d589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2788 p hg
    simpa only [d56, d589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d56, d589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2797 p hg
    simpa only [d56, d589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare2799 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (0 : Int) + d58 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban12CostPartition
