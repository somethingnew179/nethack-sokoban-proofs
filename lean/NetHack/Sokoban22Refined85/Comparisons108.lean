/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons107
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare15120 (p : Pattern) (guard : d5503 p = 1) : d133 p ≤ (0 : Int) + d2760 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d133, d2760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15104 p hg
    simpa only [d133, d2760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d133, d2760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15111 p hg
    simpa only [d133, d2760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15121 (p : Pattern) (guard : d5503 p = 1) : d134 p ≤ (0 : Int) + d2761 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d134, d2761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15106 p hg
    simpa only [d134, d2761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d134, d2761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14926 p hg
    simpa only [d134, d2761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15122 (p : Pattern) (guard : d5503 p = 1) : d135 p ≤ (0 : Int) + d2762 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d135, d2762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15120 p hg
    simpa only [d135, d2762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d135, d2762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15121 p hg
    simpa only [d135, d2762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15123 (p : Pattern) (guard : d5503 p = 1) : d136 p ≤ (0 : Int) + d2763 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d136, d2763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15106 p hg
    simpa only [d136, d2763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d136, d2763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14931 p hg
    simpa only [d136, d2763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15124 (p : Pattern) (guard : d5503 p = 1) : d137 p ≤ (0 : Int) + d2764 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d137, d2764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15123 p hg
    simpa only [d137, d2764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d137, d2764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d137, d2764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15125 (p : Pattern) (guard : d5503 p = 1) : d138 p ≤ (0 : Int) + d2765 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d138, d2765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15122 p hg
    simpa only [d138, d2765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d138, d2765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15124 p hg
    simpa only [d138, d2765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15126 (p : Pattern) (guard : d5503 p = 1) : d153 p ≤ (0 : Int) + d2766 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d153, d2766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15115 p hg
    simpa only [d153, d2766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d153, d2766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d153, d2766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15127 (p : Pattern) (guard : d5503 p = 1) : d154 p ≤ (0 : Int) + d2767 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d154, d2767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15126 p hg
    simpa only [d154, d2767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d154, d2767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d154, d2767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15128 (p : Pattern) (guard : d5503 p = 1) : d155 p ≤ (0 : Int) + d2768 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d155, d2768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15127 p hg
    simpa only [d155, d2768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d155, d2768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d155, d2768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15129 (p : Pattern) (guard : d5503 p = 1) : d156 p ≤ (0 : Int) + d2769 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d156, d2769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15125 p hg
    simpa only [d156, d2769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d156, d2769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15128 p hg
    simpa only [d156, d2769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15130 (p : Pattern) (guard : d5503 p = 1) : d157 p ≤ (0 : Int) + d2770 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d157, d2770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15119 p hg
    simpa only [d157, d2770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d157, d2770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15129 p hg
    simpa only [d157, d2770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15131 (p : Pattern) (guard : d5503 p = 1) : d158 p ≤ (0 : Int) + d2771 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d158, d2771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15102 p hg
    simpa only [d158, d2771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d158, d2771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15130 p hg
    simpa only [d158, d2771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15132 (p : Pattern) (guard : d5503 p = 1) : d159 p ≤ (0 : Int) + d2772 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d159, d2772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15054 p hg
    simpa only [d159, d2772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d159, d2772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d159, d2772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15133 (p : Pattern) (guard : d5503 p = 1) : d160 p ≤ (0 : Int) + d2773 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d160, d2773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15132 p hg
    simpa only [d160, d2773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d160, d2773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d160, d2773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15134 (p : Pattern) (guard : d5503 p = 1) : d161 p ≤ (0 : Int) + d2774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d161, d2774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15133 p hg
    simpa only [d161, d2774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d161, d2774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d161, d2774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15135 (p : Pattern) (guard : d5503 p = 1) : d162 p ≤ (0 : Int) + d2775 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d162, d2775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15134 p hg
    simpa only [d162, d2775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d162, d2775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d162, d2775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15136 (p : Pattern) (guard : d5503 p = 1) : d163 p ≤ (0 : Int) + d2776 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d163, d2776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15130 p hg
    simpa only [d163, d2776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d163, d2776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15135 p hg
    simpa only [d163, d2776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15137 (p : Pattern) (guard : d5503 p = 1) : d164 p ≤ (0 : Int) + d2777 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d164, d2777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15131 p hg
    simpa only [d164, d2777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d164, d2777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15136 p hg
    simpa only [d164, d2777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15138 (p : Pattern) (guard : d5503 p = 1) : d111 p ≤ (0 : Int) + d2778 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d111, d2778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15040 p hg
    simpa only [d111, d2778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d111, d2778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15052 p hg
    simpa only [d111, d2778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15139 (p : Pattern) (guard : d5503 p = 1) : d114 p ≤ (0 : Int) + d2779 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d114, d2779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15138 p hg
    simpa only [d114, d2779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d114, d2779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15055 p hg
    simpa only [d114, d2779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15140 (p : Pattern) (guard : d5503 p = 1) : d131 p ≤ (0 : Int) + d2780 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d131, d2780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15139 p hg
    simpa only [d131, d2780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d131, d2780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15074 p hg
    simpa only [d131, d2780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15141 (p : Pattern) (guard : d5503 p = 1) : d133 p ≤ (0 : Int) + d2781 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d133, d2781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15040 p hg
    simpa only [d133, d2781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d133, d2781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15087 p hg
    simpa only [d133, d2781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15142 (p : Pattern) (guard : d5503 p = 1) : d135 p ≤ (0 : Int) + d2782 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d135, d2782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15141 p hg
    simpa only [d135, d2782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d135, d2782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15089 p hg
    simpa only [d135, d2782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15143 (p : Pattern) (guard : d5503 p = 1) : d138 p ≤ (0 : Int) + d2783 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d138, d2783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15142 p hg
    simpa only [d138, d2783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d138, d2783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15092 p hg
    simpa only [d138, d2783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15144 (p : Pattern) (guard : d5503 p = 1) : d146 p ≤ (0 : Int) + d2784 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d146, d2784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15143 p hg
    simpa only [d146, d2784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d146, d2784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15100 p hg
    simpa only [d146, d2784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15145 (p : Pattern) (guard : d5503 p = 1) : d147 p ≤ (0 : Int) + d2785 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d147, d2785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15140 p hg
    simpa only [d147, d2785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d147, d2785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15144 p hg
    simpa only [d147, d2785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15146 (p : Pattern) (guard : d5503 p = 1) : d158 p ≤ (0 : Int) + d2786 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d158, d2786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15145 p hg
    simpa only [d158, d2786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d158, d2786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15130 p hg
    simpa only [d158, d2786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15147 (p : Pattern) (guard : d5503 p = 1) : d165 p ≤ (0 : Int) + d2787 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d165, d2787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15130 p hg
    simpa only [d165, d2787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d165, d2787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d165, d2787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15148 (p : Pattern) (guard : d5503 p = 1) : d166 p ≤ (0 : Int) + d2788 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d166, d2788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15146 p hg
    simpa only [d166, d2788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d166, d2788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15147 p hg
    simpa only [d166, d2788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15149 (p : Pattern) (guard : d5503 p = 1) : d167 p ≤ (0 : Int) + d2789 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d167, d2789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15137 p hg
    simpa only [d167, d2789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d167, d2789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15148 p hg
    simpa only [d167, d2789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15150 (p : Pattern) (guard : d5503 p = 1) : d168 p ≤ (0 : Int) + d2790 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d168, d2790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15001 p hg
    simpa only [d168, d2790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d168, d2790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15149 p hg
    simpa only [d168, d2790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15151 (p : Pattern) (guard : d5503 p = 1) : d169 p ≤ (0 : Int) + d2791 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d169, d2791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15025 p hg
    simpa only [d169, d2791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d169, d2791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15150 p hg
    simpa only [d169, d2791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15152 (p : Pattern) (guard : d5503 p = 1) : d170 p ≤ (0 : Int) + d2792 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d170, d2792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14911 p hg
    simpa only [d170, d2792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d170, d2792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14886 p hg
    simpa only [d170, d2792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15153 (p : Pattern) (guard : d5503 p = 1) : d171 p ≤ (0 : Int) + d2793 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d171, d2793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14958 p hg
    simpa only [d171, d2793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d171, d2793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15152 p hg
    simpa only [d171, d2793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15154 (p : Pattern) (guard : d5503 p = 1) : d172 p ≤ (0 : Int) + d2794 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d172, d2794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14911 p hg
    simpa only [d172, d2794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d172, d2794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14892 p hg
    simpa only [d172, d2794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15155 (p : Pattern) (guard : d5503 p = 1) : d173 p ≤ (0 : Int) + d2795 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d173, d2795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14961 p hg
    simpa only [d173, d2795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d173, d2795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d173, d2795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15156 (p : Pattern) (guard : d5503 p = 1) : d174 p ≤ (0 : Int) + d2796 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d174, d2796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15154 p hg
    simpa only [d174, d2796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d174, d2796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15155 p hg
    simpa only [d174, d2796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15157 (p : Pattern) (guard : d5503 p = 1) : d175 p ≤ (0 : Int) + d2797 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d175, d2797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15153 p hg
    simpa only [d175, d2797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d175, d2797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15156 p hg
    simpa only [d175, d2797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15158 (p : Pattern) (guard : d5503 p = 1) : d176 p ≤ (0 : Int) + d2798 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d176, d2798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14935 p hg
    simpa only [d176, d2798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d176, d2798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15155 p hg
    simpa only [d176, d2798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15159 (p : Pattern) (guard : d5503 p = 1) : d177 p ≤ (0 : Int) + d2799 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d177, d2799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15158 p hg
    simpa only [d177, d2799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d177, d2799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14942 p hg
    simpa only [d177, d2799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15160 (p : Pattern) (guard : d5503 p = 1) : d178 p ≤ (0 : Int) + d2800 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d178, d2800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15157 p hg
    simpa only [d178, d2800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d178, d2800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15159 p hg
    simpa only [d178, d2800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15161 (p : Pattern) (guard : d5503 p = 1) : d179 p ≤ (0 : Int) + d2801 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d179, d2801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14957 p hg
    simpa only [d179, d2801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d179, d2801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15160 p hg
    simpa only [d179, d2801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15162 (p : Pattern) (guard : d5503 p = 1) : d180 p ≤ (0 : Int) + d2802 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d180, d2802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15152 p hg
    simpa only [d180, d2802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d180, d2802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14894 p hg
    simpa only [d180, d2802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15163 (p : Pattern) (guard : d5503 p = 1) : d181 p ≤ (0 : Int) + d2803 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d181, d2803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15155 p hg
    simpa only [d181, d2803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d181, d2803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14941 p hg
    simpa only [d181, d2803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15164 (p : Pattern) (guard : d5503 p = 1) : d182 p ≤ (0 : Int) + d2804 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d182, d2804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15162 p hg
    simpa only [d182, d2804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d182, d2804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15163 p hg
    simpa only [d182, d2804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15165 (p : Pattern) (guard : d5503 p = 1) : d183 p ≤ (0 : Int) + d2805 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d183, d2805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15155 p hg
    simpa only [d183, d2805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d183, d2805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d183, d2805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15166 (p : Pattern) (guard : d5503 p = 1) : d184 p ≤ (0 : Int) + d2806 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d184, d2806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15165 p hg
    simpa only [d184, d2806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d184, d2806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d184, d2806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15167 (p : Pattern) (guard : d5503 p = 1) : d185 p ≤ (0 : Int) + d2807 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d185, d2807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15164 p hg
    simpa only [d185, d2807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d185, d2807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15166 p hg
    simpa only [d185, d2807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15168 (p : Pattern) (guard : d5503 p = 1) : d186 p ≤ (0 : Int) + d2808 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d186, d2808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14972 p hg
    simpa only [d186, d2808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d186, d2808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15167 p hg
    simpa only [d186, d2808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15169 (p : Pattern) (guard : d5503 p = 1) : d187 p ≤ (0 : Int) + d2809 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d187, d2809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15161 p hg
    simpa only [d187, d2809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d187, d2809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15168 p hg
    simpa only [d187, d2809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15170 (p : Pattern) (guard : d5503 p = 1) : d188 p ≤ (0 : Int) + d2810 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d188, d2810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14948 p hg
    simpa only [d188, d2810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d188, d2810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14963 p hg
    simpa only [d188, d2810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15171 (p : Pattern) (guard : d5503 p = 1) : d189 p ≤ (0 : Int) + d2811 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d189, d2811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15170 p hg
    simpa only [d189, d2811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d189, d2811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14964 p hg
    simpa only [d189, d2811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15172 (p : Pattern) (guard : d5502 p = 1) : d191 p ≤ (0 : Int) + d2812 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5250 p hg
    simpa only [d5502, d2812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11750 p hg
    simpa only [d5502, d2812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15173 (p : Pattern) (guard : d0 p = 1) : d191 p ≤ (0 : Int) + d2812 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15174 (p : Pattern) (guard : d5503 p = 1) : d191 p ≤ (0 : Int) + d2812 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15172 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15173 p hg
    simpa only [d5503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15175 (p : Pattern) (guard : d0 p = 1) : d191 p ≤ (0 : Int) + d320 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15176 (p : Pattern) (guard : d5503 p = 1) : d191 p ≤ (0 : Int) + d2813 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5503, d2813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15172 p hg
    simpa only [d5503, d2813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5503, d2813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15175 p hg
    simpa only [d5503, d2813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15177 (p : Pattern) (guard : d5503 p = 1) : d191 p ≤ (0 : Int) + d2814 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d2814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15174 p hg
    simpa only [d2814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d2814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15176 p hg
    simpa only [d2814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15178 (p : Pattern) (guard : d5503 p = 1) : d192 p ≤ (0 : Int) + d2815 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d192, d2815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15176 p hg
    simpa only [d192, d2815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d192, d2815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d192, d2815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15179 (p : Pattern) (guard : d5503 p = 1) : d193 p ≤ (0 : Int) + d2816 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d193, d2816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15177 p hg
    simpa only [d193, d2816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d193, d2816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15178 p hg
    simpa only [d193, d2816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15180 (p : Pattern) (guard : d5503 p = 1) : d194 p ≤ (0 : Int) + d2817 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d194, d2817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14950 p hg
    simpa only [d194, d2817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d194, d2817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15179 p hg
    simpa only [d194, d2817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15181 (p : Pattern) (guard : d5503 p = 1) : d195 p ≤ (0 : Int) + d2818 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d195, d2818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15180 p hg
    simpa only [d195, d2818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d195, d2818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d195, d2818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15182 (p : Pattern) (guard : d5503 p = 1) : d196 p ≤ (0 : Int) + d2819 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d196, d2819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15181 p hg
    simpa only [d196, d2819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d196, d2819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d196, d2819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15183 (p : Pattern) (guard : d5503 p = 1) : d197 p ≤ (0 : Int) + d2820 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d197, d2820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15171 p hg
    simpa only [d197, d2820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d197, d2820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15182 p hg
    simpa only [d197, d2820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15184 (p : Pattern) (guard : d5503 p = 1) : d198 p ≤ (0 : Int) + d2821 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d198, d2821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14950 p hg
    simpa only [d198, d2821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d198, d2821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14931 p hg
    simpa only [d198, d2821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15185 (p : Pattern) (guard : d5503 p = 1) : d199 p ≤ (0 : Int) + d2822 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d199, d2822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14958 p hg
    simpa only [d199, d2822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d199, d2822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15184 p hg
    simpa only [d199, d2822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15186 (p : Pattern) (guard : d5503 p = 1) : d200 p ≤ (0 : Int) + d2823 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d200, d2823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15185 p hg
    simpa only [d200, d2823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d200, d2823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14974 p hg
    simpa only [d200, d2823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15187 (p : Pattern) (guard : d5503 p = 1) : d201 p ≤ (0 : Int) + d2824 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d201, d2824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15179 p hg
    simpa only [d201, d2824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d201, d2824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d201, d2824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15188 (p : Pattern) (guard : d5503 p = 1) : d202 p ≤ (0 : Int) + d2825 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d202, d2825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15187 p hg
    simpa only [d202, d2825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d202, d2825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d202, d2825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15189 (p : Pattern) (guard : d5503 p = 1) : d203 p ≤ (0 : Int) + d2826 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d203, d2826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15188 p hg
    simpa only [d203, d2826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d203, d2826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d203, d2826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15190 (p : Pattern) (guard : d5503 p = 1) : d204 p ≤ (0 : Int) + d2827 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d204, d2827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15186 p hg
    simpa only [d204, d2827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d204, d2827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15189 p hg
    simpa only [d204, d2827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15191 (p : Pattern) (guard : d5503 p = 1) : d205 p ≤ (0 : Int) + d2828 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d205, d2828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15183 p hg
    simpa only [d205, d2828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d205, d2828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15190 p hg
    simpa only [d205, d2828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15192 (p : Pattern) (guard : d5503 p = 1) : d206 p ≤ (0 : Int) + d2829 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d206, d2829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15169 p hg
    simpa only [d206, d2829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d206, d2829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15191 p hg
    simpa only [d206, d2829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15193 (p : Pattern) (guard : d5503 p = 1) : d207 p ≤ (0 : Int) + d2830 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d207, d2830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15191 p hg
    simpa only [d207, d2830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d207, d2830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d207, d2830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15194 (p : Pattern) (guard : d5503 p = 1) : d208 p ≤ (0 : Int) + d2831 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d208, d2831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15192 p hg
    simpa only [d208, d2831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d208, d2831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15193 p hg
    simpa only [d208, d2831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15195 (p : Pattern) (guard : d5503 p = 1) : d209 p ≤ (0 : Int) + d2832 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d209, d2832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15017 p hg
    simpa only [d209, d2832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d209, d2832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15194 p hg
    simpa only [d209, d2832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15196 (p : Pattern) (guard : d5503 p = 1) : d210 p ≤ (0 : Int) + d2833 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d210, d2833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15001 p hg
    simpa only [d210, d2833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d210, d2833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15195 p hg
    simpa only [d210, d2833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15197 (p : Pattern) (guard : d5503 p = 1) : d211 p ≤ (0 : Int) + d2834 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d211, d2834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15051 p hg
    simpa only [d211, d2834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d211, d2834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d211, d2834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15198 (p : Pattern) (guard : d5503 p = 1) : d212 p ≤ (0 : Int) + d2835 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d212, d2835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15088 p hg
    simpa only [d212, d2835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d212, d2835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15197 p hg
    simpa only [d212, d2835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15199 (p : Pattern) (guard : d5503 p = 1) : d213 p ≤ (0 : Int) + d2836 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d213, d2836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15197 p hg
    simpa only [d213, d2836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d213, d2836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d213, d2836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15200 (p : Pattern) (guard : d5503 p = 1) : d214 p ≤ (0 : Int) + d2837 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d214, d2837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15198 p hg
    simpa only [d214, d2837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d214, d2837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15199 p hg
    simpa only [d214, d2837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15201 (p : Pattern) (guard : d5503 p = 1) : d215 p ≤ (0 : Int) + d2838 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d215, d2838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15069 p hg
    simpa only [d215, d2838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d215, d2838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d215, d2838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15202 (p : Pattern) (guard : d5503 p = 1) : d216 p ≤ (0 : Int) + d2839 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d216, d2839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15095 p hg
    simpa only [d216, d2839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d216, d2839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15201 p hg
    simpa only [d216, d2839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15203 (p : Pattern) (guard : d5503 p = 1) : d217 p ≤ (0 : Int) + d2840 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d217, d2840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15201 p hg
    simpa only [d217, d2840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d217, d2840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d217, d2840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15204 (p : Pattern) (guard : d5503 p = 1) : d218 p ≤ (0 : Int) + d2841 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d218, d2841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15202 p hg
    simpa only [d218, d2841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d218, d2841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15203 p hg
    simpa only [d218, d2841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15205 (p : Pattern) (guard : d5503 p = 1) : d219 p ≤ (0 : Int) + d2842 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d219, d2842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15200 p hg
    simpa only [d219, d2842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d219, d2842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15204 p hg
    simpa only [d219, d2842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15206 (p : Pattern) (guard : d5503 p = 1) : d220 p ≤ (0 : Int) + d2843 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d220, d2843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15075 p hg
    simpa only [d220, d2843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d220, d2843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15205 p hg
    simpa only [d220, d2843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15207 (p : Pattern) (guard : d5503 p = 1) : d211 p ≤ (0 : Int) + d2844 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d211, d2844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15106 p hg
    simpa only [d211, d2844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d211, d2844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d211, d2844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15208 (p : Pattern) (guard : d5503 p = 1) : d212 p ≤ (0 : Int) + d2845 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d212, d2845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15120 p hg
    simpa only [d212, d2845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d212, d2845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15207 p hg
    simpa only [d212, d2845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15209 (p : Pattern) (guard : d5503 p = 1) : d213 p ≤ (0 : Int) + d2846 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d213, d2846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15207 p hg
    simpa only [d213, d2846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d213, d2846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d213, d2846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15210 (p : Pattern) (guard : d5503 p = 1) : d214 p ≤ (0 : Int) + d2847 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d214, d2847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15208 p hg
    simpa only [d214, d2847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d214, d2847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15209 p hg
    simpa only [d214, d2847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15211 (p : Pattern) (guard : d5503 p = 1) : d221 p ≤ (0 : Int) + d2848 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d221, d2848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15210 p hg
    simpa only [d221, d2848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d221, d2848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15128 p hg
    simpa only [d221, d2848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15212 (p : Pattern) (guard : d5503 p = 1) : d222 p ≤ (0 : Int) + d2849 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d222, d2849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15119 p hg
    simpa only [d222, d2849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d222, d2849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15211 p hg
    simpa only [d222, d2849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15213 (p : Pattern) (guard : d5503 p = 1) : d223 p ≤ (0 : Int) + d2850 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d223, d2850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15206 p hg
    simpa only [d223, d2850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d223, d2850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15212 p hg
    simpa only [d223, d2850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15214 (p : Pattern) (guard : d5503 p = 1) : d224 p ≤ (0 : Int) + d2851 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d224, d2851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15212 p hg
    simpa only [d224, d2851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d224, d2851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15135 p hg
    simpa only [d224, d2851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15215 (p : Pattern) (guard : d5503 p = 1) : d225 p ≤ (0 : Int) + d2852 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d225, d2852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15213 p hg
    simpa only [d225, d2852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d225, d2852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15214 p hg
    simpa only [d225, d2852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15216 (p : Pattern) (guard : d5503 p = 1) : d226 p ≤ (0 : Int) + d2853 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d226, d2853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15083 p hg
    simpa only [d226, d2853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d226, d2853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15065 p hg
    simpa only [d226, d2853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15217 (p : Pattern) (guard : d5503 p = 1) : d227 p ≤ (0 : Int) + d2854 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d227, d2854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15111 p hg
    simpa only [d227, d2854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d227, d2854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15216 p hg
    simpa only [d227, d2854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15218 (p : Pattern) (guard : d5503 p = 1) : d228 p ≤ (0 : Int) + d2855 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d228, d2855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15217 p hg
    simpa only [d228, d2855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d228, d2855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15201 p hg
    simpa only [d228, d2855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15219 (p : Pattern) (guard : d5503 p = 1) : d229 p ≤ (0 : Int) + d2856 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d229, d2856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15114 p hg
    simpa only [d229, d2856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d229, d2856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d229, d2856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15220 (p : Pattern) (guard : d5503 p = 1) : d230 p ≤ (0 : Int) + d2857 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d230, d2857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15219 p hg
    simpa only [d230, d2857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d230, d2857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d230, d2857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15221 (p : Pattern) (guard : d5503 p = 1) : d231 p ≤ (0 : Int) + d2858 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d231, d2858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15220 p hg
    simpa only [d231, d2858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d231, d2858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d231, d2858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15222 (p : Pattern) (guard : d5503 p = 1) : d232 p ≤ (0 : Int) + d2859 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d232, d2859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15218 p hg
    simpa only [d232, d2859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d232, d2859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15221 p hg
    simpa only [d232, d2859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15223 (p : Pattern) (guard : d5503 p = 1) : d233 p ≤ (0 : Int) + d2860 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d233, d2860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15110 p hg
    simpa only [d233, d2860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d233, d2860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15222 p hg
    simpa only [d233, d2860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15224 (p : Pattern) (guard : d5503 p = 1) : d234 p ≤ (0 : Int) + d2861 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d234, d2861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15047 p hg
    simpa only [d234, d2861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d234, d2861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15065 p hg
    simpa only [d234, d2861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15225 (p : Pattern) (guard : d5503 p = 1) : d235 p ≤ (0 : Int) + d2862 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d235, d2862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15224 p hg
    simpa only [d235, d2862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d235, d2862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15069 p hg
    simpa only [d235, d2862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15226 (p : Pattern) (guard : d5503 p = 1) : d236 p ≤ (0 : Int) + d2863 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d236, d2863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15225 p hg
    simpa only [d236, d2863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d236, d2863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15220 p hg
    simpa only [d236, d2863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15227 (p : Pattern) (guard : d5503 p = 1) : d237 p ≤ (0 : Int) + d2864 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d237, d2864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14900 p hg
    simpa only [d237, d2864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d237, d2864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d237, d2864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15228 (p : Pattern) (guard : d5503 p = 1) : d238 p ≤ (0 : Int) + d2865 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d238, d2865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15226 p hg
    simpa only [d238, d2865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d238, d2865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15227 p hg
    simpa only [d238, d2865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15229 (p : Pattern) (guard : d5503 p = 1) : d239 p ≤ (0 : Int) + d2866 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d239, d2866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15210 p hg
    simpa only [d239, d2866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d239, d2866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15228 p hg
    simpa only [d239, d2866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15230 (p : Pattern) (guard : d5503 p = 1) : d240 p ≤ (0 : Int) + d2867 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d240, d2867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15223 p hg
    simpa only [d240, d2867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d240, d2867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15229 p hg
    simpa only [d240, d2867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15231 (p : Pattern) (guard : d5503 p = 1) : d241 p ≤ (0 : Int) + d2868 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d241, d2868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15111 p hg
    simpa only [d241, d2868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d241, d2868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14931 p hg
    simpa only [d241, d2868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15232 (p : Pattern) (guard : d5503 p = 1) : d242 p ≤ (0 : Int) + d2869 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d242, d2869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15104 p hg
    simpa only [d242, d2869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d242, d2869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15231 p hg
    simpa only [d242, d2869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15233 (p : Pattern) (guard : d5503 p = 1) : d243 p ≤ (0 : Int) + d2870 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d243, d2870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15232 p hg
    simpa only [d243, d2870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d243, d2870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15124 p hg
    simpa only [d243, d2870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15234 (p : Pattern) (guard : d5503 p = 1) : d244 p ≤ (0 : Int) + d2871 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d244, d2871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15233 p hg
    simpa only [d244, d2871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d244, d2871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15128 p hg
    simpa only [d244, d2871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15235 (p : Pattern) (guard : d5503 p = 1) : d245 p ≤ (0 : Int) + d2872 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d245, d2872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15111 p hg
    simpa only [d245, d2872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d245, d2872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15207 p hg
    simpa only [d245, d2872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15236 (p : Pattern) (guard : d5503 p = 1) : d246 p ≤ (0 : Int) + d2873 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d246, d2873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15235 p hg
    simpa only [d246, d2873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d246, d2873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15127 p hg
    simpa only [d246, d2873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15237 (p : Pattern) (guard : d5503 p = 1) : d247 p ≤ (0 : Int) + d2874 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d247, d2874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14955 p hg
    simpa only [d247, d2874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d247, d2874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d247, d2874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15238 (p : Pattern) (guard : d5503 p = 1) : d248 p ≤ (0 : Int) + d2875 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d248, d2875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15237 p hg
    simpa only [d248, d2875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d248, d2875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d248, d2875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15239 (p : Pattern) (guard : d5503 p = 1) : d249 p ≤ (0 : Int) + d2876 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d249, d2876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15236 p hg
    simpa only [d249, d2876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d249, d2876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15238 p hg
    simpa only [d249, d2876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15240 (p : Pattern) (guard : d5503 p = 1) : d250 p ≤ (0 : Int) + d2877 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d250, d2877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15234 p hg
    simpa only [d250, d2877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d250, d2877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15239 p hg
    simpa only [d250, d2877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15241 (p : Pattern) (guard : d5503 p = 1) : d251 p ≤ (0 : Int) + d2878 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d251, d2878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15230 p hg
    simpa only [d251, d2878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d251, d2878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15240 p hg
    simpa only [d251, d2878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15242 (p : Pattern) (guard : d5503 p = 1) : d252 p ≤ (0 : Int) + d2879 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d252, d2879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15111 p hg
    simpa only [d252, d2879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d252, d2879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14954 p hg
    simpa only [d252, d2879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15243 (p : Pattern) (guard : d5503 p = 1) : d253 p ≤ (0 : Int) + d2880 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d253, d2880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15104 p hg
    simpa only [d253, d2880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d253, d2880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15242 p hg
    simpa only [d253, d2880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15244 (p : Pattern) (guard : d5503 p = 1) : d254 p ≤ (0 : Int) + d2881 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d254, d2881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15106 p hg
    simpa only [d254, d2881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d254, d2881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14954 p hg
    simpa only [d254, d2881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15245 (p : Pattern) (guard : d5503 p = 1) : d255 p ≤ (0 : Int) + d2882 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d255, d2882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15244 p hg
    simpa only [d255, d2882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d255, d2882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d255, d2882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15246 (p : Pattern) (guard : d5503 p = 1) : d256 p ≤ (0 : Int) + d2883 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d256, d2883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15243 p hg
    simpa only [d256, d2883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d256, d2883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15245 p hg
    simpa only [d256, d2883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15247 (p : Pattern) (guard : d5503 p = 1) : d257 p ≤ (0 : Int) + d2884 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d257, d2884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15115 p hg
    simpa only [d257, d2884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d257, d2884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14931 p hg
    simpa only [d257, d2884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15248 (p : Pattern) (guard : d5503 p = 1) : d258 p ≤ (0 : Int) + d2885 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d258, d2885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15247 p hg
    simpa only [d258, d2885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d258, d2885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d258, d2885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15249 (p : Pattern) (guard : d5503 p = 1) : d259 p ≤ (0 : Int) + d2886 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d259, d2886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15248 p hg
    simpa only [d259, d2886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d259, d2886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d259, d2886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15250 (p : Pattern) (guard : d5503 p = 1) : d260 p ≤ (0 : Int) + d2887 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d260, d2887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15246 p hg
    simpa only [d260, d2887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d260, d2887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15249 p hg
    simpa only [d260, d2887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15251 (p : Pattern) (guard : d5503 p = 1) : d261 p ≤ (0 : Int) + d2888 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d261, d2888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15250 p hg
    simpa only [d261, d2888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d261, d2888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15239 p hg
    simpa only [d261, d2888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15252 (p : Pattern) (guard : d5503 p = 1) : d262 p ≤ (0 : Int) + d2889 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d262, d2889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15251 p hg
    simpa only [d262, d2889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d262, d2889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14841 p hg
    simpa only [d262, d2889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15253 (p : Pattern) (guard : d5503 p = 1) : d263 p ≤ (0 : Int) + d2890 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d263, d2890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15241 p hg
    simpa only [d263, d2890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d263, d2890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15252 p hg
    simpa only [d263, d2890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15254 (p : Pattern) (guard : d5503 p = 1) : d264 p ≤ (0 : Int) + d2891 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d264, d2891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15215 p hg
    simpa only [d264, d2891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d264, d2891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15253 p hg
    simpa only [d264, d2891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15255 (p : Pattern) (guard : d5503 p = 1) : d265 p ≤ (0 : Int) + d2892 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d265, d2892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15001 p hg
    simpa only [d265, d2892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d265, d2892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15254 p hg
    simpa only [d265, d2892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15256 (p : Pattern) (guard : d5503 p = 1) : d266 p ≤ (0 : Int) + d2893 p := by
  cases selected : p 49 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d266, d2893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15196 p hg
    simpa only [d266, d2893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d266, d2893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15255 p hg
    simpa only [d266, d2893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15257 (p : Pattern) (guard : d5503 p = 1) : d267 p ≤ (0 : Int) + d2894 p := by
  cases selected : p 48 with
  | false =>
    have hg : d5503 p = 1 := by simpa only [d267, d2894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15151 p hg
    simpa only [d267, d2894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5503 p = 1 := by simpa only [d267, d2894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15256 p hg
    simpa only [d267, d2894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare15258 (p : Pattern) (guard : d0 p = 1) : d321 p ≤ (0 : Int) + d14 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare15259 (p : Pattern) (guard : d4474 p = 1) : d1682 p ≤ (0 : Int) + d14 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4474, d1682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4474, d1682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4474, d1682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15258 p hg
    simpa only [d4474, d1682, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
