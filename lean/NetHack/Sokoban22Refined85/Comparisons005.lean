/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons004
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare700 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (0 : Int) + d116 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d31, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare698 p hg
    simpa only [d31, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d31, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare699 p hg
    simpa only [d31, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare701 (p : Pattern) (guard : d1 p = 1) : d32 p ≤ (0 : Int) + d117 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d32, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare700 p hg
    simpa only [d32, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d32, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d32, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare702 (p : Pattern) (guard : d1 p = 1) : d33 p ≤ (0 : Int) + d118 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d33, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare680 p hg
    simpa only [d33, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d33, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare701 p hg
    simpa only [d33, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare703 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (0 : Int) + d7 p := by
  change (6 : Int) ≤ (0 : Int) + 7
  decide
theorem compare704 (p : Pattern) (guard : d1 p = 1) : d34 p ≤ (0 : Int) + d119 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d34, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare703 p hg
    simpa only [d34, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d34, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d34, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare705 (p : Pattern) (guard : d1 p = 1) : d35 p ≤ (0 : Int) + d120 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d35, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare703 p hg
    simpa only [d35, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d35, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare704 p hg
    simpa only [d35, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare706 (p : Pattern) (guard : d1 p = 1) : d36 p ≤ (0 : Int) + d121 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d36, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare705 p hg
    simpa only [d36, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d36, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d36, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare707 (p : Pattern) (guard : d1 p = 1) : d37 p ≤ (0 : Int) + d122 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d37, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare680 p hg
    simpa only [d37, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d37, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare706 p hg
    simpa only [d37, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare708 (p : Pattern) (guard : d1 p = 1) : d38 p ≤ (0 : Int) + d123 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d38, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare702 p hg
    simpa only [d38, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d38, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare707 p hg
    simpa only [d38, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare709 (p : Pattern) (guard : d1 p = 1) : d11 p ≤ (0 : Int) + d12 p := by
  change (11 : Int) ≤ (0 : Int) + 12
  decide
theorem compare710 (p : Pattern) (guard : d1 p = 1) : d39 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare709 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare711 (p : Pattern) (guard : d1 p = 1) : d40 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare709 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare710 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare712 (p : Pattern) (guard : d1 p = 1) : d41 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare711 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare713 (p : Pattern) (guard : d1 p = 1) : d42 p ≤ (0 : Int) + d124 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d42, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare680 p hg
    simpa only [d42, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d42, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare712 p hg
    simpa only [d42, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare714 (p : Pattern) (guard : d1 p = 1) : d43 p ≤ (0 : Int) + d125 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d43, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare685 p hg
    simpa only [d43, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d43, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d43, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare715 (p : Pattern) (guard : d1 p = 1) : d44 p ≤ (0 : Int) + d126 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d44, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare713 p hg
    simpa only [d44, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d44, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare714 p hg
    simpa only [d44, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare716 (p : Pattern) (guard : d1 p = 1) : d45 p ≤ (0 : Int) + d127 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d45, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare708 p hg
    simpa only [d45, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d45, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare715 p hg
    simpa only [d45, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare717 (p : Pattern) (guard : d1 p = 1) : d46 p ≤ (0 : Int) + d124 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d46, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare680 p hg
    simpa only [d46, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d46, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d46, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare718 (p : Pattern) (guard : d1 p = 1) : d47 p ≤ (0 : Int) + d126 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d47, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare717 p hg
    simpa only [d47, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d47, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare714 p hg
    simpa only [d47, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare719 (p : Pattern) (guard : d1 p = 1) : d48 p ≤ (0 : Int) + d70 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d48, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare692 p hg
    simpa only [d48, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d48, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d48, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare720 (p : Pattern) (guard : d1 p = 1) : d49 p ≤ (0 : Int) + d128 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d49, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare719 p hg
    simpa only [d49, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d49, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d49, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare721 (p : Pattern) (guard : d1 p = 1) : d50 p ≤ (0 : Int) + d129 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d50, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare718 p hg
    simpa only [d50, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d50, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare720 p hg
    simpa only [d50, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare722 (p : Pattern) (guard : d1 p = 1) : d51 p ≤ (0 : Int) + d130 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d51, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare716 p hg
    simpa only [d51, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d51, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare721 p hg
    simpa only [d51, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare723 (p : Pattern) (guard : d1 p = 1) : d52 p ≤ (0 : Int) + d131 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d52, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare697 p hg
    simpa only [d52, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d52, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare722 p hg
    simpa only [d52, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare724 (p : Pattern) (guard : d1 p = 1) : d53 p ≤ (0 : Int) + d132 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d53, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare700 p hg
    simpa only [d53, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d53, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare701 p hg
    simpa only [d53, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare725 (p : Pattern) (guard : d1 p = 1) : d54 p ≤ (0 : Int) + d133 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d54, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare682 p hg
    simpa only [d54, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d54, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare724 p hg
    simpa only [d54, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare726 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (0 : Int) + d134 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d55, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare687 p hg
    simpa only [d55, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d55, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare694 p hg
    simpa only [d55, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare727 (p : Pattern) (guard : d1 p = 1) : d56 p ≤ (0 : Int) + d135 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d56, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare725 p hg
    simpa only [d56, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d56, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare726 p hg
    simpa only [d56, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare728 (p : Pattern) (guard : d1 p = 1) : d10 p ≤ (0 : Int) + d11 p := by
  change (10 : Int) ≤ (0 : Int) + 11
  decide
theorem compare729 (p : Pattern) (guard : d1 p = 1) : d57 p ≤ (0 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d57, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare728 p hg
    simpa only [d57, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d57, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d57, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare730 (p : Pattern) (guard : d1 p = 1) : d58 p ≤ (0 : Int) + d40 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d58, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare728 p hg
    simpa only [d58, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d58, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare729 p hg
    simpa only [d58, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare731 (p : Pattern) (guard : d1 p = 1) : d59 p ≤ (0 : Int) + d41 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d59, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare730 p hg
    simpa only [d59, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d59, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d59, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare732 (p : Pattern) (guard : d1 p = 1) : d60 p ≤ (0 : Int) + d62 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d60, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare730 p hg
    simpa only [d60, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d60, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare731 p hg
    simpa only [d60, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare733 (p : Pattern) (guard : d1 p = 1) : d61 p ≤ (0 : Int) + d136 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d61, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare687 p hg
    simpa only [d61, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d61, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare732 p hg
    simpa only [d61, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare734 (p : Pattern) (guard : d1 p = 1) : d62 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare711 p hg
    simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare712 p hg
    simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare735 (p : Pattern) (guard : d1 p = 1) : d63 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare734 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare736 (p : Pattern) (guard : d1 p = 1) : d64 p ≤ (0 : Int) + d137 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d64, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare733 p hg
    simpa only [d64, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d64, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare735 p hg
    simpa only [d64, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare737 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (0 : Int) + d138 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d65, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare727 p hg
    simpa only [d65, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d65, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare736 p hg
    simpa only [d65, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare738 (p : Pattern) (guard : d1 p = 1) : d66 p ≤ (0 : Int) + d139 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d66, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare700 p hg
    simpa only [d66, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d66, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d66, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare739 (p : Pattern) (guard : d1 p = 1) : d67 p ≤ (0 : Int) + d140 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d67, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare707 p hg
    simpa only [d67, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d67, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare738 p hg
    simpa only [d67, d140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare740 (p : Pattern) (guard : d1 p = 1) : d68 p ≤ (0 : Int) + d141 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d68, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare714 p hg
    simpa only [d68, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d68, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare719 p hg
    simpa only [d68, d141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare741 (p : Pattern) (guard : d1 p = 1) : d69 p ≤ (0 : Int) + d142 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d69, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare739 p hg
    simpa only [d69, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d69, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare740 p hg
    simpa only [d69, d142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare742 (p : Pattern) (guard : d1 p = 1) : d70 p ≤ (0 : Int) + d72 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d70, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare730 p hg
    simpa only [d70, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d70, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d70, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare743 (p : Pattern) (guard : d1 p = 1) : d71 p ≤ (0 : Int) + d143 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d71, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare714 p hg
    simpa only [d71, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d71, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare742 p hg
    simpa only [d71, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare744 (p : Pattern) (guard : d1 p = 1) : d72 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare711 p hg
    simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare745 (p : Pattern) (guard : d1 p = 1) : d73 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare744 p hg
    simpa only [d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare746 (p : Pattern) (guard : d1 p = 1) : d74 p ≤ (0 : Int) + d144 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d74, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare743 p hg
    simpa only [d74, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d74, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare745 p hg
    simpa only [d74, d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare747 (p : Pattern) (guard : d1 p = 1) : d75 p ≤ (0 : Int) + d145 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d75, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare741 p hg
    simpa only [d75, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d75, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare746 p hg
    simpa only [d75, d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare748 (p : Pattern) (guard : d1 p = 1) : d76 p ≤ (0 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d76, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare737 p hg
    simpa only [d76, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d76, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare747 p hg
    simpa only [d76, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare749 (p : Pattern) (guard : d1 p = 1) : d77 p ≤ (0 : Int) + d147 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d77, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare723 p hg
    simpa only [d77, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d77, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare748 p hg
    simpa only [d77, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare750 (p : Pattern) (guard : d1 p = 1) : d78 p ≤ (0 : Int) + d148 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d78, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare705 p hg
    simpa only [d78, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d78, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare706 p hg
    simpa only [d78, d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare751 (p : Pattern) (guard : d1 p = 1) : d79 p ≤ (0 : Int) + d149 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d79, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare724 p hg
    simpa only [d79, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d79, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare750 p hg
    simpa only [d79, d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare752 (p : Pattern) (guard : d1 p = 1) : d80 p ≤ (0 : Int) + d150 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d80, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare751 p hg
    simpa only [d80, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d80, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare735 p hg
    simpa only [d80, d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare753 (p : Pattern) (guard : d1 p = 1) : d81 p ≤ (0 : Int) + d151 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d81, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare752 p hg
    simpa only [d81, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d81, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d81, d151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare754 (p : Pattern) (guard : d1 p = 1) : d82 p ≤ (0 : Int) + d152 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d82, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare697 p hg
    simpa only [d82, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d82, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare753 p hg
    simpa only [d82, d152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare755 (p : Pattern) (guard : d1 p = 1) : d83 p ≤ (0 : Int) + d153 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d83, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare750 p hg
    simpa only [d83, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d83, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d83, d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare756 (p : Pattern) (guard : d1 p = 1) : d84 p ≤ (0 : Int) + d154 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d84, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare755 p hg
    simpa only [d84, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d84, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d84, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare757 (p : Pattern) (guard : d1 p = 1) : d85 p ≤ (0 : Int) + d155 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d85, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare756 p hg
    simpa only [d85, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d85, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d85, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare758 (p : Pattern) (guard : d1 p = 1) : d86 p ≤ (0 : Int) + d156 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d86, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare737 p hg
    simpa only [d86, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d86, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare757 p hg
    simpa only [d86, d156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare759 (p : Pattern) (guard : d1 p = 1) : d87 p ≤ (0 : Int) + d157 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d87, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare754 p hg
    simpa only [d87, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d87, d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare758 p hg
    simpa only [d87, d157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare760 (p : Pattern) (guard : d1 p = 1) : d88 p ≤ (0 : Int) + d158 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d88, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare749 p hg
    simpa only [d88, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d88, d158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare759 p hg
    simpa only [d88, d158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare761 (p : Pattern) (guard : d1 p = 1) : d89 p ≤ (0 : Int) + d112 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d89, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare694 p hg
    simpa only [d89, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d89, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare734 p hg
    simpa only [d89, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare762 (p : Pattern) (guard : d1 p = 1) : d90 p ≤ (0 : Int) + d159 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d90, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare761 p hg
    simpa only [d90, d159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d90, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare735 p hg
    simpa only [d90, d159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare763 (p : Pattern) (guard : d1 p = 1) : d91 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare735 p hg
    simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare764 (p : Pattern) (guard : d1 p = 1) : d92 p ≤ (0 : Int) + d160 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d92, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare762 p hg
    simpa only [d92, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d92, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare763 p hg
    simpa only [d92, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare765 (p : Pattern) (guard : d1 p = 1) : d93 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare763 p hg
    simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare766 (p : Pattern) (guard : d1 p = 1) : d94 p ≤ (0 : Int) + d161 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d94, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare764 p hg
    simpa only [d94, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d94, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare765 p hg
    simpa only [d94, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare767 (p : Pattern) (guard : d1 p = 1) : d95 p ≤ (0 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare765 p hg
    simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare768 (p : Pattern) (guard : d1 p = 1) : d96 p ≤ (0 : Int) + d162 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d96, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare766 p hg
    simpa only [d96, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d96, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare767 p hg
    simpa only [d96, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare769 (p : Pattern) (guard : d1 p = 1) : d97 p ≤ (0 : Int) + d163 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d97, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare759 p hg
    simpa only [d97, d163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d97, d163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare768 p hg
    simpa only [d97, d163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare770 (p : Pattern) (guard : d1 p = 1) : d98 p ≤ (0 : Int) + d164 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d98, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare760 p hg
    simpa only [d98, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d98, d164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare769 p hg
    simpa only [d98, d164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare771 (p : Pattern) (guard : d1 p = 1) : d99 p ≤ (0 : Int) + d165 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d99, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare759 p hg
    simpa only [d99, d165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d99, d165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d99, d165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare772 (p : Pattern) (guard : d1 p = 1) : d100 p ≤ (0 : Int) + d166 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d100, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare760 p hg
    simpa only [d100, d166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d100, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare771 p hg
    simpa only [d100, d166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare773 (p : Pattern) (guard : d1 p = 1) : d101 p ≤ (0 : Int) + d167 p := by
  cases selected : p 115 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d101, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare770 p hg
    simpa only [d101, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d101, d167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare772 p hg
    simpa only [d101, d167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare774 (p : Pattern) (guard : d0 p = 1) : d167 p ≤ (0 : Int) + d167 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare775 (p : Pattern) (guard : d4042 p = 1) : d168 p ≤ (0 : Int) + d167 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4042, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare773 p hg
    simpa only [d4042, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4042, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare774 p hg
    simpa only [d4042, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare776 (p : Pattern) (guard : d4042 p = 1) : d169 p ≤ (0 : Int) + d4054 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4042 p = 1 := by simpa only [d169, d4054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare676 p hg
    simpa only [d169, d4054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4042 p = 1 := by simpa only [d169, d4054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare775 p hg
    simpa only [d169, d4054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare777 (p : Pattern) (guard : d1 p = 1) : d98 p ≤ (0 : Int) + d98 p := by
  omega
theorem compare778 (p : Pattern) (guard : d1 p = 1) : d29 p ≤ (0 : Int) + d29 p := by
  omega
theorem compare779 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) ≤ (0 : Int) + 2
  decide
theorem compare780 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (0 : Int) + d30 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d13, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare779 p hg
    simpa only [d13, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d13, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d13, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare781 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d31 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare779 p hg
    simpa only [d14, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare780 p hg
    simpa only [d14, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare782 (p : Pattern) (guard : d1 p = 1) : d32 p ≤ (0 : Int) + d32 p := by
  omega
theorem compare783 (p : Pattern) (guard : d1 p = 1) : d33 p ≤ (0 : Int) + d53 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d33, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare781 p hg
    simpa only [d33, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d33, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare782 p hg
    simpa only [d33, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare784 (p : Pattern) (guard : d1 p = 1) : d36 p ≤ (0 : Int) + d36 p := by
  omega
theorem compare785 (p : Pattern) (guard : d1 p = 1) : d37 p ≤ (0 : Int) + d170 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d37, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare781 p hg
    simpa only [d37, d170, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d37, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare784 p hg
    simpa only [d37, d170, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare786 (p : Pattern) (guard : d1 p = 1) : d38 p ≤ (0 : Int) + d171 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d38, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare783 p hg
    simpa only [d38, d171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d38, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare785 p hg
    simpa only [d38, d171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare787 (p : Pattern) (guard : d1 p = 1) : d41 p ≤ (0 : Int) + d41 p := by
  omega
theorem compare788 (p : Pattern) (guard : d1 p = 1) : d42 p ≤ (0 : Int) + d172 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d42, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare781 p hg
    simpa only [d42, d172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d42, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare787 p hg
    simpa only [d42, d172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare789 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (0 : Int) + d6 p := by
  change (4 : Int) ≤ (0 : Int) + 6
  decide
theorem compare790 (p : Pattern) (guard : d1 p = 1) : d17 p ≤ (0 : Int) + d34 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d17, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare789 p hg
    simpa only [d17, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d17, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d17, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare791 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (0 : Int) + d35 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d18, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare789 p hg
    simpa only [d18, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d18, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare790 p hg
    simpa only [d18, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare792 (p : Pattern) (guard : d1 p = 1) : d43 p ≤ (0 : Int) + d173 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d43, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare791 p hg
    simpa only [d43, d173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d43, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d43, d173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare793 (p : Pattern) (guard : d1 p = 1) : d44 p ≤ (0 : Int) + d174 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d44, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare788 p hg
    simpa only [d44, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d44, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare792 p hg
    simpa only [d44, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare794 (p : Pattern) (guard : d1 p = 1) : d45 p ≤ (0 : Int) + d175 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d45, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare786 p hg
    simpa only [d45, d175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d45, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare793 p hg
    simpa only [d45, d175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare795 (p : Pattern) (guard : d1 p = 1) : d46 p ≤ (0 : Int) + d66 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d46, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare781 p hg
    simpa only [d46, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d46, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d46, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare796 (p : Pattern) (guard : d1 p = 1) : d47 p ≤ (0 : Int) + d176 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d47, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare795 p hg
    simpa only [d47, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d47, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare792 p hg
    simpa only [d47, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare797 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (0 : Int) + d11 p := by
  change (9 : Int) ≤ (0 : Int) + 11
  decide
theorem compare798 (p : Pattern) (guard : d1 p = 1) : d23 p ≤ (0 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d23, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare797 p hg
    simpa only [d23, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d23, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d23, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare799 (p : Pattern) (guard : d1 p = 1) : d24 p ≤ (0 : Int) + d40 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d24, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare797 p hg
    simpa only [d24, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d24, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare798 p hg
    simpa only [d24, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare800 (p : Pattern) (guard : d1 p = 1) : d48 p ≤ (0 : Int) + d72 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d48, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare799 p hg
    simpa only [d48, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d48, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d48, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare801 (p : Pattern) (guard : d1 p = 1) : d49 p ≤ (0 : Int) + d73 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d49, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare800 p hg
    simpa only [d49, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d49, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d49, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare802 (p : Pattern) (guard : d1 p = 1) : d50 p ≤ (0 : Int) + d177 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d50, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare796 p hg
    simpa only [d50, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d50, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare801 p hg
    simpa only [d50, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare803 (p : Pattern) (guard : d1 p = 1) : d51 p ≤ (0 : Int) + d178 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d51, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare794 p hg
    simpa only [d51, d178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d51, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare802 p hg
    simpa only [d51, d178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare804 (p : Pattern) (guard : d1 p = 1) : d52 p ≤ (0 : Int) + d179 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d52, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare778 p hg
    simpa only [d52, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d52, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare803 p hg
    simpa only [d52, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare805 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (0 : Int) + d65 p := by
  omega
theorem compare806 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (0 : Int) + d4 p := by
  change (2 : Int) ≤ (0 : Int) + 4
  decide
theorem compare807 (p : Pattern) (guard : d1 p = 1) : d30 p ≤ (0 : Int) + d17 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d30, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare806 p hg
    simpa only [d30, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d30, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d30, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare808 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (0 : Int) + d18 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d31, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare806 p hg
    simpa only [d31, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d31, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare807 p hg
    simpa only [d31, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare809 (p : Pattern) (guard : d1 p = 1) : d66 p ≤ (0 : Int) + d43 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d66, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare808 p hg
    simpa only [d66, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d66, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d66, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare810 (p : Pattern) (guard : d1 p = 1) : d67 p ≤ (0 : Int) + d180 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d67, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare785 p hg
    simpa only [d67, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d67, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare809 p hg
    simpa only [d67, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare811 (p : Pattern) (guard : d1 p = 1) : d68 p ≤ (0 : Int) + d181 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d68, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare792 p hg
    simpa only [d68, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d68, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare800 p hg
    simpa only [d68, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare812 (p : Pattern) (guard : d1 p = 1) : d69 p ≤ (0 : Int) + d182 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d69, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare810 p hg
    simpa only [d69, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d69, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare811 p hg
    simpa only [d69, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare813 (p : Pattern) (guard : d1 p = 1) : d10 p ≤ (0 : Int) + d12 p := by
  change (10 : Int) ≤ (0 : Int) + 12
  decide
theorem compare814 (p : Pattern) (guard : d1 p = 1) : d57 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare813 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare815 (p : Pattern) (guard : d1 p = 1) : d58 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare813 p hg
    simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare814 p hg
    simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare816 (p : Pattern) (guard : d1 p = 1) : d70 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare815 p hg
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare817 (p : Pattern) (guard : d1 p = 1) : d71 p ≤ (0 : Int) + d183 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d71, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare792 p hg
    simpa only [d71, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d71, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare816 p hg
    simpa only [d71, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare818 (p : Pattern) (guard : d1 p = 1) : d74 p ≤ (0 : Int) + d184 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d74, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare817 p hg
    simpa only [d74, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d74, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare745 p hg
    simpa only [d74, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare819 (p : Pattern) (guard : d1 p = 1) : d75 p ≤ (0 : Int) + d185 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d75, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare812 p hg
    simpa only [d75, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d75, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare818 p hg
    simpa only [d75, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare820 (p : Pattern) (guard : d1 p = 1) : d76 p ≤ (0 : Int) + d186 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d76, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare805 p hg
    simpa only [d76, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d76, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare819 p hg
    simpa only [d76, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare821 (p : Pattern) (guard : d1 p = 1) : d77 p ≤ (0 : Int) + d187 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d77, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare804 p hg
    simpa only [d77, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d77, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare820 p hg
    simpa only [d77, d187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare822 (p : Pattern) (guard : d1 p = 1) : d16 p ≤ (0 : Int) + d16 p := by
  omega
theorem compare823 (p : Pattern) (guard : d1 p = 1) : d15 p ≤ (0 : Int) + d32 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d15, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare781 p hg
    simpa only [d15, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d15, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d15, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare824 (p : Pattern) (guard : d1 p = 1) : d16 p ≤ (0 : Int) + d53 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d16, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare781 p hg
    simpa only [d16, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d16, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare823 p hg
    simpa only [d16, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare825 (p : Pattern) (guard : d1 p = 1) : d19 p ≤ (0 : Int) + d36 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d19, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare791 p hg
    simpa only [d19, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d19, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d19, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare826 (p : Pattern) (guard : d1 p = 1) : d20 p ≤ (0 : Int) + d78 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d20, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare791 p hg
    simpa only [d20, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d20, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare825 p hg
    simpa only [d20, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare827 (p : Pattern) (guard : d1 p = 1) : d21 p ≤ (0 : Int) + d79 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d21, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare824 p hg
    simpa only [d21, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d21, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare826 p hg
    simpa only [d21, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare828 (p : Pattern) (guard : d1 p = 1) : d22 p ≤ (0 : Int) + d188 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d22, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d22, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d22, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare827 p hg
    simpa only [d22, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare829 (p : Pattern) (guard : d1 p = 1) : d25 p ≤ (0 : Int) + d41 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d25, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare799 p hg
    simpa only [d25, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d25, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d25, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare830 (p : Pattern) (guard : d1 p = 1) : d26 p ≤ (0 : Int) + d62 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d26, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare799 p hg
    simpa only [d26, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d26, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare829 p hg
    simpa only [d26, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare831 (p : Pattern) (guard : d1 p = 1) : d27 p ≤ (0 : Int) + d63 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d27, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare830 p hg
    simpa only [d27, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d27, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d27, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare832 (p : Pattern) (guard : d1 p = 1) : d28 p ≤ (0 : Int) + d80 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d28, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare827 p hg
    simpa only [d28, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d28, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare831 p hg
    simpa only [d28, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare833 (p : Pattern) (guard : d1 p = 1) : d29 p ≤ (0 : Int) + d189 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d29, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare828 p hg
    simpa only [d29, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d29, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare832 p hg
    simpa only [d29, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare834 (p : Pattern) (guard : d1 p = 1) : d32 p ≤ (0 : Int) + d19 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d32, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare808 p hg
    simpa only [d32, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d32, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d32, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare835 (p : Pattern) (guard : d1 p = 1) : d53 p ≤ (0 : Int) + d20 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d53, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare808 p hg
    simpa only [d53, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d53, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare834 p hg
    simpa only [d53, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare836 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (0 : Int) + d8 p := by
  change (6 : Int) ≤ (0 : Int) + 8
  decide
theorem compare837 (p : Pattern) (guard : d1 p = 1) : d34 p ≤ (0 : Int) + d190 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d34, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare836 p hg
    simpa only [d34, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d34, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d34, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare838 (p : Pattern) (guard : d1 p = 1) : d35 p ≤ (0 : Int) + d191 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d35, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare836 p hg
    simpa only [d35, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d35, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare837 p hg
    simpa only [d35, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare839 (p : Pattern) (guard : d1 p = 1) : d36 p ≤ (0 : Int) + d192 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d36, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare838 p hg
    simpa only [d36, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d36, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d36, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
