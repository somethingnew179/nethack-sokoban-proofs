import NetHack.Soko22Hazard87.Compare054
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare13750 (p : Pattern) (guard : d49 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 93 with
  | false =>
    have hg : d41 p = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13749 p hg
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13751 (p : Pattern) (guard : d50 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 91 with
  | false =>
    have hg : d49 p = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13750 p hg
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13752 (p : Pattern) (guard : d51 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 90 with
  | false =>
    have hg : d50 p = 1 := by simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13751 p hg
    simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13753 (p : Pattern) (guard : d52 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 89 with
  | false =>
    have hg : d51 p = 1 := by simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13752 p hg
    simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13754 (p : Pattern) (guard : d53 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d52 p = 1 := by simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13753 p hg
    simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13755 (p : Pattern) (guard : d54 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53 p = 1 := by simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13754 p hg
    simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13756 (p : Pattern) (guard : d60 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d60, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54 p = 1 := by simpa only [d60, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13755 p hg
    simpa only [d60, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13757 (p : Pattern) (guard : d61 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13726 p hg
    simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60 p = 1 := by simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13756 p hg
    simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13758 (p : Pattern) (guard : d62 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 69 with
  | false =>
    have hg : d61 p = 1 := by simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13757 p hg
    simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13726 p hg
    simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13759 (p : Pattern) (guard : d63 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 51 with
  | false =>
    have hg : d62 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13758 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13726 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13760 (p : Pattern) (guard : d64 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 50 with
  | false =>
    have hg : d63 p = 1 := by simpa only [d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13759 p hg
    simpa only [d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13726 p hg
    simpa only [d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13761 (p : Pattern) (guard : d65 p = 1) : d48359 p ≤ (1 : Int) + d171289 p := by
  cases selected : p 49 with
  | false =>
    have hg : d59 p = 1 := by simpa only [d65, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13725 p hg
    simpa only [d65, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64 p = 1 := by simpa only [d65, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13760 p hg
    simpa only [d65, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13762 (p : Pattern) (guard : d0 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13763 (p : Pattern) (guard : d0 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13764 (p : Pattern) (guard : d0 p = 1) : d48317 p ≤ (1 : Int) + d48204 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13765 (p : Pattern) (guard : d0 p = 1) : d48360 p ≤ (1 : Int) + d48195 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13766 (p : Pattern) (guard : d68 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare13767 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (1 : Int) + d48202 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13768 (p : Pattern) (guard : d69 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d68 p = 1 := by simpa only [d69, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13766 p hg
    simpa only [d69, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d69, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d69, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13769 (p : Pattern) (guard : d0 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13770 (p : Pattern) (guard : d70 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d69 p = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13768 p hg
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13769 p hg
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13771 (p : Pattern) (guard : d71 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d70 p = 1 := by simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13770 p hg
    simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13769 p hg
    simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13772 (p : Pattern) (guard : d72 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 157 with
  | false =>
    have hg : d71 p = 1 := by simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13771 p hg
    simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13769 p hg
    simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13773 (p : Pattern) (guard : d73 p = 1) : d48362 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d73, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13765 p hg
    simpa only [d73, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d72 p = 1 := by simpa only [d73, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13772 p hg
    simpa only [d73, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13774 (p : Pattern) (guard : d74 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d74, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13764 p hg
    simpa only [d74, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d73 p = 1 := by simpa only [d74, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13773 p hg
    simpa only [d74, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13775 (p : Pattern) (guard : d0 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13776 (p : Pattern) (guard : d75 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 136 with
  | false =>
    have hg : d74 p = 1 := by simpa only [d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13774 p hg
    simpa only [d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13775 p hg
    simpa only [d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13777 (p : Pattern) (guard : d76 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 135 with
  | false =>
    have hg : d75 p = 1 := by simpa only [d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13776 p hg
    simpa only [d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13775 p hg
    simpa only [d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13778 (p : Pattern) (guard : d77 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 119 with
  | false =>
    have hg : d76 p = 1 := by simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13777 p hg
    simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13775 p hg
    simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13779 (p : Pattern) (guard : d0 p = 1) : d48364 p ≤ (1 : Int) + d48204 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13780 (p : Pattern) (guard : d78 p = 1) : d48365 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 116 with
  | false =>
    have hg : d77 p = 1 := by simpa only [d78, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13778 p hg
    simpa only [d78, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d78, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13779 p hg
    simpa only [d78, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13781 (p : Pattern) (guard : d79 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d79, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d79, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d78 p = 1 := by simpa only [d79, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13780 p hg
    simpa only [d79, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13782 (p : Pattern) (guard : d80 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 113 with
  | false =>
    have hg : d79 p = 1 := by simpa only [d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13781 p hg
    simpa only [d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13783 (p : Pattern) (guard : d81 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 96 with
  | false =>
    have hg : d80 p = 1 := by simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13782 p hg
    simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13784 (p : Pattern) (guard : d82 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 95 with
  | false =>
    have hg : d81 p = 1 := by simpa only [d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13783 p hg
    simpa only [d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13785 (p : Pattern) (guard : d83 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 93 with
  | false =>
    have hg : d82 p = 1 := by simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13784 p hg
    simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13786 (p : Pattern) (guard : d84 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 91 with
  | false =>
    have hg : d83 p = 1 := by simpa only [d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13785 p hg
    simpa only [d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13787 (p : Pattern) (guard : d85 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 90 with
  | false =>
    have hg : d84 p = 1 := by simpa only [d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13786 p hg
    simpa only [d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13788 (p : Pattern) (guard : d86 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 89 with
  | false =>
    have hg : d85 p = 1 := by simpa only [d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13787 p hg
    simpa only [d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13789 (p : Pattern) (guard : d87 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d86 p = 1 := by simpa only [d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13788 p hg
    simpa only [d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13790 (p : Pattern) (guard : d88 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d87 p = 1 := by simpa only [d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13789 p hg
    simpa only [d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13791 (p : Pattern) (guard : d89 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d89, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d89, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d88 p = 1 := by simpa only [d89, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13790 p hg
    simpa only [d89, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13792 (p : Pattern) (guard : d90 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13762 p hg
    simpa only [d90, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d89 p = 1 := by simpa only [d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13791 p hg
    simpa only [d90, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13793 (p : Pattern) (guard : d91 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 69 with
  | false =>
    have hg : d90 p = 1 := by simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13792 p hg
    simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13762 p hg
    simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13794 (p : Pattern) (guard : d92 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 51 with
  | false =>
    have hg : d91 p = 1 := by simpa only [d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13793 p hg
    simpa only [d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13762 p hg
    simpa only [d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13795 (p : Pattern) (guard : d93 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 50 with
  | false =>
    have hg : d92 p = 1 := by simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13794 p hg
    simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13762 p hg
    simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13796 (p : Pattern) (guard : d0 p = 1) : d48386 p ≤ (1 : Int) + d171293 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13797 (p : Pattern) (guard : d94 p = 1) : d48387 p ≤ (1 : Int) + d171294 p := by
  cases selected : p 49 with
  | false =>
    have hg : d93 p = 1 := by simpa only [d94, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13795 p hg
    simpa only [d94, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d94, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13796 p hg
    simpa only [d94, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13798 (p : Pattern) (guard : d95 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 48 with
  | false =>
    have hg : d65 p = 1 := by simpa only [d95, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13761 p hg
    simpa only [d95, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d94 p = 1 := by simpa only [d95, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13797 p hg
    simpa only [d95, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13799 (p : Pattern) (guard : d96 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d95 p = 1 := by simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13798 p hg
    simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13800 (p : Pattern) (guard : d97 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d96 p = 1 := by simpa only [d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13799 p hg
    simpa only [d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13801 (p : Pattern) (guard : d98 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d97 p = 1 := by simpa only [d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13800 p hg
    simpa only [d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13802 (p : Pattern) (guard : d99 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d98 p = 1 := by simpa only [d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13801 p hg
    simpa only [d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13803 (p : Pattern) (guard : d100 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d43 p = 1 := by simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13691 p hg
    simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13804 (p : Pattern) (guard : d101 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d100 p = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13803 p hg
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13805 (p : Pattern) (guard : d102 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101 p = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13804 p hg
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13806 (p : Pattern) (guard : d103 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d102 p = 1 := by simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13805 p hg
    simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13807 (p : Pattern) (guard : d104 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d104, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d104, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d103 p = 1 := by simpa only [d104, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13806 p hg
    simpa only [d104, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13808 (p : Pattern) (guard : d105 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13665 p hg
    simpa only [d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d104 p = 1 := by simpa only [d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13807 p hg
    simpa only [d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13809 (p : Pattern) (guard : d106 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 69 with
  | false =>
    have hg : d105 p = 1 := by simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13808 p hg
    simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13665 p hg
    simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13810 (p : Pattern) (guard : d100 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d43 p = 1 := by simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13710 p hg
    simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13811 (p : Pattern) (guard : d101 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d100 p = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13810 p hg
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13812 (p : Pattern) (guard : d102 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101 p = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13811 p hg
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13813 (p : Pattern) (guard : d103 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d102 p = 1 := by simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13812 p hg
    simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13814 (p : Pattern) (guard : d107 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d50 p = 1 := by simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13716 p hg
    simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13815 (p : Pattern) (guard : d108 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d107 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13814 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13816 (p : Pattern) (guard : d109 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d108 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13815 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13817 (p : Pattern) (guard : d110 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d109 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13816 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13818 (p : Pattern) (guard : d111 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d103 p = 1 := by simpa only [d111, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13813 p hg
    simpa only [d111, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d110 p = 1 := by simpa only [d111, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13817 p hg
    simpa only [d111, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13819 (p : Pattern) (guard : d112 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 70 with
  | false =>
    have hg : d104 p = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13807 p hg
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d111 p = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13818 p hg
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13820 (p : Pattern) (guard : d113 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 69 with
  | false =>
    have hg : d112 p = 1 := by simpa only [d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13819 p hg
    simpa only [d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13665 p hg
    simpa only [d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13821 (p : Pattern) (guard : d114 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 51 with
  | false =>
    have hg : d106 p = 1 := by simpa only [d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13809 p hg
    simpa only [d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d113 p = 1 := by simpa only [d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13820 p hg
    simpa only [d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13822 (p : Pattern) (guard : d115 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d40 p = 1 := by simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13688 p hg
    simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13823 (p : Pattern) (guard : d116 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d115 p = 1 := by simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13822 p hg
    simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13824 (p : Pattern) (guard : d117 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d116 p = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13823 p hg
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13825 (p : Pattern) (guard : d118 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d117 p = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13824 p hg
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13826 (p : Pattern) (guard : d119 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d118 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13825 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13827 (p : Pattern) (guard : d120 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d119 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13826 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13828 (p : Pattern) (guard : d121 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d39 p = 1 := by simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13687 p hg
    simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13829 (p : Pattern) (guard : d122 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d121 p = 1 := by simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13828 p hg
    simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13830 (p : Pattern) (guard : d123 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d122 p = 1 := by simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13829 p hg
    simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13831 (p : Pattern) (guard : d124 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d123 p = 1 := by simpa only [d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13830 p hg
    simpa only [d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13832 (p : Pattern) (guard : d125 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d124 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13831 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13833 (p : Pattern) (guard : d126 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d125 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13832 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13834 (p : Pattern) (guard : d141 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare13835 (p : Pattern) (guard : d142 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d141 p = 1 := by simpa only [d142, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13834 p hg
    simpa only [d142, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d142, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d142, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13836 (p : Pattern) (guard : d143 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d142 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13835 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d28 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13673 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13837 (p : Pattern) (guard : d144 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d143 p = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13836 p hg
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d29 p = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13675 p hg
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13838 (p : Pattern) (guard : d145 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 157 with
  | false =>
    have hg : d144 p = 1 := by simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13837 p hg
    simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d30 p = 1 := by simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13676 p hg
    simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13839 (p : Pattern) (guard : d146 p = 1) : d48326 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d146, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13670 p hg
    simpa only [d146, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d145 p = 1 := by simpa only [d146, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13838 p hg
    simpa only [d146, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13840 (p : Pattern) (guard : d147 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d147, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13669 p hg
    simpa only [d147, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d146 p = 1 := by simpa only [d147, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13839 p hg
    simpa only [d147, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13841 (p : Pattern) (guard : d148 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d147 p = 1 := by simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13840 p hg
    simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d33 p = 1 := by simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13679 p hg
    simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13842 (p : Pattern) (guard : d149 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d148 p = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13841 p hg
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34 p = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13681 p hg
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13843 (p : Pattern) (guard : d150 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d149 p = 1 := by simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13842 p hg
    simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13680 p hg
    simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13844 (p : Pattern) (guard : d151 p = 1) : d48338 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d150 p = 1 := by simpa only [d151, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13843 p hg
    simpa only [d151, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d151, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d151, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13845 (p : Pattern) (guard : d152 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d152, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d152, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d151 p = 1 := by simpa only [d152, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13844 p hg
    simpa only [d152, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13846 (p : Pattern) (guard : d153 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d152 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13845 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13686 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13847 (p : Pattern) (guard : d154 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d153 p = 1 := by simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13846 p hg
    simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13848 (p : Pattern) (guard : d155 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d154 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13847 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13849 (p : Pattern) (guard : d156 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d155 p = 1 := by simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13848 p hg
    simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13850 (p : Pattern) (guard : d157 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d156 p = 1 := by simpa only [d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13849 p hg
    simpa only [d157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d42 p = 1 := by simpa only [d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13690 p hg
    simpa only [d157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13851 (p : Pattern) (guard : d4335 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d157 p = 1 := by simpa only [d4335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13850 p hg
    simpa only [d4335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d4335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13852 (p : Pattern) (guard : d4336 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d4335 p = 1 := by simpa only [d4336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13851 p hg
    simpa only [d4336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44 p = 1 := by simpa only [d4336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13692 p hg
    simpa only [d4336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13853 (p : Pattern) (guard : d51641 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d126 p = 1 := by simpa only [d51641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13833 p hg
    simpa only [d51641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4336 p = 1 := by simpa only [d51641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13852 p hg
    simpa only [d51641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13854 (p : Pattern) (guard : d51642 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d120 p = 1 := by simpa only [d51642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13827 p hg
    simpa only [d51642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51641 p = 1 := by simpa only [d51642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13853 p hg
    simpa only [d51642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13855 (p : Pattern) (guard : d51643 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d51643, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d51643, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51642 p = 1 := by simpa only [d51643, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13854 p hg
    simpa only [d51643, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13856 (p : Pattern) (guard : d115 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d40 p = 1 := by simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13707 p hg
    simpa only [d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13857 (p : Pattern) (guard : d116 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d115 p = 1 := by simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13856 p hg
    simpa only [d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13858 (p : Pattern) (guard : d117 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d116 p = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13857 p hg
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13859 (p : Pattern) (guard : d118 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d117 p = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13858 p hg
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13860 (p : Pattern) (guard : d119 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d118 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13859 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13861 (p : Pattern) (guard : d120 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d119 p = 1 := by simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13860 p hg
    simpa only [d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13862 (p : Pattern) (guard : d121 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d39 p = 1 := by simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13706 p hg
    simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13863 (p : Pattern) (guard : d122 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d121 p = 1 := by simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13862 p hg
    simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13864 (p : Pattern) (guard : d123 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d122 p = 1 := by simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13863 p hg
    simpa only [d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13865 (p : Pattern) (guard : d124 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d123 p = 1 := by simpa only [d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13864 p hg
    simpa only [d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13866 (p : Pattern) (guard : d125 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d124 p = 1 := by simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13865 p hg
    simpa only [d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13867 (p : Pattern) (guard : d126 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d125 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13866 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13868 (p : Pattern) (guard : d147 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d147, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13698 p hg
    simpa only [d147, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d146 p = 1 := by simpa only [d147, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13839 p hg
    simpa only [d147, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13869 (p : Pattern) (guard : d148 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d147 p = 1 := by simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13868 p hg
    simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d33 p = 1 := by simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13699 p hg
    simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13870 (p : Pattern) (guard : d149 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d148 p = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13869 p hg
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34 p = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13701 p hg
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13871 (p : Pattern) (guard : d150 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d149 p = 1 := by simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13870 p hg
    simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13700 p hg
    simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13872 (p : Pattern) (guard : d151 p = 1) : d48329 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d150 p = 1 := by simpa only [d151, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13871 p hg
    simpa only [d151, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d151, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d151, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13873 (p : Pattern) (guard : d152 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d152, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13697 p hg
    simpa only [d152, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d151 p = 1 := by simpa only [d152, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13872 p hg
    simpa only [d152, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13874 (p : Pattern) (guard : d153 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d152 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13873 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13705 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13875 (p : Pattern) (guard : d154 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d153 p = 1 := by simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13874 p hg
    simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13876 (p : Pattern) (guard : d155 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d154 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13875 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13877 (p : Pattern) (guard : d156 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d155 p = 1 := by simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13876 p hg
    simpa only [d156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13878 (p : Pattern) (guard : d157 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d156 p = 1 := by simpa only [d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13877 p hg
    simpa only [d157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d42 p = 1 := by simpa only [d157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13709 p hg
    simpa only [d157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13879 (p : Pattern) (guard : d4335 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d157 p = 1 := by simpa only [d4335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13878 p hg
    simpa only [d4335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d4335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13880 (p : Pattern) (guard : d4336 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d4335 p = 1 := by simpa only [d4336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13879 p hg
    simpa only [d4336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d44 p = 1 := by simpa only [d4336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13711 p hg
    simpa only [d4336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13881 (p : Pattern) (guard : d51641 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d126 p = 1 := by simpa only [d51641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13867 p hg
    simpa only [d51641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4336 p = 1 := by simpa only [d51641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13880 p hg
    simpa only [d51641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13882 (p : Pattern) (guard : d51642 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d120 p = 1 := by simpa only [d51642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13861 p hg
    simpa only [d51642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51641 p = 1 := by simpa only [d51642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13881 p hg
    simpa only [d51642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13883 (p : Pattern) (guard : d194 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d115 p = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13822 p hg
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13884 (p : Pattern) (guard : d195 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d194 p = 1 := by simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13883 p hg
    simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13885 (p : Pattern) (guard : d196 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d195 p = 1 := by simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13884 p hg
    simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13886 (p : Pattern) (guard : d197 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d196 p = 1 := by simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13885 p hg
    simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13887 (p : Pattern) (guard : d198 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d197 p = 1 := by simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13886 p hg
    simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13888 (p : Pattern) (guard : d199 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d122 p = 1 := by simpa only [d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13829 p hg
    simpa only [d199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13889 (p : Pattern) (guard : d200 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d199 p = 1 := by simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13888 p hg
    simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13890 (p : Pattern) (guard : d201 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d200 p = 1 := by simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13889 p hg
    simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13891 (p : Pattern) (guard : d202 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d201 p = 1 := by simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13890 p hg
    simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13892 (p : Pattern) (guard : d203 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d155 p = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13848 p hg
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13893 (p : Pattern) (guard : d204 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d203 p = 1 := by simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13892 p hg
    simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d49 p = 1 := by simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13715 p hg
    simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13894 (p : Pattern) (guard : d4340 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d204 p = 1 := by simpa only [d4340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13893 p hg
    simpa only [d4340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d4340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13895 (p : Pattern) (guard : d4341 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d4340 p = 1 := by simpa only [d4341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13894 p hg
    simpa only [d4341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51 p = 1 := by simpa only [d4341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13717 p hg
    simpa only [d4341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13896 (p : Pattern) (guard : d51644 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d202 p = 1 := by simpa only [d51644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13891 p hg
    simpa only [d51644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4341 p = 1 := by simpa only [d51644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13895 p hg
    simpa only [d51644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13897 (p : Pattern) (guard : d51645 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d198 p = 1 := by simpa only [d51645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13887 p hg
    simpa only [d51645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51644 p = 1 := by simpa only [d51645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13896 p hg
    simpa only [d51645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13898 (p : Pattern) (guard : d51646 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d51642 p = 1 := by simpa only [d51646, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13882 p hg
    simpa only [d51646, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51645 p = 1 := by simpa only [d51646, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13897 p hg
    simpa only [d51646, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13899 (p : Pattern) (guard : d51647 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 70 with
  | false =>
    have hg : d51643 p = 1 := by simpa only [d51647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13855 p hg
    simpa only [d51647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51646 p = 1 := by simpa only [d51647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13898 p hg
    simpa only [d51647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13900 (p : Pattern) (guard : d213 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d103 p = 1 := by simpa only [d213, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13813 p hg
    simpa only [d213, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d213, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d213, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13901 (p : Pattern) (guard : d214 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 70 with
  | false =>
    have hg : d213 p = 1 := by simpa only [d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13900 p hg
    simpa only [d214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13665 p hg
    simpa only [d214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13902 (p : Pattern) (guard : d51648 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 69 with
  | false =>
    have hg : d51647 p = 1 := by simpa only [d51648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13899 p hg
    simpa only [d51648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d214 p = 1 := by simpa only [d51648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13901 p hg
    simpa only [d51648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13903 (p : Pattern) (guard : d51649 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 51 with
  | false =>
    have hg : d51648 p = 1 := by simpa only [d51649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13902 p hg
    simpa only [d51649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d51649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13665 p hg
    simpa only [d51649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13904 (p : Pattern) (guard : d51650 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 50 with
  | false =>
    have hg : d114 p = 1 := by simpa only [d51650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13821 p hg
    simpa only [d51650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51649 p = 1 := by simpa only [d51650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13903 p hg
    simpa only [d51650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13905 (p : Pattern) (guard : d141 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare13906 (p : Pattern) (guard : d142 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d141 p = 1 := by simpa only [d142, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13905 p hg
    simpa only [d142, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d142, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d142, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13907 (p : Pattern) (guard : d143 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d142 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13906 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d28 p = 1 := by simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13733 p hg
    simpa only [d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13908 (p : Pattern) (guard : d144 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d143 p = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13907 p hg
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d29 p = 1 := by simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13735 p hg
    simpa only [d144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13909 (p : Pattern) (guard : d145 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 157 with
  | false =>
    have hg : d144 p = 1 := by simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13908 p hg
    simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d30 p = 1 := by simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13736 p hg
    simpa only [d145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13910 (p : Pattern) (guard : d146 p = 1) : d48346 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d146, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13730 p hg
    simpa only [d146, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d145 p = 1 := by simpa only [d146, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13909 p hg
    simpa only [d146, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13911 (p : Pattern) (guard : d147 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d147, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13729 p hg
    simpa only [d147, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d146 p = 1 := by simpa only [d147, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13910 p hg
    simpa only [d147, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13912 (p : Pattern) (guard : d148 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 136 with
  | false =>
    have hg : d147 p = 1 := by simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13911 p hg
    simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d33 p = 1 := by simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13739 p hg
    simpa only [d148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13913 (p : Pattern) (guard : d149 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 135 with
  | false =>
    have hg : d148 p = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13912 p hg
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34 p = 1 := by simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13741 p hg
    simpa only [d149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13914 (p : Pattern) (guard : d150 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 119 with
  | false =>
    have hg : d149 p = 1 := by simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13913 p hg
    simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13740 p hg
    simpa only [d150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13915 (p : Pattern) (guard : d151 p = 1) : d48356 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 116 with
  | false =>
    have hg : d150 p = 1 := by simpa only [d151, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13914 p hg
    simpa only [d151, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d151, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13744 p hg
    simpa only [d151, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13916 (p : Pattern) (guard : d152 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d152, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13728 p hg
    simpa only [d152, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d151 p = 1 := by simpa only [d152, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13915 p hg
    simpa only [d152, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13917 (p : Pattern) (guard : d153 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 113 with
  | false =>
    have hg : d152 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13916 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13746 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13918 (p : Pattern) (guard : d154 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 96 with
  | false =>
    have hg : d153 p = 1 := by simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13917 p hg
    simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13919 (p : Pattern) (guard : d155 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 95 with
  | false =>
    have hg : d154 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13918 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13920 (p : Pattern) (guard : d203 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 93 with
  | false =>
    have hg : d155 p = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13919 p hg
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13921 (p : Pattern) (guard : d204 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 91 with
  | false =>
    have hg : d203 p = 1 := by simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13920 p hg
    simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d49 p = 1 := by simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13750 p hg
    simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13922 (p : Pattern) (guard : d4340 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 90 with
  | false =>
    have hg : d204 p = 1 := by simpa only [d4340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13921 p hg
    simpa only [d4340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d4340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13923 (p : Pattern) (guard : d4341 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 89 with
  | false =>
    have hg : d4340 p = 1 := by simpa only [d4341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13922 p hg
    simpa only [d4341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51 p = 1 := by simpa only [d4341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13752 p hg
    simpa only [d4341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13924 (p : Pattern) (guard : d4342 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d4342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4341 p = 1 := by simpa only [d4342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13923 p hg
    simpa only [d4342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13925 (p : Pattern) (guard : d4343 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d4343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4342 p = 1 := by simpa only [d4343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13924 p hg
    simpa only [d4343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13926 (p : Pattern) (guard : d4349 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4349, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d4349, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4343 p = 1 := by simpa only [d4349, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13925 p hg
    simpa only [d4349, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13927 (p : Pattern) (guard : d4350 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13726 p hg
    simpa only [d4350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4349 p = 1 := by simpa only [d4350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13926 p hg
    simpa only [d4350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13928 (p : Pattern) (guard : d4351 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 69 with
  | false =>
    have hg : d4350 p = 1 := by simpa only [d4351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13927 p hg
    simpa only [d4351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13726 p hg
    simpa only [d4351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13929 (p : Pattern) (guard : d4352 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 51 with
  | false =>
    have hg : d4351 p = 1 := by simpa only [d4352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13928 p hg
    simpa only [d4352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13726 p hg
    simpa only [d4352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13930 (p : Pattern) (guard : d4353 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  cases selected : p 50 with
  | false =>
    have hg : d4352 p = 1 := by simpa only [d4353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13929 p hg
    simpa only [d4353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13726 p hg
    simpa only [d4353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13931 (p : Pattern) (guard : d51651 p = 1) : d48359 p ≤ (1 : Int) + d171289 p := by
  cases selected : p 49 with
  | false =>
    have hg : d51650 p = 1 := by simpa only [d51651, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13904 p hg
    simpa only [d51651, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4353 p = 1 := by simpa only [d51651, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13930 p hg
    simpa only [d51651, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13932 (p : Pattern) (guard : d228 p = 1) : d47799 p ≤ (1 : Int) + d47799 p := by
  omega
theorem compare13933 (p : Pattern) (guard : d229 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d228 p = 1 := by simpa only [d229, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13932 p hg
    simpa only [d229, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d229, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13767 p hg
    simpa only [d229, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13934 (p : Pattern) (guard : d230 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d229 p = 1 := by simpa only [d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13933 p hg
    simpa only [d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d69 p = 1 := by simpa only [d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13768 p hg
    simpa only [d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13935 (p : Pattern) (guard : d231 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d230 p = 1 := by simpa only [d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13934 p hg
    simpa only [d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d70 p = 1 := by simpa only [d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13770 p hg
    simpa only [d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13936 (p : Pattern) (guard : d232 p = 1) : d48361 p ≤ (1 : Int) + d48203 p := by
  cases selected : p 157 with
  | false =>
    have hg : d231 p = 1 := by simpa only [d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13935 p hg
    simpa only [d232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d71 p = 1 := by simpa only [d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13771 p hg
    simpa only [d232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13937 (p : Pattern) (guard : d233 p = 1) : d48362 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d233, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13765 p hg
    simpa only [d233, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d232 p = 1 := by simpa only [d233, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13936 p hg
    simpa only [d233, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13938 (p : Pattern) (guard : d234 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d234, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13764 p hg
    simpa only [d234, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d233 p = 1 := by simpa only [d234, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13937 p hg
    simpa only [d234, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13939 (p : Pattern) (guard : d235 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 136 with
  | false =>
    have hg : d234 p = 1 := by simpa only [d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13938 p hg
    simpa only [d235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d74 p = 1 := by simpa only [d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13774 p hg
    simpa only [d235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13940 (p : Pattern) (guard : d236 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 135 with
  | false =>
    have hg : d235 p = 1 := by simpa only [d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13939 p hg
    simpa only [d236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d75 p = 1 := by simpa only [d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13776 p hg
    simpa only [d236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13941 (p : Pattern) (guard : d237 p = 1) : d48363 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 119 with
  | false =>
    have hg : d236 p = 1 := by simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13940 p hg
    simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13775 p hg
    simpa only [d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13942 (p : Pattern) (guard : d238 p = 1) : d48365 p ≤ (1 : Int) + d48204 p := by
  cases selected : p 116 with
  | false =>
    have hg : d237 p = 1 := by simpa only [d238, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13941 p hg
    simpa only [d238, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d238, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13779 p hg
    simpa only [d238, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13943 (p : Pattern) (guard : d239 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d239, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d239, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d238 p = 1 := by simpa only [d239, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13942 p hg
    simpa only [d239, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13944 (p : Pattern) (guard : d240 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 113 with
  | false =>
    have hg : d239 p = 1 := by simpa only [d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13943 p hg
    simpa only [d240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d79 p = 1 := by simpa only [d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13781 p hg
    simpa only [d240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13945 (p : Pattern) (guard : d241 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 96 with
  | false =>
    have hg : d240 p = 1 := by simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13944 p hg
    simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13946 (p : Pattern) (guard : d242 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 95 with
  | false =>
    have hg : d241 p = 1 := by simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13945 p hg
    simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13947 (p : Pattern) (guard : d243 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 93 with
  | false =>
    have hg : d242 p = 1 := by simpa only [d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13946 p hg
    simpa only [d243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13948 (p : Pattern) (guard : d244 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 91 with
  | false =>
    have hg : d243 p = 1 := by simpa only [d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13947 p hg
    simpa only [d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d83 p = 1 := by simpa only [d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13785 p hg
    simpa only [d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13949 (p : Pattern) (guard : d4355 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 90 with
  | false =>
    have hg : d244 p = 1 := by simpa only [d4355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13948 p hg
    simpa only [d4355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d4355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13950 (p : Pattern) (guard : d4356 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 89 with
  | false =>
    have hg : d4355 p = 1 := by simpa only [d4356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13949 p hg
    simpa only [d4356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d85 p = 1 := by simpa only [d4356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13787 p hg
    simpa only [d4356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13951 (p : Pattern) (guard : d4357 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d4357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4356 p = 1 := by simpa only [d4357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13950 p hg
    simpa only [d4357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13952 (p : Pattern) (guard : d4358 p = 1) : d48366 p ≤ (1 : Int) + d171290 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13763 p hg
    simpa only [d4358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4357 p = 1 := by simpa only [d4358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13951 p hg
    simpa only [d4358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13953 (p : Pattern) (guard : d4359 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4359, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d4359, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4358 p = 1 := by simpa only [d4359, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13952 p hg
    simpa only [d4359, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13954 (p : Pattern) (guard : d4360 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13762 p hg
    simpa only [d4360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4359 p = 1 := by simpa only [d4360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13953 p hg
    simpa only [d4360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13955 (p : Pattern) (guard : d4361 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 69 with
  | false =>
    have hg : d4360 p = 1 := by simpa only [d4361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13954 p hg
    simpa only [d4361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13762 p hg
    simpa only [d4361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13956 (p : Pattern) (guard : d4362 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 51 with
  | false =>
    have hg : d4361 p = 1 := by simpa only [d4362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13955 p hg
    simpa only [d4362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13762 p hg
    simpa only [d4362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13957 (p : Pattern) (guard : d4363 p = 1) : d48367 p ≤ (1 : Int) + d171291 p := by
  cases selected : p 50 with
  | false =>
    have hg : d4362 p = 1 := by simpa only [d4363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13956 p hg
    simpa only [d4363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13762 p hg
    simpa only [d4363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13958 (p : Pattern) (guard : d4364 p = 1) : d48387 p ≤ (1 : Int) + d171294 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4363 p = 1 := by simpa only [d4364, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13957 p hg
    simpa only [d4364, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4364, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13796 p hg
    simpa only [d4364, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13959 (p : Pattern) (guard : d51652 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 48 with
  | false =>
    have hg : d51651 p = 1 := by simpa only [d51652, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13931 p hg
    simpa only [d51652, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4364 p = 1 := by simpa only [d51652, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13958 p hg
    simpa only [d51652, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13960 (p : Pattern) (guard : d51653 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d51653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d51653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51652 p = 1 := by simpa only [d51653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13959 p hg
    simpa only [d51653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13961 (p : Pattern) (guard : d51654 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d51654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d51654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51653 p = 1 := by simpa only [d51654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13960 p hg
    simpa only [d51654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13962 (p : Pattern) (guard : d51655 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d51655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d51655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51654 p = 1 := by simpa only [d51655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13961 p hg
    simpa only [d51655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13963 (p : Pattern) (guard : d51656 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d51656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13664 p hg
    simpa only [d51656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51655 p = 1 := by simpa only [d51656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13962 p hg
    simpa only [d51656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13964 (p : Pattern) (guard : d51657 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d99 p = 1 := by simpa only [d51657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13802 p hg
    simpa only [d51657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d51656 p = 1 := by simpa only [d51657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13963 p hg
    simpa only [d51657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13965 (p : Pattern) (guard : d280 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d157 p = 1 := by simpa only [d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13850 p hg
    simpa only [d280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13966 (p : Pattern) (guard : d281 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d280 p = 1 := by simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13965 p hg
    simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13967 (p : Pattern) (guard : d282 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d281 p = 1 := by simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13966 p hg
    simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13968 (p : Pattern) (guard : d283 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d282 p = 1 := by simpa only [d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13967 p hg
    simpa only [d283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13969 (p : Pattern) (guard : d284 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d284, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d284, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d283 p = 1 := by simpa only [d284, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13968 p hg
    simpa only [d284, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13970 (p : Pattern) (guard : d285 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13665 p hg
    simpa only [d285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d284 p = 1 := by simpa only [d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13969 p hg
    simpa only [d285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13971 (p : Pattern) (guard : d286 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 69 with
  | false =>
    have hg : d285 p = 1 := by simpa only [d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13970 p hg
    simpa only [d286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13665 p hg
    simpa only [d286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13972 (p : Pattern) (guard : d280 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d157 p = 1 := by simpa only [d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13878 p hg
    simpa only [d280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13973 (p : Pattern) (guard : d281 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d280 p = 1 := by simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13972 p hg
    simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13974 (p : Pattern) (guard : d282 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d281 p = 1 := by simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13973 p hg
    simpa only [d282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13975 (p : Pattern) (guard : d283 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d282 p = 1 := by simpa only [d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13974 p hg
    simpa only [d283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13976 (p : Pattern) (guard : d287 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d204 p = 1 := by simpa only [d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13893 p hg
    simpa only [d287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13977 (p : Pattern) (guard : d288 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d287 p = 1 := by simpa only [d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13976 p hg
    simpa only [d288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13978 (p : Pattern) (guard : d289 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d288 p = 1 := by simpa only [d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13977 p hg
    simpa only [d289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13979 (p : Pattern) (guard : d290 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d289 p = 1 := by simpa only [d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13978 p hg
    simpa only [d290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13980 (p : Pattern) (guard : d291 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d283 p = 1 := by simpa only [d291, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13975 p hg
    simpa only [d291, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d290 p = 1 := by simpa only [d291, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13979 p hg
    simpa only [d291, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13981 (p : Pattern) (guard : d292 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 70 with
  | false =>
    have hg : d284 p = 1 := by simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13969 p hg
    simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d291 p = 1 := by simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13980 p hg
    simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13982 (p : Pattern) (guard : d293 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 69 with
  | false =>
    have hg : d292 p = 1 := by simpa only [d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13981 p hg
    simpa only [d293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13665 p hg
    simpa only [d293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13983 (p : Pattern) (guard : d294 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 51 with
  | false =>
    have hg : d286 p = 1 := by simpa only [d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13971 p hg
    simpa only [d294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d293 p = 1 := by simpa only [d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13982 p hg
    simpa only [d294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13984 (p : Pattern) (guard : d295 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d154 p = 1 := by simpa only [d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13847 p hg
    simpa only [d295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13985 (p : Pattern) (guard : d296 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295 p = 1 := by simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13984 p hg
    simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13986 (p : Pattern) (guard : d297 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d296 p = 1 := by simpa only [d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13985 p hg
    simpa only [d297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d116 p = 1 := by simpa only [d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13823 p hg
    simpa only [d297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13987 (p : Pattern) (guard : d298 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d297 p = 1 := by simpa only [d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13986 p hg
    simpa only [d298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13988 (p : Pattern) (guard : d299 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d298 p = 1 := by simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13987 p hg
    simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13989 (p : Pattern) (guard : d300 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d299 p = 1 := by simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13988 p hg
    simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13990 (p : Pattern) (guard : d301 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d153 p = 1 := by simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13846 p hg
    simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13991 (p : Pattern) (guard : d302 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d301 p = 1 := by simpa only [d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13990 p hg
    simpa only [d302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13992 (p : Pattern) (guard : d303 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d302 p = 1 := by simpa only [d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13991 p hg
    simpa only [d303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13993 (p : Pattern) (guard : d304 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d303 p = 1 := by simpa only [d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13992 p hg
    simpa only [d304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d123 p = 1 := by simpa only [d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13830 p hg
    simpa only [d304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13994 (p : Pattern) (guard : d305 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d304 p = 1 := by simpa only [d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13993 p hg
    simpa only [d305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13995 (p : Pattern) (guard : d306 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d305 p = 1 := by simpa only [d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13994 p hg
    simpa only [d306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13996 (p : Pattern) (guard : d321 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare13997 (p : Pattern) (guard : d322 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d321 p = 1 := by simpa only [d322, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13996 p hg
    simpa only [d322, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d322, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d322, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13998 (p : Pattern) (guard : d323 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d322 p = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13997 p hg
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d142 p = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13835 p hg
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13999 (p : Pattern) (guard : d12493 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
end NetHack.Soko22Hazard87
