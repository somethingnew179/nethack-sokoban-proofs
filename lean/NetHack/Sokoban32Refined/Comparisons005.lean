/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons004
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare700 (p : Pattern) (guard : d1 p = 1) : d10 p ≤ (0 : Int) + d21 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d10, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare699 p hg
    simpa only [d10, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d10, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare677 p hg
    simpa only [d10, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare701 (p : Pattern) (guard : d1 p = 1) : d22 p ≤ (0 : Int) + d23 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d22, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare700 p hg
    simpa only [d22, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d22, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d22, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare702 (p : Pattern) (guard : d0 p = 1) : d23 p ≤ (0 : Int) + d23 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare703 (p : Pattern) (guard : d873 p = 1) : d24 p ≤ (0 : Int) + d23 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d873, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare701 p hg
    simpa only [d873, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d873, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare702 p hg
    simpa only [d873, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare704 (p : Pattern) (guard : d873 p = 1) : d25 p ≤ (0 : Int) + d876 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d25, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare697 p hg
    simpa only [d25, d876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d25, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare703 p hg
    simpa only [d25, d876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare705 (p : Pattern) (guard : d873 p = 1) : d26 p ≤ (0 : Int) + d877 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d26, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare697 p hg
    simpa only [d26, d877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d26, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare704 p hg
    simpa only [d26, d877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare706 (p : Pattern) (guard : d873 p = 1) : d43 p ≤ (0 : Int) + d878 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d43, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare690 p hg
    simpa only [d43, d878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d43, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare705 p hg
    simpa only [d43, d878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare707 (p : Pattern) (guard : d873 p = 1) : d44 p ≤ (0 : Int) + d879 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d44, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare684 p hg
    simpa only [d44, d879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d44, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare706 p hg
    simpa only [d44, d879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare708 (p : Pattern) (guard : d874 p = 1) : d45 p ≤ (0 : Int) + d879 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d874, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare658 p hg
    simpa only [d874, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d874, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare707 p hg
    simpa only [d874, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare709 (p : Pattern) (guard : d0 p = 1) : d47 p ≤ (0 : Int) + d881 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare710 (p : Pattern) (guard : d873 p = 1) : d48 p ≤ (0 : Int) + d653 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare670 p hg
    simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare682 p hg
    simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare711 (p : Pattern) (guard : d873 p = 1) : d49 p ≤ (0 : Int) + d880 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d49, d880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare689 p hg
    simpa only [d49, d880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d49, d880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare704 p hg
    simpa only [d49, d880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare712 (p : Pattern) (guard : d873 p = 1) : d50 p ≤ (0 : Int) + d881 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d50, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare710 p hg
    simpa only [d50, d881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d50, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare711 p hg
    simpa only [d50, d881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare713 (p : Pattern) (guard : d874 p = 1) : d51 p ≤ (0 : Int) + d881 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d874, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare709 p hg
    simpa only [d874, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d874, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare712 p hg
    simpa only [d874, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare714 (p : Pattern) (guard : d0 p = 1) : d57 p ≤ (0 : Int) + d885 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare715 (p : Pattern) (guard : d873 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare716 (p : Pattern) (guard : d873 p = 1) : d52 p ≤ (0 : Int) + d655 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d52, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare664 p hg
    simpa only [d52, d655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d52, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare715 p hg
    simpa only [d52, d655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare717 (p : Pattern) (guard : d873 p = 1) : d53 p ≤ (0 : Int) + d656 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d53, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare670 p hg
    simpa only [d53, d656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d53, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare716 p hg
    simpa only [d53, d656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare718 (p : Pattern) (guard : d873 p = 1) : d58 p ≤ (0 : Int) + d655 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d58, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare676 p hg
    simpa only [d58, d655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d58, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare715 p hg
    simpa only [d58, d655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare719 (p : Pattern) (guard : d873 p = 1) : d59 p ≤ (0 : Int) + d656 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d59, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare682 p hg
    simpa only [d59, d656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d59, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare718 p hg
    simpa only [d59, d656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare720 (p : Pattern) (guard : d873 p = 1) : d60 p ≤ (0 : Int) + d656 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare717 p hg
    simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare719 p hg
    simpa only [d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare721 (p : Pattern) (guard : d873 p = 1) : d61 p ≤ (0 : Int) + d655 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d61, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare686 p hg
    simpa only [d61, d655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d61, d655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare715 p hg
    simpa only [d61, d655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare722 (p : Pattern) (guard : d873 p = 1) : d62 p ≤ (0 : Int) + d656 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d62, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare689 p hg
    simpa only [d62, d656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d62, d656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare721 p hg
    simpa only [d62, d656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare723 (p : Pattern) (guard : d873 p = 1) : d54 p ≤ (0 : Int) + d882 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d54, d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare697 p hg
    simpa only [d54, d882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d54, d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare715 p hg
    simpa only [d54, d882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare724 (p : Pattern) (guard : d873 p = 1) : d55 p ≤ (0 : Int) + d883 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d55, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare704 p hg
    simpa only [d55, d883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d55, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare723 p hg
    simpa only [d55, d883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare725 (p : Pattern) (guard : d873 p = 1) : d63 p ≤ (0 : Int) + d884 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d63, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare722 p hg
    simpa only [d63, d884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d63, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare724 p hg
    simpa only [d63, d884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare726 (p : Pattern) (guard : d873 p = 1) : d64 p ≤ (0 : Int) + d885 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d64, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare720 p hg
    simpa only [d64, d885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d64, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare725 p hg
    simpa only [d64, d885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare727 (p : Pattern) (guard : d874 p = 1) : d65 p ≤ (0 : Int) + d885 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d874, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare714 p hg
    simpa only [d874, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d874, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare726 p hg
    simpa only [d874, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare728 (p : Pattern) (guard : d874 p = 1) : d66 p ≤ (0 : Int) + d886 p := by
  cases selected : p 113 with
  | false =>
    have hg : d874 p = 1 := by simpa only [d66, d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare713 p hg
    simpa only [d66, d886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d874 p = 1 := by simpa only [d66, d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare727 p hg
    simpa only [d66, d886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare729 (p : Pattern) (guard : d874 p = 1) : d67 p ≤ (0 : Int) + d887 p := by
  cases selected : p 112 with
  | false =>
    have hg : d874 p = 1 := by simpa only [d67, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare708 p hg
    simpa only [d67, d887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d874 p = 1 := by simpa only [d67, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare728 p hg
    simpa only [d67, d887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare730 (p : Pattern) (guard : d0 p = 1) : d156 p ≤ (0 : Int) + d887 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare731 (p : Pattern) (guard : d875 p = 1) : d177 p ≤ (0 : Int) + d887 p := by
  cases selected : p 106 with
  | false =>
    have hg : d874 p = 1 := by simpa only [d875, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare729 p hg
    simpa only [d875, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d875, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare730 p hg
    simpa only [d875, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare732 (p : Pattern) (guard : d0 p = 1) : d89 p ≤ (0 : Int) + d890 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare733 (p : Pattern) (guard : d873 p = 1) : d86 p ≤ (0 : Int) + d673 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d86, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare664 p hg
    simpa only [d86, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d86, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare716 p hg
    simpa only [d86, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare734 (p : Pattern) (guard : d873 p = 1) : d90 p ≤ (0 : Int) + d673 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d90, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare676 p hg
    simpa only [d90, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d90, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare718 p hg
    simpa only [d90, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare735 (p : Pattern) (guard : d873 p = 1) : d91 p ≤ (0 : Int) + d673 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare733 p hg
    simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare734 p hg
    simpa only [d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare736 (p : Pattern) (guard : d873 p = 1) : d92 p ≤ (0 : Int) + d673 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d92, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare686 p hg
    simpa only [d92, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d92, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare721 p hg
    simpa only [d92, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare737 (p : Pattern) (guard : d873 p = 1) : d87 p ≤ (0 : Int) + d888 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d87, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare697 p hg
    simpa only [d87, d888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d87, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare723 p hg
    simpa only [d87, d888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare738 (p : Pattern) (guard : d873 p = 1) : d93 p ≤ (0 : Int) + d889 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d93, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare736 p hg
    simpa only [d93, d889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d93, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare737 p hg
    simpa only [d93, d889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare739 (p : Pattern) (guard : d873 p = 1) : d94 p ≤ (0 : Int) + d890 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d94, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare735 p hg
    simpa only [d94, d890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d94, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare738 p hg
    simpa only [d94, d890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare740 (p : Pattern) (guard : d874 p = 1) : d95 p ≤ (0 : Int) + d890 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d874, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare732 p hg
    simpa only [d874, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d874, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare739 p hg
    simpa only [d874, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare741 (p : Pattern) (guard : d874 p = 1) : d96 p ≤ (0 : Int) + d891 p := by
  cases selected : p 113 with
  | false =>
    have hg : d874 p = 1 := by simpa only [d96, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare708 p hg
    simpa only [d96, d891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d874 p = 1 := by simpa only [d96, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare740 p hg
    simpa only [d96, d891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare742 (p : Pattern) (guard : d0 p = 1) : d100 p ≤ (0 : Int) + d895 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare743 (p : Pattern) (guard : d873 p = 1) : d97 p ≤ (0 : Int) + d659 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d97, d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare669 p hg
    simpa only [d97, d659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d97, d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare715 p hg
    simpa only [d97, d659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare744 (p : Pattern) (guard : d873 p = 1) : d98 p ≤ (0 : Int) + d660 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d98, d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare669 p hg
    simpa only [d98, d660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d98, d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare743 p hg
    simpa only [d98, d660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare745 (p : Pattern) (guard : d873 p = 1) : d70 p ≤ (0 : Int) + d659 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d70, d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare681 p hg
    simpa only [d70, d659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d70, d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare715 p hg
    simpa only [d70, d659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare746 (p : Pattern) (guard : d873 p = 1) : d71 p ≤ (0 : Int) + d660 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d71, d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare681 p hg
    simpa only [d71, d660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d71, d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare745 p hg
    simpa only [d71, d660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare747 (p : Pattern) (guard : d873 p = 1) : d99 p ≤ (0 : Int) + d660 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare744 p hg
    simpa only [d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare746 p hg
    simpa only [d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare748 (p : Pattern) (guard : d873 p = 1) : d68 p ≤ (0 : Int) + d659 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d68, d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare688 p hg
    simpa only [d68, d659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d68, d659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare715 p hg
    simpa only [d68, d659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare749 (p : Pattern) (guard : d873 p = 1) : d69 p ≤ (0 : Int) + d660 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d69, d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare688 p hg
    simpa only [d69, d660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d69, d660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare748 p hg
    simpa only [d69, d660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare750 (p : Pattern) (guard : d873 p = 1) : d70 p ≤ (0 : Int) + d892 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d70, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare703 p hg
    simpa only [d70, d892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d70, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare715 p hg
    simpa only [d70, d892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare751 (p : Pattern) (guard : d873 p = 1) : d71 p ≤ (0 : Int) + d893 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d71, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare703 p hg
    simpa only [d71, d893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d71, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare750 p hg
    simpa only [d71, d893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare752 (p : Pattern) (guard : d873 p = 1) : d72 p ≤ (0 : Int) + d894 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d72, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare749 p hg
    simpa only [d72, d894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d72, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare751 p hg
    simpa only [d72, d894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare753 (p : Pattern) (guard : d873 p = 1) : d101 p ≤ (0 : Int) + d895 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d101, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare747 p hg
    simpa only [d101, d895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d101, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare752 p hg
    simpa only [d101, d895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare754 (p : Pattern) (guard : d874 p = 1) : d102 p ≤ (0 : Int) + d895 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d874, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare742 p hg
    simpa only [d874, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d874, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare753 p hg
    simpa only [d874, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare755 (p : Pattern) (guard : d874 p = 1) : d103 p ≤ (0 : Int) + d896 p := by
  cases selected : p 112 with
  | false =>
    have hg : d874 p = 1 := by simpa only [d103, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare741 p hg
    simpa only [d103, d896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d874 p = 1 := by simpa only [d103, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare754 p hg
    simpa only [d103, d896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare756 (p : Pattern) (guard : d0 p = 1) : d165 p ≤ (0 : Int) + d900 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare757 (p : Pattern) (guard : d875 p = 1) : d178 p ≤ (0 : Int) + d901 p := by
  cases selected : p 106 with
  | false =>
    have hg : d874 p = 1 := by simpa only [d875, d178, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare755 p hg
    simpa only [d875, d178, d901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d875, d178, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare756 p hg
    simpa only [d875, d178, d901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare758 (p : Pattern) (guard : d875 p = 1) : d179 p ≤ (0 : Int) + d902 p := by
  cases selected : p 86 with
  | false =>
    have hg : d875 p = 1 := by simpa only [d179, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare731 p hg
    simpa only [d179, d902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d875 p = 1 := by simpa only [d179, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare757 p hg
    simpa only [d179, d902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare759 (p : Pattern) (guard : d0 p = 1) : d165 p ≤ (0 : Int) + d887 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare760 (p : Pattern) (guard : d875 p = 1) : d180 p ≤ (0 : Int) + d887 p := by
  cases selected : p 106 with
  | false =>
    have hg : d874 p = 1 := by simpa only [d875, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare729 p hg
    simpa only [d875, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d875, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare759 p hg
    simpa only [d875, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare761 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (0 : Int) + d7 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d18, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare659 p hg
    simpa only [d18, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d18, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare694 p hg
    simpa only [d18, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare762 (p : Pattern) (guard : d0 p = 1) : d19 p ≤ (0 : Int) + d7 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare763 (p : Pattern) (guard : d873 p = 1) : d20 p ≤ (0 : Int) + d7 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d873, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare761 p hg
    simpa only [d873, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d873, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare762 p hg
    simpa only [d873, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare764 (p : Pattern) (guard : d873 p = 1) : d119 p ≤ (0 : Int) + d7 p := by
  cases selected : p 139 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare676 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare763 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare765 (p : Pattern) (guard : d873 p = 1) : d120 p ≤ (0 : Int) + d673 p := by
  cases selected : p 138 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d120, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare764 p hg
    simpa only [d120, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d120, d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare718 p hg
    simpa only [d120, d673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare766 (p : Pattern) (guard : d873 p = 1) : d121 p ≤ (0 : Int) + d673 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare733 p hg
    simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare765 p hg
    simpa only [d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare767 (p : Pattern) (guard : d873 p = 1) : d122 p ≤ (0 : Int) + d890 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d122, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare766 p hg
    simpa only [d122, d890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d122, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare738 p hg
    simpa only [d122, d890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare768 (p : Pattern) (guard : d874 p = 1) : d123 p ≤ (0 : Int) + d890 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d874, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare732 p hg
    simpa only [d874, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d874, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare767 p hg
    simpa only [d874, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare769 (p : Pattern) (guard : d874 p = 1) : d124 p ≤ (0 : Int) + d891 p := by
  cases selected : p 113 with
  | false =>
    have hg : d874 p = 1 := by simpa only [d124, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare708 p hg
    simpa only [d124, d891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d874 p = 1 := by simpa only [d124, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare768 p hg
    simpa only [d124, d891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare770 (p : Pattern) (guard : d0 p = 1) : d110 p ≤ (0 : Int) + d898 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare771 (p : Pattern) (guard : d873 p = 1) : d109 p ≤ (0 : Int) + d659 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare743 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare745 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare772 (p : Pattern) (guard : d873 p = 1) : d75 p ≤ (0 : Int) + d897 p := by
  cases selected : p 134 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d75, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare748 p hg
    simpa only [d75, d897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d75, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare750 p hg
    simpa only [d75, d897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare773 (p : Pattern) (guard : d873 p = 1) : d125 p ≤ (0 : Int) + d898 p := by
  cases selected : p 133 with
  | false =>
    have hg : d873 p = 1 := by simpa only [d125, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare771 p hg
    simpa only [d125, d898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d125, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare772 p hg
    simpa only [d125, d898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare774 (p : Pattern) (guard : d874 p = 1) : d126 p ≤ (0 : Int) + d898 p := by
  cases selected : p 132 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d874, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare770 p hg
    simpa only [d874, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d873 p = 1 := by simpa only [d874, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare773 p hg
    simpa only [d874, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare775 (p : Pattern) (guard : d874 p = 1) : d127 p ≤ (0 : Int) + d899 p := by
  cases selected : p 113 with
  | false =>
    have hg : d874 p = 1 := by simpa only [d127, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare754 p hg
    simpa only [d127, d899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d874 p = 1 := by simpa only [d127, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare774 p hg
    simpa only [d127, d899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare776 (p : Pattern) (guard : d874 p = 1) : d128 p ≤ (0 : Int) + d900 p := by
  cases selected : p 112 with
  | false =>
    have hg : d874 p = 1 := by simpa only [d128, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare769 p hg
    simpa only [d128, d900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d874 p = 1 := by simpa only [d128, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare775 p hg
    simpa only [d128, d900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare777 (p : Pattern) (guard : d0 p = 1) : d170 p ≤ (0 : Int) + d905 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare778 (p : Pattern) (guard : d875 p = 1) : d181 p ≤ (0 : Int) + d906 p := by
  cases selected : p 106 with
  | false =>
    have hg : d874 p = 1 := by simpa only [d875, d181, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare776 p hg
    simpa only [d875, d181, d906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d875, d181, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare777 p hg
    simpa only [d875, d181, d906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare779 (p : Pattern) (guard : d875 p = 1) : d182 p ≤ (0 : Int) + d907 p := by
  cases selected : p 86 with
  | false =>
    have hg : d875 p = 1 := by simpa only [d182, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare760 p hg
    simpa only [d182, d907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d875 p = 1 := by simpa only [d182, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare778 p hg
    simpa only [d182, d907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare780 (p : Pattern) (guard : d875 p = 1) : d183 p ≤ (0 : Int) + d908 p := by
  cases selected : p 80 with
  | false =>
    have hg : d875 p = 1 := by simpa only [d183, d908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare758 p hg
    simpa only [d183, d908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d875 p = 1 := by simpa only [d183, d908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare779 p hg
    simpa only [d183, d908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare781 (p : Pattern) (guard : d0 p = 1) : d165 p ≤ (0 : Int) + d117 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare782 (p : Pattern) (guard : d829 p = 1) : d180 p ≤ (0 : Int) + d118 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d829, d180, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare284 p hg
    simpa only [d829, d180, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, d180, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare781 p hg
    simpa only [d829, d180, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare783 (p : Pattern) (guard : d0 p = 1) : d170 p ≤ (0 : Int) + d131 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare784 (p : Pattern) (guard : d829 p = 1) : d181 p ≤ (0 : Int) + d132 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d829, d181, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare293 p hg
    simpa only [d829, d181, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, d181, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare783 p hg
    simpa only [d829, d181, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare785 (p : Pattern) (guard : d829 p = 1) : d182 p ≤ (0 : Int) + d133 p := by
  cases selected : p 86 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d182, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare782 p hg
    simpa only [d182, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d182, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare784 p hg
    simpa only [d182, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare786 (p : Pattern) (guard : d829 p = 1) : d183 p ≤ (0 : Int) + d134 p := by
  cases selected : p 80 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d183, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare617 p hg
    simpa only [d183, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d183, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare785 p hg
    simpa only [d183, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare787 (p : Pattern) (guard : d1 p = 1) : d16 p ≤ (0 : Int) + d16 p := by
  omega
theorem compare788 (p : Pattern) (guard : d0 p = 1) : d27 p ≤ (0 : Int) + d140 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare789 (p : Pattern) (guard : d910 p = 1) : d28 p ≤ (0 : Int) + d293 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d910, d28, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare787 p hg
    simpa only [d910, d28, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d910, d28, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare788 p hg
    simpa only [d910, d28, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare790 (p : Pattern) (guard : d0 p = 1) : d44 p ≤ (0 : Int) + d293 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare791 (p : Pattern) (guard : d912 p = 1) : d45 p ≤ (0 : Int) + d293 p := by
  cases selected : p 132 with
  | false =>
    have hg : d910 p = 1 := by simpa only [d912, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare789 p hg
    simpa only [d912, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d912, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare790 p hg
    simpa only [d912, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare792 (p : Pattern) (guard : d0 p = 1) : d46 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare793 (p : Pattern) (guard : d910 p = 1) : d47 p ≤ (0 : Int) + d294 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d910, d47, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare209 p hg
    simpa only [d910, d47, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d910, d47, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare792 p hg
    simpa only [d910, d47, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare794 (p : Pattern) (guard : d0 p = 1) : d50 p ≤ (0 : Int) + d294 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare795 (p : Pattern) (guard : d912 p = 1) : d51 p ≤ (0 : Int) + d294 p := by
  cases selected : p 132 with
  | false =>
    have hg : d910 p = 1 := by simpa only [d912, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare793 p hg
    simpa only [d912, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d912, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare794 p hg
    simpa only [d912, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare796 (p : Pattern) (guard : d1 p = 1) : d53 p ≤ (0 : Int) + d53 p := by
  omega
theorem compare797 (p : Pattern) (guard : d0 p = 1) : d56 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare798 (p : Pattern) (guard : d910 p = 1) : d57 p ≤ (0 : Int) + d295 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d910, d57, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare796 p hg
    simpa only [d910, d57, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d910, d57, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare797 p hg
    simpa only [d910, d57, d295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare799 (p : Pattern) (guard : d0 p = 1) : d64 p ≤ (0 : Int) + d295 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare800 (p : Pattern) (guard : d912 p = 1) : d65 p ≤ (0 : Int) + d295 p := by
  cases selected : p 132 with
  | false =>
    have hg : d910 p = 1 := by simpa only [d912, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare798 p hg
    simpa only [d912, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d912, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare799 p hg
    simpa only [d912, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare801 (p : Pattern) (guard : d912 p = 1) : d66 p ≤ (0 : Int) + d296 p := by
  cases selected : p 113 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d66, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare795 p hg
    simpa only [d66, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d66, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare800 p hg
    simpa only [d66, d296, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare802 (p : Pattern) (guard : d912 p = 1) : d67 p ≤ (0 : Int) + d297 p := by
  cases selected : p 112 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d67, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare791 p hg
    simpa only [d67, d297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d67, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare801 p hg
    simpa only [d67, d297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare803 (p : Pattern) (guard : d0 p = 1) : d156 p ≤ (0 : Int) + d301 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare804 (p : Pattern) (guard : d913 p = 1) : d177 p ≤ (0 : Int) + d302 p := by
  cases selected : p 106 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d913, d177, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare802 p hg
    simpa only [d913, d177, d302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d913, d177, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare803 p hg
    simpa only [d913, d177, d302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare805 (p : Pattern) (guard : d1 p = 1) : d86 p ≤ (0 : Int) + d86 p := by
  omega
theorem compare806 (p : Pattern) (guard : d0 p = 1) : d88 p ≤ (0 : Int) + d140 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare807 (p : Pattern) (guard : d910 p = 1) : d89 p ≤ (0 : Int) + d303 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d910, d89, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare805 p hg
    simpa only [d910, d89, d303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d910, d89, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare806 p hg
    simpa only [d910, d89, d303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare808 (p : Pattern) (guard : d0 p = 1) : d94 p ≤ (0 : Int) + d304 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare809 (p : Pattern) (guard : d912 p = 1) : d95 p ≤ (0 : Int) + d305 p := by
  cases selected : p 132 with
  | false =>
    have hg : d910 p = 1 := by simpa only [d912, d95, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare807 p hg
    simpa only [d912, d95, d305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d912, d95, d305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare808 p hg
    simpa only [d912, d95, d305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare810 (p : Pattern) (guard : d912 p = 1) : d96 p ≤ (0 : Int) + d306 p := by
  cases selected : p 113 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d96, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare791 p hg
    simpa only [d96, d306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d96, d306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare809 p hg
    simpa only [d96, d306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare811 (p : Pattern) (guard : d1 p = 1) : d98 p ≤ (0 : Int) + d98 p := by
  omega
theorem compare812 (p : Pattern) (guard : d0 p = 1) : d99 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare813 (p : Pattern) (guard : d910 p = 1) : d100 p ≤ (0 : Int) + d307 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d910, d100, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare811 p hg
    simpa only [d910, d100, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d910, d100, d307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare812 p hg
    simpa only [d910, d100, d307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare814 (p : Pattern) (guard : d0 p = 1) : d101 p ≤ (0 : Int) + d307 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare815 (p : Pattern) (guard : d912 p = 1) : d102 p ≤ (0 : Int) + d307 p := by
  cases selected : p 132 with
  | false =>
    have hg : d910 p = 1 := by simpa only [d912, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare813 p hg
    simpa only [d912, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d912, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare814 p hg
    simpa only [d912, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare816 (p : Pattern) (guard : d912 p = 1) : d103 p ≤ (0 : Int) + d308 p := by
  cases selected : p 112 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d103, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare810 p hg
    simpa only [d103, d308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d103, d308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare815 p hg
    simpa only [d103, d308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare817 (p : Pattern) (guard : d0 p = 1) : d165 p ≤ (0 : Int) + d314 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare818 (p : Pattern) (guard : d913 p = 1) : d178 p ≤ (0 : Int) + d315 p := by
  cases selected : p 106 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d913, d178, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare816 p hg
    simpa only [d913, d178, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d913, d178, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare817 p hg
    simpa only [d913, d178, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare819 (p : Pattern) (guard : d913 p = 1) : d179 p ≤ (0 : Int) + d316 p := by
  cases selected : p 86 with
  | false =>
    have hg : d913 p = 1 := by simpa only [d179, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare804 p hg
    simpa only [d179, d316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d913 p = 1 := by simpa only [d179, d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare818 p hg
    simpa only [d179, d316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare820 (p : Pattern) (guard : d0 p = 1) : d44 p ≤ (0 : Int) + d298 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare821 (p : Pattern) (guard : d912 p = 1) : d45 p ≤ (0 : Int) + d299 p := by
  cases selected : p 132 with
  | false =>
    have hg : d910 p = 1 := by simpa only [d912, d45, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare789 p hg
    simpa only [d912, d45, d299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d912, d45, d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare820 p hg
    simpa only [d912, d45, d299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare822 (p : Pattern) (guard : d912 p = 1) : d45 p ≤ (0 : Int) + d300 p := by
  cases selected : p 113 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare791 p hg
    simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare821 p hg
    simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare823 (p : Pattern) (guard : d912 p = 1) : d67 p ≤ (0 : Int) + d301 p := by
  cases selected : p 112 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d67, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d67, d301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d67, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare801 p hg
    simpa only [d67, d301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare824 (p : Pattern) (guard : d0 p = 1) : d165 p ≤ (0 : Int) + d320 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare825 (p : Pattern) (guard : d913 p = 1) : d180 p ≤ (0 : Int) + d321 p := by
  cases selected : p 106 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d913, d180, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare823 p hg
    simpa only [d913, d180, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d913, d180, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare824 p hg
    simpa only [d913, d180, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare826 (p : Pattern) (guard : d0 p = 1) : d88 p ≤ (0 : Int) + d148 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare827 (p : Pattern) (guard : d910 p = 1) : d89 p ≤ (0 : Int) + d304 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d910, d89, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare805 p hg
    simpa only [d910, d89, d304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d910, d89, d304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare826 p hg
    simpa only [d910, d89, d304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare828 (p : Pattern) (guard : d0 p = 1) : d122 p ≤ (0 : Int) + d309 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare829 (p : Pattern) (guard : d912 p = 1) : d123 p ≤ (0 : Int) + d310 p := by
  cases selected : p 132 with
  | false =>
    have hg : d910 p = 1 := by simpa only [d912, d123, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare827 p hg
    simpa only [d912, d123, d310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d912, d123, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare828 p hg
    simpa only [d912, d123, d310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare830 (p : Pattern) (guard : d912 p = 1) : d124 p ≤ (0 : Int) + d311 p := by
  cases selected : p 113 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d124, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare821 p hg
    simpa only [d124, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d124, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare829 p hg
    simpa only [d124, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare831 (p : Pattern) (guard : d1 p = 1) : d97 p ≤ (0 : Int) + d97 p := by
  omega
theorem compare832 (p : Pattern) (guard : d0 p = 1) : d109 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare833 (p : Pattern) (guard : d910 p = 1) : d110 p ≤ (0 : Int) + d312 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d910, d110, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare831 p hg
    simpa only [d910, d110, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d910, d110, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare832 p hg
    simpa only [d910, d110, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare834 (p : Pattern) (guard : d0 p = 1) : d125 p ≤ (0 : Int) + d312 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare835 (p : Pattern) (guard : d912 p = 1) : d126 p ≤ (0 : Int) + d312 p := by
  cases selected : p 132 with
  | false =>
    have hg : d910 p = 1 := by simpa only [d912, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare833 p hg
    simpa only [d912, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d912, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare834 p hg
    simpa only [d912, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare836 (p : Pattern) (guard : d912 p = 1) : d127 p ≤ (0 : Int) + d313 p := by
  cases selected : p 113 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d127, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare815 p hg
    simpa only [d127, d313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d127, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare835 p hg
    simpa only [d127, d313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare837 (p : Pattern) (guard : d912 p = 1) : d128 p ≤ (0 : Int) + d314 p := by
  cases selected : p 112 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d128, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare830 p hg
    simpa only [d128, d314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d912 p = 1 := by simpa only [d128, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare836 p hg
    simpa only [d128, d314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare838 (p : Pattern) (guard : d0 p = 1) : d170 p ≤ (0 : Int) + d324 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare839 (p : Pattern) (guard : d913 p = 1) : d181 p ≤ (0 : Int) + d325 p := by
  cases selected : p 106 with
  | false =>
    have hg : d912 p = 1 := by simpa only [d913, d181, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare837 p hg
    simpa only [d913, d181, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d913, d181, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare838 p hg
    simpa only [d913, d181, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
