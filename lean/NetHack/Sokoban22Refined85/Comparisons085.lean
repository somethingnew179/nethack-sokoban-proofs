/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons084
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare11900 (p : Pattern) (guard : d4471 p = 1) : d1527 p ≤ (0 : Int) + d715 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1527, d715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11894 p hg
    simpa only [d1527, d715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1527, d715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11899 p hg
    simpa only [d1527, d715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11901 (p : Pattern) (guard : d4471 p = 1) : d1528 p ≤ (0 : Int) + d716 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1528, d716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11890 p hg
    simpa only [d1528, d716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1528, d716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11900 p hg
    simpa only [d1528, d716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11902 (p : Pattern) (guard : d4206 p = 1) : d1529 p ≤ (0 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11864 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11868 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11903 (p : Pattern) (guard : d4206 p = 1) : d1530 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1530, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11902 p hg
    simpa only [d1530, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1530, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11869 p hg
    simpa only [d1530, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11904 (p : Pattern) (guard : d4206 p = 1) : d1531 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1531, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11903 p hg
    simpa only [d1531, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1531, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11872 p hg
    simpa only [d1531, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11905 (p : Pattern) (guard : d0 p = 1) : d1523 p ≤ (0 : Int) + d405 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11906 (p : Pattern) (guard : d4471 p = 1) : d1532 p ≤ (0 : Int) + d717 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d1532, d717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11904 p hg
    simpa only [d4471, d1532, d717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d1532, d717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11905 p hg
    simpa only [d4471, d1532, d717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11907 (p : Pattern) (guard : d4471 p = 1) : d1533 p ≤ (0 : Int) + d718 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1533, d718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11906 p hg
    simpa only [d1533, d718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1533, d718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11899 p hg
    simpa only [d1533, d718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11908 (p : Pattern) (guard : d4206 p = 1) : d1534 p ≤ (0 : Int) + d89 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1534, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11870 p hg
    simpa only [d1534, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1534, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11884 p hg
    simpa only [d1534, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11909 (p : Pattern) (guard : d4206 p = 1) : d1535 p ≤ (0 : Int) + d90 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1535, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11908 p hg
    simpa only [d1535, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1535, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11885 p hg
    simpa only [d1535, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11910 (p : Pattern) (guard : d4206 p = 1) : d1536 p ≤ (0 : Int) + d91 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1536, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11885 p hg
    simpa only [d1536, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1536, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d1536, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11911 (p : Pattern) (guard : d4206 p = 1) : d1537 p ≤ (0 : Int) + d92 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1537, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11909 p hg
    simpa only [d1537, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1537, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11910 p hg
    simpa only [d1537, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11912 (p : Pattern) (guard : d0 p = 1) : d1538 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11913 (p : Pattern) (guard : d4471 p = 1) : d1539 p ≤ (0 : Int) + d719 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d1539, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11911 p hg
    simpa only [d4471, d1539, d719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d1539, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11912 p hg
    simpa only [d4471, d1539, d719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11914 (p : Pattern) (guard : d4206 p = 1) : d1538 p ≤ (0 : Int) + d93 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1538, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11910 p hg
    simpa only [d1538, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1538, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d1538, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11915 (p : Pattern) (guard : d4471 p = 1) : d1540 p ≤ (0 : Int) + d95 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d1540, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11914 p hg
    simpa only [d4471, d1540, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d1540, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4471, d1540, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11916 (p : Pattern) (guard : d4471 p = 1) : d1541 p ≤ (0 : Int) + d720 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1541, d720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11913 p hg
    simpa only [d1541, d720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1541, d720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11915 p hg
    simpa only [d1541, d720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11917 (p : Pattern) (guard : d4471 p = 1) : d1542 p ≤ (0 : Int) + d721 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1542, d721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11907 p hg
    simpa only [d1542, d721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1542, d721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11916 p hg
    simpa only [d1542, d721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11918 (p : Pattern) (guard : d4471 p = 1) : d1543 p ≤ (0 : Int) + d722 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1543, d722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11901 p hg
    simpa only [d1543, d722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1543, d722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11917 p hg
    simpa only [d1543, d722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11919 (p : Pattern) (guard : d4206 p = 1) : d1544 p ≤ (0 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11861 p hg
    simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11868 p hg
    simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11920 (p : Pattern) (guard : d4206 p = 1) : d1545 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1545, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11919 p hg
    simpa only [d1545, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1545, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11869 p hg
    simpa only [d1545, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11921 (p : Pattern) (guard : d4206 p = 1) : d1546 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1546, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11920 p hg
    simpa only [d1546, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1546, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11872 p hg
    simpa only [d1546, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11922 (p : Pattern) (guard : d0 p = 1) : d1512 p ≤ (0 : Int) + d409 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11923 (p : Pattern) (guard : d4471 p = 1) : d1547 p ≤ (0 : Int) + d723 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d1547, d723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11921 p hg
    simpa only [d4471, d1547, d723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d1547, d723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11922 p hg
    simpa only [d4471, d1547, d723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11924 (p : Pattern) (guard : d0 p = 1) : d1520 p ≤ (0 : Int) + d396 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11925 (p : Pattern) (guard : d4471 p = 1) : d1520 p ≤ (0 : Int) + d724 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11897 p hg
    simpa only [d4471, d724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11924 p hg
    simpa only [d4471, d724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11926 (p : Pattern) (guard : d4471 p = 1) : d1548 p ≤ (0 : Int) + d725 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1548, d725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11923 p hg
    simpa only [d1548, d725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1548, d725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11925 p hg
    simpa only [d1548, d725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11927 (p : Pattern) (guard : d0 p = 1) : d1523 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11928 (p : Pattern) (guard : d4471 p = 1) : d1524 p ≤ (0 : Int) + d726 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d1524, d726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11892 p hg
    simpa only [d4471, d1524, d726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d1524, d726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11927 p hg
    simpa only [d4471, d1524, d726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11929 (p : Pattern) (guard : d4471 p = 1) : d1527 p ≤ (0 : Int) + d727 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1527, d727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11928 p hg
    simpa only [d1527, d727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1527, d727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11899 p hg
    simpa only [d1527, d727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11930 (p : Pattern) (guard : d4471 p = 1) : d1549 p ≤ (0 : Int) + d728 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1549, d728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11926 p hg
    simpa only [d1549, d728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1549, d728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11929 p hg
    simpa only [d1549, d728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11931 (p : Pattern) (guard : d4471 p = 1) : d1550 p ≤ (0 : Int) + d729 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1550, d729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11929 p hg
    simpa only [d1550, d729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1550, d729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5563 p hg
    simpa only [d1550, d729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11932 (p : Pattern) (guard : d4471 p = 1) : d1551 p ≤ (0 : Int) + d730 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1551, d730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11930 p hg
    simpa only [d1551, d730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1551, d730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11931 p hg
    simpa only [d1551, d730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11933 (p : Pattern) (guard : d4471 p = 1) : d1552 p ≤ (0 : Int) + d731 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1552, d731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11918 p hg
    simpa only [d1552, d731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1552, d731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11932 p hg
    simpa only [d1552, d731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11934 (p : Pattern) (guard : d0 p = 1) : d353 p ≤ (0 : Int) + d15 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11935 (p : Pattern) (guard : d4206 p = 1) : d1553 p ≤ (0 : Int) + d16 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d1553, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1207 p hg
    simpa only [d4206, d1553, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d1553, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11934 p hg
    simpa only [d4206, d1553, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11936 (p : Pattern) (guard : d4206 p = 1) : d1554 p ≤ (0 : Int) + d16 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11935 p hg
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11864 p hg
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11937 (p : Pattern) (guard : d4206 p = 1) : d1555 p ≤ (0 : Int) + d22 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1555, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11936 p hg
    simpa only [d1555, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1555, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11869 p hg
    simpa only [d1555, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11938 (p : Pattern) (guard : d4206 p = 1) : d1556 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1556, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11937 p hg
    simpa only [d1556, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1556, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11872 p hg
    simpa only [d1556, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11939 (p : Pattern) (guard : d0 p = 1) : d1512 p ≤ (0 : Int) + d398 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11940 (p : Pattern) (guard : d4471 p = 1) : d1557 p ≤ (0 : Int) + d732 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d1557, d732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11938 p hg
    simpa only [d4471, d1557, d732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d1557, d732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11939 p hg
    simpa only [d4471, d1557, d732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11941 (p : Pattern) (guard : d4206 p = 1) : d1558 p ≤ (0 : Int) + d54 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1558, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11861 p hg
    simpa only [d1558, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1558, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11878 p hg
    simpa only [d1558, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11942 (p : Pattern) (guard : d4206 p = 1) : d1559 p ≤ (0 : Int) + d56 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1559, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11941 p hg
    simpa only [d1559, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1559, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11880 p hg
    simpa only [d1559, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11943 (p : Pattern) (guard : d4206 p = 1) : d1560 p ≤ (0 : Int) + d65 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1560, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11942 p hg
    simpa only [d1560, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1560, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11886 p hg
    simpa only [d1560, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11944 (p : Pattern) (guard : d0 p = 1) : d1520 p ≤ (0 : Int) + d409 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11945 (p : Pattern) (guard : d4471 p = 1) : d1561 p ≤ (0 : Int) + d733 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d1561, d733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11943 p hg
    simpa only [d4471, d1561, d733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d1561, d733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11944 p hg
    simpa only [d4471, d1561, d733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11946 (p : Pattern) (guard : d4471 p = 1) : d1562 p ≤ (0 : Int) + d734 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1562, d734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11940 p hg
    simpa only [d1562, d734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1562, d734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11945 p hg
    simpa only [d1562, d734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11947 (p : Pattern) (guard : d4471 p = 1) : d1563 p ≤ (0 : Int) + d735 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1563, d735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11946 p hg
    simpa only [d1563, d735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1563, d735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11929 p hg
    simpa only [d1563, d735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11948 (p : Pattern) (guard : d4471 p = 1) : d1564 p ≤ (0 : Int) + d736 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1564, d736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11900 p hg
    simpa only [d1564, d736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1564, d736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11916 p hg
    simpa only [d1564, d736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11949 (p : Pattern) (guard : d4471 p = 1) : d1565 p ≤ (0 : Int) + d737 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1565, d737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11947 p hg
    simpa only [d1565, d737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1565, d737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11948 p hg
    simpa only [d1565, d737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11950 (p : Pattern) (guard : d0 p = 1) : d1512 p ≤ (0 : Int) + d405 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11951 (p : Pattern) (guard : d4471 p = 1) : d1566 p ≤ (0 : Int) + d717 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d1566, d717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11904 p hg
    simpa only [d4471, d1566, d717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d1566, d717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11950 p hg
    simpa only [d4471, d1566, d717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11952 (p : Pattern) (guard : d0 p = 1) : d1520 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11953 (p : Pattern) (guard : d4471 p = 1) : d1520 p ≤ (0 : Int) + d714 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11897 p hg
    simpa only [d4471, d714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11952 p hg
    simpa only [d4471, d714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11954 (p : Pattern) (guard : d4471 p = 1) : d1567 p ≤ (0 : Int) + d718 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1567, d718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11951 p hg
    simpa only [d1567, d718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1567, d718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11953 p hg
    simpa only [d1567, d718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11955 (p : Pattern) (guard : d4471 p = 1) : d1568 p ≤ (0 : Int) + d738 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1568, d738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11954 p hg
    simpa only [d1568, d738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1568, d738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11929 p hg
    simpa only [d1568, d738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11956 (p : Pattern) (guard : d4471 p = 1) : d1569 p ≤ (0 : Int) + d739 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1569, d739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11955 p hg
    simpa only [d1569, d739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1569, d739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11931 p hg
    simpa only [d1569, d739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11957 (p : Pattern) (guard : d4471 p = 1) : d1570 p ≤ (0 : Int) + d740 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1570, d740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11949 p hg
    simpa only [d1570, d740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1570, d740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11956 p hg
    simpa only [d1570, d740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11958 (p : Pattern) (guard : d4471 p = 1) : d1571 p ≤ (0 : Int) + d741 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1571, d741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11933 p hg
    simpa only [d1571, d741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1571, d741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11957 p hg
    simpa only [d1571, d741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11959 (p : Pattern) (guard : d0 p = 1) : d353 p ≤ (0 : Int) + d104 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11960 (p : Pattern) (guard : d4206 p = 1) : d1572 p ≤ (0 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d1572, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d4206, d1572, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d1572, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11959 p hg
    simpa only [d4206, d1572, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11961 (p : Pattern) (guard : d0 p = 1) : d343 p ≤ (0 : Int) + d104 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11962 (p : Pattern) (guard : d4206 p = 1) : d1573 p ≤ (0 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d1573, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d4206, d1573, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d1573, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11961 p hg
    simpa only [d4206, d1573, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11963 (p : Pattern) (guard : d4206 p = 1) : d1574 p ≤ (0 : Int) + d105 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11960 p hg
    simpa only [d1574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11962 p hg
    simpa only [d1574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11964 (p : Pattern) (guard : d4206 p = 1) : d124 p ≤ (0 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d124, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d4206, d124, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d124, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3008 p hg
    simpa only [d4206, d124, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11965 (p : Pattern) (guard : d4206 p = 1) : d125 p ≤ (0 : Int) + d109 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d125, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2051 p hg
    simpa only [d4206, d125, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d125, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3011 p hg
    simpa only [d4206, d125, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11966 (p : Pattern) (guard : d4206 p = 1) : d126 p ≤ (0 : Int) + d110 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d126, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11964 p hg
    simpa only [d126, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d126, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11965 p hg
    simpa only [d126, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11967 (p : Pattern) (guard : d4206 p = 1) : d1575 p ≤ (0 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1575, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11963 p hg
    simpa only [d1575, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1575, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11966 p hg
    simpa only [d1575, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11968 (p : Pattern) (guard : d4206 p = 1) : d128 p ≤ (0 : Int) + d112 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d128, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11882 p hg
    simpa only [d128, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d128, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d128, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11969 (p : Pattern) (guard : d4206 p = 1) : d129 p ≤ (0 : Int) + d113 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d129, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11966 p hg
    simpa only [d129, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d129, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11968 p hg
    simpa only [d129, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11970 (p : Pattern) (guard : d4206 p = 1) : d1576 p ≤ (0 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1576, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11967 p hg
    simpa only [d1576, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1576, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11969 p hg
    simpa only [d1576, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11971 (p : Pattern) (guard : d0 p = 1) : d1578 p ≤ (0 : Int) + d398 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11972 (p : Pattern) (guard : d4471 p = 1) : d1579 p ≤ (0 : Int) + d742 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d1579, d742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11970 p hg
    simpa only [d4471, d1579, d742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d1579, d742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11971 p hg
    simpa only [d4471, d1579, d742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11973 (p : Pattern) (guard : d0 p = 1) : d336 p ≤ (0 : Int) + d104 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11974 (p : Pattern) (guard : d4206 p = 1) : d1580 p ≤ (0 : Int) + d105 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d1580, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d4206, d1580, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d1580, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11973 p hg
    simpa only [d4206, d1580, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11975 (p : Pattern) (guard : d4206 p = 1) : d139 p ≤ (0 : Int) + d132 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d139, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d4206, d139, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d139, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3021 p hg
    simpa only [d4206, d139, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11976 (p : Pattern) (guard : d4206 p = 1) : d1581 p ≤ (0 : Int) + d133 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1581, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11974 p hg
    simpa only [d1581, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1581, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11975 p hg
    simpa only [d1581, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11977 (p : Pattern) (guard : d4206 p = 1) : d141 p ≤ (0 : Int) + d134 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d141, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11965 p hg
    simpa only [d141, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d141, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11882 p hg
    simpa only [d141, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11978 (p : Pattern) (guard : d4206 p = 1) : d1582 p ≤ (0 : Int) + d135 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1582, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11976 p hg
    simpa only [d1582, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1582, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11977 p hg
    simpa only [d1582, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11979 (p : Pattern) (guard : d4206 p = 1) : d143 p ≤ (0 : Int) + d136 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d143, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11965 p hg
    simpa only [d143, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d143, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11884 p hg
    simpa only [d143, d136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11980 (p : Pattern) (guard : d4206 p = 1) : d144 p ≤ (0 : Int) + d137 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d144, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11979 p hg
    simpa only [d144, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d144, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d144, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11981 (p : Pattern) (guard : d4206 p = 1) : d1583 p ≤ (0 : Int) + d138 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1583, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11978 p hg
    simpa only [d1583, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1583, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11980 p hg
    simpa only [d1583, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11982 (p : Pattern) (guard : d0 p = 1) : d1586 p ≤ (0 : Int) + d409 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11983 (p : Pattern) (guard : d4471 p = 1) : d1587 p ≤ (0 : Int) + d743 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d1587, d743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11981 p hg
    simpa only [d4471, d1587, d743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d1587, d743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11982 p hg
    simpa only [d4471, d1587, d743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11984 (p : Pattern) (guard : d4471 p = 1) : d1588 p ≤ (0 : Int) + d744 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1588, d744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11972 p hg
    simpa only [d1588, d744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1588, d744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11983 p hg
    simpa only [d1588, d744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11985 (p : Pattern) (guard : d4206 p = 1) : d1577 p ≤ (0 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1577, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11964 p hg
    simpa only [d1577, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1577, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11966 p hg
    simpa only [d1577, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11986 (p : Pattern) (guard : d4206 p = 1) : d1578 p ≤ (0 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1578, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11985 p hg
    simpa only [d1578, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1578, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11969 p hg
    simpa only [d1578, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11987 (p : Pattern) (guard : d0 p = 1) : d1589 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11988 (p : Pattern) (guard : d4471 p = 1) : d1590 p ≤ (0 : Int) + d745 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d1590, d745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11986 p hg
    simpa only [d4471, d1590, d745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d1590, d745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11987 p hg
    simpa only [d4471, d1590, d745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11989 (p : Pattern) (guard : d4206 p = 1) : d1584 p ≤ (0 : Int) + d133 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1584, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11964 p hg
    simpa only [d1584, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1584, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11975 p hg
    simpa only [d1584, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11990 (p : Pattern) (guard : d4206 p = 1) : d1585 p ≤ (0 : Int) + d135 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1585, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11989 p hg
    simpa only [d1585, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1585, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11977 p hg
    simpa only [d1585, d135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11991 (p : Pattern) (guard : d4206 p = 1) : d1586 p ≤ (0 : Int) + d138 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1586, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11990 p hg
    simpa only [d1586, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1586, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11980 p hg
    simpa only [d1586, d138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11992 (p : Pattern) (guard : d0 p = 1) : d1591 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11993 (p : Pattern) (guard : d4471 p = 1) : d1592 p ≤ (0 : Int) + d746 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d1592, d746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11991 p hg
    simpa only [d4471, d1592, d746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d1592, d746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11992 p hg
    simpa only [d4471, d1592, d746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11994 (p : Pattern) (guard : d4471 p = 1) : d1593 p ≤ (0 : Int) + d747 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1593, d747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11988 p hg
    simpa only [d1593, d747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1593, d747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11993 p hg
    simpa only [d1593, d747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11995 (p : Pattern) (guard : d4471 p = 1) : d1594 p ≤ (0 : Int) + d748 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1594, d748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11984 p hg
    simpa only [d1594, d748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1594, d748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11994 p hg
    simpa only [d1594, d748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11996 (p : Pattern) (guard : d0 p = 1) : d1589 p ≤ (0 : Int) + d396 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare11997 (p : Pattern) (guard : d4471 p = 1) : d1590 p ≤ (0 : Int) + d749 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d1590, d749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11986 p hg
    simpa only [d4471, d1590, d749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d1590, d749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11996 p hg
    simpa only [d4471, d1590, d749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11998 (p : Pattern) (guard : d4471 p = 1) : d1593 p ≤ (0 : Int) + d750 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1593, d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11997 p hg
    simpa only [d1593, d750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1593, d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11993 p hg
    simpa only [d1593, d750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11999 (p : Pattern) (guard : d4206 p = 1) : d1595 p ≤ (0 : Int) + d159 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1595, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11968 p hg
    simpa only [d1595, d159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1595, d159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d1595, d159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12000 (p : Pattern) (guard : d4206 p = 1) : d1596 p ≤ (0 : Int) + d160 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1596, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11999 p hg
    simpa only [d1596, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1596, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d1596, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12001 (p : Pattern) (guard : d4471 p = 1) : d1597 p ≤ (0 : Int) + d161 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d1597, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12000 p hg
    simpa only [d4471, d1597, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d1597, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4471, d1597, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12002 (p : Pattern) (guard : d4471 p = 1) : d1598 p ≤ (0 : Int) + d162 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1598, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12001 p hg
    simpa only [d1598, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1598, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5563 p hg
    simpa only [d1598, d162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12003 (p : Pattern) (guard : d4471 p = 1) : d1599 p ≤ (0 : Int) + d751 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1599, d751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11998 p hg
    simpa only [d1599, d751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1599, d751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12002 p hg
    simpa only [d1599, d751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12004 (p : Pattern) (guard : d4471 p = 1) : d1600 p ≤ (0 : Int) + d752 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1600, d752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11995 p hg
    simpa only [d1600, d752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1600, d752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12003 p hg
    simpa only [d1600, d752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12005 (p : Pattern) (guard : d4206 p = 1) : d1601 p ≤ (0 : Int) + d105 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11962 p hg
    simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11964 p hg
    simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12006 (p : Pattern) (guard : d4206 p = 1) : d1602 p ≤ (0 : Int) + d111 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1602, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12005 p hg
    simpa only [d1602, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1602, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11966 p hg
    simpa only [d1602, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12007 (p : Pattern) (guard : d4206 p = 1) : d1603 p ≤ (0 : Int) + d114 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1603, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12006 p hg
    simpa only [d1603, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1603, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11969 p hg
    simpa only [d1603, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12008 (p : Pattern) (guard : d0 p = 1) : d1578 p ≤ (0 : Int) + d405 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12009 (p : Pattern) (guard : d4471 p = 1) : d1604 p ≤ (0 : Int) + d753 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d1604, d753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12007 p hg
    simpa only [d4471, d1604, d753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d1604, d753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12008 p hg
    simpa only [d4471, d1604, d753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12010 (p : Pattern) (guard : d0 p = 1) : d1586 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12011 (p : Pattern) (guard : d4471 p = 1) : d1586 p ≤ (0 : Int) + d746 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11991 p hg
    simpa only [d4471, d746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12010 p hg
    simpa only [d4471, d746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12012 (p : Pattern) (guard : d4471 p = 1) : d1605 p ≤ (0 : Int) + d754 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1605, d754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12009 p hg
    simpa only [d1605, d754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1605, d754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12011 p hg
    simpa only [d1605, d754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12013 (p : Pattern) (guard : d4471 p = 1) : d1606 p ≤ (0 : Int) + d755 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1606, d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12012 p hg
    simpa only [d1606, d755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1606, d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11994 p hg
    simpa only [d1606, d755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12014 (p : Pattern) (guard : d4471 p = 1) : d1607 p ≤ (0 : Int) + d756 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1607, d756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11994 p hg
    simpa only [d1607, d756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1607, d756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5563 p hg
    simpa only [d1607, d756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12015 (p : Pattern) (guard : d4471 p = 1) : d1608 p ≤ (0 : Int) + d757 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1608, d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12013 p hg
    simpa only [d1608, d757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1608, d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12014 p hg
    simpa only [d1608, d757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12016 (p : Pattern) (guard : d4471 p = 1) : d1609 p ≤ (0 : Int) + d758 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1609, d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12004 p hg
    simpa only [d1609, d758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1609, d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12015 p hg
    simpa only [d1609, d758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12017 (p : Pattern) (guard : d4471 p = 1) : d1610 p ≤ (0 : Int) + d759 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1610, d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11933 p hg
    simpa only [d1610, d759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1610, d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12016 p hg
    simpa only [d1610, d759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12018 (p : Pattern) (guard : d4471 p = 1) : d1611 p ≤ (0 : Int) + d760 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1611, d760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11958 p hg
    simpa only [d1611, d760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1611, d760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12017 p hg
    simpa only [d1611, d760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12019 (p : Pattern) (guard : d0 p = 1) : d1613 p ≤ (0 : Int) + d405 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12020 (p : Pattern) (guard : d4471 p = 1) : d1614 p ≤ (0 : Int) + d717 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d1614, d717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11904 p hg
    simpa only [d4471, d1614, d717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d1614, d717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12019 p hg
    simpa only [d4471, d1614, d717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12021 (p : Pattern) (guard : d0 p = 1) : d1617 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12022 (p : Pattern) (guard : d4471 p = 1) : d1618 p ≤ (0 : Int) + d714 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d1618, d714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11897 p hg
    simpa only [d4471, d1618, d714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d1618, d714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12021 p hg
    simpa only [d4471, d1618, d714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12023 (p : Pattern) (guard : d4471 p = 1) : d1619 p ≤ (0 : Int) + d718 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1619, d718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12020 p hg
    simpa only [d1619, d718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1619, d718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12022 p hg
    simpa only [d1619, d718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12024 (p : Pattern) (guard : d4206 p = 1) : d173 p ≤ (0 : Int) + d78 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4206, d173, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3072 p hg
    simpa only [d4206, d173, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4206, d173, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3074 p hg
    simpa only [d4206, d173, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12025 (p : Pattern) (guard : d4206 p = 1) : d176 p ≤ (0 : Int) + d79 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d176, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11878 p hg
    simpa only [d176, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d176, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12024 p hg
    simpa only [d176, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12026 (p : Pattern) (guard : d4206 p = 1) : d1620 p ≤ (0 : Int) + d188 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1620, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11868 p hg
    simpa only [d1620, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1620, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12025 p hg
    simpa only [d1620, d188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12027 (p : Pattern) (guard : d4206 p = 1) : d177 p ≤ (0 : Int) + d80 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d177, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12025 p hg
    simpa only [d177, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d177, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11885 p hg
    simpa only [d177, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12028 (p : Pattern) (guard : d4206 p = 1) : d1621 p ≤ (0 : Int) + d189 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1621, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12026 p hg
    simpa only [d1621, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1621, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12027 p hg
    simpa only [d1621, d189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12029 (p : Pattern) (guard : d0 p = 1) : d1625 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12030 (p : Pattern) (guard : d4471 p = 1) : d1626 p ≤ (0 : Int) + d761 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d1626, d761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12028 p hg
    simpa only [d4471, d1626, d761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d1626, d761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12029 p hg
    simpa only [d4471, d1626, d761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12031 (p : Pattern) (guard : d4206 p = 1) : d1627 p ≤ (0 : Int) + d198 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1627, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11865 p hg
    simpa only [d1627, d198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1627, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11884 p hg
    simpa only [d1627, d198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12032 (p : Pattern) (guard : d4206 p = 1) : d1628 p ≤ (0 : Int) + d199 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1628, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11878 p hg
    simpa only [d1628, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1628, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12031 p hg
    simpa only [d1628, d199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12033 (p : Pattern) (guard : d4206 p = 1) : d183 p ≤ (0 : Int) + d83 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d183, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12024 p hg
    simpa only [d183, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d183, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d183, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12034 (p : Pattern) (guard : d4206 p = 1) : d184 p ≤ (0 : Int) + d84 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d184, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12033 p hg
    simpa only [d184, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d184, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d184, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12035 (p : Pattern) (guard : d4206 p = 1) : d1629 p ≤ (0 : Int) + d200 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d1629, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12032 p hg
    simpa only [d1629, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d1629, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12034 p hg
    simpa only [d1629, d200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12036 (p : Pattern) (guard : d0 p = 1) : d1632 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12037 (p : Pattern) (guard : d4471 p = 1) : d1633 p ≤ (0 : Int) + d762 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d4471, d1633, d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12035 p hg
    simpa only [d4471, d1633, d762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4471, d1633, d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12036 p hg
    simpa only [d4471, d1633, d762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12038 (p : Pattern) (guard : d4471 p = 1) : d1634 p ≤ (0 : Int) + d763 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1634, d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12030 p hg
    simpa only [d1634, d763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1634, d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12037 p hg
    simpa only [d1634, d763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12039 (p : Pattern) (guard : d4471 p = 1) : d1635 p ≤ (0 : Int) + d764 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4471 p = 1 := by simpa only [d1635, d764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12023 p hg
    simpa only [d1635, d764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4471 p = 1 := by simpa only [d1635, d764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12038 p hg
    simpa only [d1635, d764, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
