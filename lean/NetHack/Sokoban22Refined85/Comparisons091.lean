/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons090
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare12740 (p : Pattern) (guard : d4985 p = 1) : d47 p ≤ (0 : Int) + d4998 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d47, d4998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12738 p hg
    simpa only [d47, d4998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d47, d4998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12739 p hg
    simpa only [d47, d4998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12741 (p : Pattern) (guard : d4985 p = 1) : d1511 p ≤ (0 : Int) + d4999 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1511, d4999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12736 p hg
    simpa only [d1511, d4999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1511, d4999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12740 p hg
    simpa only [d1511, d4999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12742 (p : Pattern) (guard : d4985 p = 1) : d50 p ≤ (0 : Int) + d50 p := by
  omega
theorem compare12743 (p : Pattern) (guard : d4985 p = 1) : d1512 p ≤ (0 : Int) + d5000 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1512, d5000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12741 p hg
    simpa only [d1512, d5000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1512, d5000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12742 p hg
    simpa only [d1512, d5000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12744 (p : Pattern) (guard : d4985 p = 1) : d1513 p ≤ (0 : Int) + d5001 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1513, d5001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12731 p hg
    simpa only [d1513, d5001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1513, d5001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12743 p hg
    simpa only [d1513, d5001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12745 (p : Pattern) (guard : d0 p = 1) : d359 p ≤ (0 : Int) + d1686 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12746 (p : Pattern) (guard : d4985 p = 1) : d1514 p ≤ (0 : Int) + d4986 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d1514, d4986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12709 p hg
    simpa only [d4985, d1514, d4986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d1514, d4986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12745 p hg
    simpa only [d4985, d1514, d4986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12747 (p : Pattern) (guard : d4473 p = 1) : d31 p ≤ (0 : Int) + d31 p := by
  omega
theorem compare12748 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1745 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12749 (p : Pattern) (guard : d4985 p = 1) : d66 p ≤ (0 : Int) + d5002 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d66, d5002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12747 p hg
    simpa only [d4985, d66, d5002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d66, d5002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12748 p hg
    simpa only [d4985, d66, d5002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12750 (p : Pattern) (guard : d4985 p = 1) : d1515 p ≤ (0 : Int) + d5003 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1515, d5003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12746 p hg
    simpa only [d1515, d5003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1515, d5003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12749 p hg
    simpa only [d1515, d5003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12751 (p : Pattern) (guard : d4985 p = 1) : d68 p ≤ (0 : Int) + d5004 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d68, d5004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12719 p hg
    simpa only [d68, d5004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d68, d5004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12727 p hg
    simpa only [d68, d5004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12752 (p : Pattern) (guard : d4985 p = 1) : d1516 p ≤ (0 : Int) + d5005 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1516, d5005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12750 p hg
    simpa only [d1516, d5005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1516, d5005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12751 p hg
    simpa only [d1516, d5005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12753 (p : Pattern) (guard : d4473 p = 1) : d58 p ≤ (0 : Int) + d58 p := by
  omega
theorem compare12754 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1752 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12755 (p : Pattern) (guard : d4985 p = 1) : d70 p ≤ (0 : Int) + d5006 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d70, d5006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12753 p hg
    simpa only [d4985, d70, d5006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d70, d5006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12754 p hg
    simpa only [d4985, d70, d5006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12756 (p : Pattern) (guard : d4985 p = 1) : d71 p ≤ (0 : Int) + d5007 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d71, d5007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12719 p hg
    simpa only [d71, d5007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d71, d5007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12755 p hg
    simpa only [d71, d5007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12757 (p : Pattern) (guard : d4473 p = 1) : d40 p ≤ (0 : Int) + d40 p := by
  omega
theorem compare12758 (p : Pattern) (guard : d4985 p = 1) : d72 p ≤ (0 : Int) + d5008 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d72, d5008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12757 p hg
    simpa only [d4985, d72, d5008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d72, d5008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12737 p hg
    simpa only [d4985, d72, d5008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12759 (p : Pattern) (guard : d4985 p = 1) : d73 p ≤ (0 : Int) + d5009 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d73, d5009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12758 p hg
    simpa only [d73, d5009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d73, d5009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12728 p hg
    simpa only [d73, d5009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12760 (p : Pattern) (guard : d4985 p = 1) : d74 p ≤ (0 : Int) + d5010 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d74, d5010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12756 p hg
    simpa only [d74, d5010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d74, d5010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12759 p hg
    simpa only [d74, d5010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12761 (p : Pattern) (guard : d4985 p = 1) : d1517 p ≤ (0 : Int) + d5011 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1517, d5011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12752 p hg
    simpa only [d1517, d5011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1517, d5011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12760 p hg
    simpa only [d1517, d5011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12762 (p : Pattern) (guard : d4985 p = 1) : d66 p ≤ (0 : Int) + d66 p := by
  omega
theorem compare12763 (p : Pattern) (guard : d4985 p = 1) : d1518 p ≤ (0 : Int) + d5012 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1518, d5012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12735 p hg
    simpa only [d1518, d5012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1518, d5012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12762 p hg
    simpa only [d1518, d5012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12764 (p : Pattern) (guard : d4985 p = 1) : d68 p ≤ (0 : Int) + d68 p := by
  omega
theorem compare12765 (p : Pattern) (guard : d4985 p = 1) : d1519 p ≤ (0 : Int) + d5013 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1519, d5013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12763 p hg
    simpa only [d1519, d5013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1519, d5013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12764 p hg
    simpa only [d1519, d5013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12766 (p : Pattern) (guard : d4985 p = 1) : d74 p ≤ (0 : Int) + d74 p := by
  omega
theorem compare12767 (p : Pattern) (guard : d4985 p = 1) : d1520 p ≤ (0 : Int) + d5014 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1520, d5014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12765 p hg
    simpa only [d1520, d5014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1520, d5014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12766 p hg
    simpa only [d1520, d5014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12768 (p : Pattern) (guard : d4985 p = 1) : d1521 p ≤ (0 : Int) + d5015 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1521, d5015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12761 p hg
    simpa only [d1521, d5015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1521, d5015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12767 p hg
    simpa only [d1521, d5015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12769 (p : Pattern) (guard : d4985 p = 1) : d1522 p ≤ (0 : Int) + d5016 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1522, d5016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12744 p hg
    simpa only [d1522, d5016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1522, d5016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12768 p hg
    simpa only [d1522, d5016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12770 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1772 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12771 (p : Pattern) (guard : d4985 p = 1) : d46 p ≤ (0 : Int) + d5017 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d46, d5017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12709 p hg
    simpa only [d4985, d46, d5017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d46, d5017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12770 p hg
    simpa only [d4985, d46, d5017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12772 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1781 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12773 (p : Pattern) (guard : d4985 p = 1) : d46 p ≤ (0 : Int) + d5018 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d46, d5018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12709 p hg
    simpa only [d4985, d46, d5018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d46, d5018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12772 p hg
    simpa only [d4985, d46, d5018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12774 (p : Pattern) (guard : d4985 p = 1) : d46 p ≤ (0 : Int) + d5019 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d5019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12771 p hg
    simpa only [d5019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d5019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12773 p hg
    simpa only [d5019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12775 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1788 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12776 (p : Pattern) (guard : d4985 p = 1) : d46 p ≤ (0 : Int) + d5020 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d46, d5020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12709 p hg
    simpa only [d4985, d46, d5020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d46, d5020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12775 p hg
    simpa only [d4985, d46, d5020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12777 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1797 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12778 (p : Pattern) (guard : d4985 p = 1) : d43 p ≤ (0 : Int) + d5021 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d43, d5021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12717 p hg
    simpa only [d4985, d43, d5021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d43, d5021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12777 p hg
    simpa only [d4985, d43, d5021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12779 (p : Pattern) (guard : d4985 p = 1) : d47 p ≤ (0 : Int) + d5022 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d47, d5022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12776 p hg
    simpa only [d47, d5022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d47, d5022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12778 p hg
    simpa only [d47, d5022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12780 (p : Pattern) (guard : d4985 p = 1) : d1511 p ≤ (0 : Int) + d5023 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1511, d5023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12774 p hg
    simpa only [d1511, d5023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1511, d5023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12779 p hg
    simpa only [d1511, d5023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12781 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1803 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12782 (p : Pattern) (guard : d4985 p = 1) : d48 p ≤ (0 : Int) + d5024 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d48, d5024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12725 p hg
    simpa only [d4985, d48, d5024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d48, d5024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12781 p hg
    simpa only [d4985, d48, d5024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12783 (p : Pattern) (guard : d4985 p = 1) : d49 p ≤ (0 : Int) + d5025 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d49, d5025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12782 p hg
    simpa only [d49, d5025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d49, d5025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12728 p hg
    simpa only [d49, d5025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12784 (p : Pattern) (guard : d4985 p = 1) : d50 p ≤ (0 : Int) + d5026 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d50, d5026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12779 p hg
    simpa only [d50, d5026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d50, d5026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12783 p hg
    simpa only [d50, d5026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12785 (p : Pattern) (guard : d4985 p = 1) : d1512 p ≤ (0 : Int) + d5027 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1512, d5027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12780 p hg
    simpa only [d1512, d5027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1512, d5027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d1512, d5027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12786 (p : Pattern) (guard : d4985 p = 1) : d66 p ≤ (0 : Int) + d5028 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d66, d5028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12747 p hg
    simpa only [d4985, d66, d5028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d66, d5028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12732 p hg
    simpa only [d4985, d66, d5028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12787 (p : Pattern) (guard : d4473 p = 1) : d35 p ≤ (0 : Int) + d35 p := by
  omega
theorem compare12788 (p : Pattern) (guard : d4985 p = 1) : d173 p ≤ (0 : Int) + d5029 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d173, d5029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12787 p hg
    simpa only [d4985, d173, d5029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d173, d5029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12734 p hg
    simpa only [d4985, d173, d5029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12789 (p : Pattern) (guard : d4985 p = 1) : d176 p ≤ (0 : Int) + d5030 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d176, d5030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12786 p hg
    simpa only [d176, d5030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d176, d5030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12788 p hg
    simpa only [d176, d5030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12790 (p : Pattern) (guard : d4985 p = 1) : d177 p ≤ (0 : Int) + d5031 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d177, d5031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12789 p hg
    simpa only [d177, d5031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d177, d5031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12759 p hg
    simpa only [d177, d5031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12791 (p : Pattern) (guard : d4985 p = 1) : d1523 p ≤ (0 : Int) + d5032 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1523, d5032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12790 p hg
    simpa only [d1523, d5032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1523, d5032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12728 p hg
    simpa only [d1523, d5032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12792 (p : Pattern) (guard : d4985 p = 1) : d1524 p ≤ (0 : Int) + d5033 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1524, d5033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d1524, d5033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1524, d5033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12791 p hg
    simpa only [d1524, d5033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12793 (p : Pattern) (guard : d4985 p = 1) : d1518 p ≤ (0 : Int) + d5034 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1518, d5034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12773 p hg
    simpa only [d1518, d5034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1518, d5034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12786 p hg
    simpa only [d1518, d5034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12794 (p : Pattern) (guard : d4985 p = 1) : d68 p ≤ (0 : Int) + d5035 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d68, d5035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12778 p hg
    simpa only [d68, d5035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d68, d5035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12782 p hg
    simpa only [d68, d5035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12795 (p : Pattern) (guard : d4985 p = 1) : d1519 p ≤ (0 : Int) + d5036 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1519, d5036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12793 p hg
    simpa only [d1519, d5036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1519, d5036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12794 p hg
    simpa only [d1519, d5036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12796 (p : Pattern) (guard : d4985 p = 1) : d71 p ≤ (0 : Int) + d5037 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d71, d5037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12778 p hg
    simpa only [d71, d5037, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d71, d5037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12755 p hg
    simpa only [d71, d5037, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12797 (p : Pattern) (guard : d4985 p = 1) : d74 p ≤ (0 : Int) + d5038 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d74, d5038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12796 p hg
    simpa only [d74, d5038, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d74, d5038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12759 p hg
    simpa only [d74, d5038, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12798 (p : Pattern) (guard : d4985 p = 1) : d1520 p ≤ (0 : Int) + d5039 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1520, d5039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12795 p hg
    simpa only [d1520, d5039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1520, d5039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12797 p hg
    simpa only [d1520, d5039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12799 (p : Pattern) (guard : d4985 p = 1) : d183 p ≤ (0 : Int) + d5040 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d183, d5040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12788 p hg
    simpa only [d183, d5040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d183, d5040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12728 p hg
    simpa only [d183, d5040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12800 (p : Pattern) (guard : d4985 p = 1) : d184 p ≤ (0 : Int) + d5041 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d184, d5041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12799 p hg
    simpa only [d184, d5041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d184, d5041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12728 p hg
    simpa only [d184, d5041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12801 (p : Pattern) (guard : d4985 p = 1) : d1525 p ≤ (0 : Int) + d5042 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1525, d5042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12800 p hg
    simpa only [d1525, d5042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1525, d5042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12728 p hg
    simpa only [d1525, d5042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12802 (p : Pattern) (guard : d4985 p = 1) : d1526 p ≤ (0 : Int) + d5043 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1526, d5043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12798 p hg
    simpa only [d1526, d5043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1526, d5043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12801 p hg
    simpa only [d1526, d5043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12803 (p : Pattern) (guard : d4985 p = 1) : d1527 p ≤ (0 : Int) + d5044 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1527, d5044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12792 p hg
    simpa only [d1527, d5044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1527, d5044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12802 p hg
    simpa only [d1527, d5044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12804 (p : Pattern) (guard : d4985 p = 1) : d1528 p ≤ (0 : Int) + d5045 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1528, d5045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12769 p hg
    simpa only [d1528, d5045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1528, d5045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12803 p hg
    simpa only [d1528, d5045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12805 (p : Pattern) (guard : d0 p = 1) : d343 p ≤ (0 : Int) + d1772 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12806 (p : Pattern) (guard : d4985 p = 1) : d1507 p ≤ (0 : Int) + d5017 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d1507, d5017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12709 p hg
    simpa only [d4985, d1507, d5017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d1507, d5017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12805 p hg
    simpa only [d4985, d1507, d5017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12807 (p : Pattern) (guard : d4985 p = 1) : d1529 p ≤ (0 : Int) + d5019 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1529, d5019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12806 p hg
    simpa only [d1529, d5019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1529, d5019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12773 p hg
    simpa only [d1529, d5019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12808 (p : Pattern) (guard : d4985 p = 1) : d1530 p ≤ (0 : Int) + d5023 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1530, d5023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12807 p hg
    simpa only [d1530, d5023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1530, d5023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12779 p hg
    simpa only [d1530, d5023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12809 (p : Pattern) (guard : d4985 p = 1) : d1531 p ≤ (0 : Int) + d5027 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1531, d5027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12808 p hg
    simpa only [d1531, d5027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1531, d5027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d1531, d5027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12810 (p : Pattern) (guard : d4985 p = 1) : d1532 p ≤ (0 : Int) + d5033 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1532, d5033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12809 p hg
    simpa only [d1532, d5033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1532, d5033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12791 p hg
    simpa only [d1532, d5033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12811 (p : Pattern) (guard : d4985 p = 1) : d1533 p ≤ (0 : Int) + d5044 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1533, d5044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12810 p hg
    simpa only [d1533, d5044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1533, d5044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12802 p hg
    simpa only [d1533, d5044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12812 (p : Pattern) (guard : d4985 p = 1) : d1534 p ≤ (0 : Int) + d5046 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1534, d5046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12782 p hg
    simpa only [d1534, d5046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1534, d5046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12758 p hg
    simpa only [d1534, d5046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12813 (p : Pattern) (guard : d4985 p = 1) : d1535 p ≤ (0 : Int) + d5047 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1535, d5047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12812 p hg
    simpa only [d1535, d5047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1535, d5047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12759 p hg
    simpa only [d1535, d5047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12814 (p : Pattern) (guard : d4985 p = 1) : d1536 p ≤ (0 : Int) + d5048 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1536, d5048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12759 p hg
    simpa only [d1536, d5048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1536, d5048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12728 p hg
    simpa only [d1536, d5048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12815 (p : Pattern) (guard : d4985 p = 1) : d1537 p ≤ (0 : Int) + d5049 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1537, d5049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12813 p hg
    simpa only [d1537, d5049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1537, d5049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12814 p hg
    simpa only [d1537, d5049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12816 (p : Pattern) (guard : d4985 p = 1) : d1538 p ≤ (0 : Int) + d5050 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1538, d5050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12814 p hg
    simpa only [d1538, d5050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1538, d5050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12728 p hg
    simpa only [d1538, d5050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12817 (p : Pattern) (guard : d4985 p = 1) : d1539 p ≤ (0 : Int) + d5051 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1539, d5051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12815 p hg
    simpa only [d1539, d5051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1539, d5051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12816 p hg
    simpa only [d1539, d5051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12818 (p : Pattern) (guard : d4985 p = 1) : d1540 p ≤ (0 : Int) + d5052 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1540, d5052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12816 p hg
    simpa only [d1540, d5052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1540, d5052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12728 p hg
    simpa only [d1540, d5052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12819 (p : Pattern) (guard : d4985 p = 1) : d1541 p ≤ (0 : Int) + d5053 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1541, d5053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12817 p hg
    simpa only [d1541, d5053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1541, d5053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12818 p hg
    simpa only [d1541, d5053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12820 (p : Pattern) (guard : d4985 p = 1) : d1542 p ≤ (0 : Int) + d5054 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1542, d5054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12811 p hg
    simpa only [d1542, d5054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1542, d5054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12819 p hg
    simpa only [d1542, d5054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12821 (p : Pattern) (guard : d4985 p = 1) : d1543 p ≤ (0 : Int) + d5055 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1543, d5055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12804 p hg
    simpa only [d1543, d5055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1543, d5055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12820 p hg
    simpa only [d1543, d5055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12822 (p : Pattern) (guard : d4985 p = 1) : d1544 p ≤ (0 : Int) + d4986 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12713 p hg
    simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12723 p hg
    simpa only [d1544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12823 (p : Pattern) (guard : d4985 p = 1) : d1545 p ≤ (0 : Int) + d4989 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1545, d4989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12822 p hg
    simpa only [d1545, d4989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1545, d4989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12724 p hg
    simpa only [d1545, d4989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12824 (p : Pattern) (guard : d4985 p = 1) : d1546 p ≤ (0 : Int) + d4993 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1546, d4993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12823 p hg
    simpa only [d1546, d4993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1546, d4993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12730 p hg
    simpa only [d1546, d4993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12825 (p : Pattern) (guard : d4985 p = 1) : d1547 p ≤ (0 : Int) + d5001 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1547, d5001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12824 p hg
    simpa only [d1547, d5001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1547, d5001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12743 p hg
    simpa only [d1547, d5001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12826 (p : Pattern) (guard : d4985 p = 1) : d1518 p ≤ (0 : Int) + d5003 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1518, d5003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12723 p hg
    simpa only [d1518, d5003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1518, d5003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12749 p hg
    simpa only [d1518, d5003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12827 (p : Pattern) (guard : d4985 p = 1) : d1519 p ≤ (0 : Int) + d5005 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1519, d5005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12826 p hg
    simpa only [d1519, d5005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1519, d5005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12751 p hg
    simpa only [d1519, d5005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12828 (p : Pattern) (guard : d4985 p = 1) : d1520 p ≤ (0 : Int) + d5011 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1520, d5011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12827 p hg
    simpa only [d1520, d5011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1520, d5011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12760 p hg
    simpa only [d1520, d5011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12829 (p : Pattern) (guard : d4985 p = 1) : d1520 p ≤ (0 : Int) + d5015 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d5015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d5015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d5015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12767 p hg
    simpa only [d5015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12830 (p : Pattern) (guard : d4985 p = 1) : d1548 p ≤ (0 : Int) + d5016 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1548, d5016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12825 p hg
    simpa only [d1548, d5016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1548, d5016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12829 p hg
    simpa only [d1548, d5016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12831 (p : Pattern) (guard : d4985 p = 1) : d1549 p ≤ (0 : Int) + d5045 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1549, d5045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12830 p hg
    simpa only [d1549, d5045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1549, d5045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12803 p hg
    simpa only [d1549, d5045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12832 (p : Pattern) (guard : d4985 p = 1) : d1550 p ≤ (0 : Int) + d5056 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1550, d5056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12803 p hg
    simpa only [d1550, d5056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1550, d5056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12728 p hg
    simpa only [d1550, d5056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12833 (p : Pattern) (guard : d4985 p = 1) : d1551 p ≤ (0 : Int) + d5057 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1551, d5057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12831 p hg
    simpa only [d1551, d5057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1551, d5057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12832 p hg
    simpa only [d1551, d5057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12834 (p : Pattern) (guard : d4985 p = 1) : d1552 p ≤ (0 : Int) + d5058 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1552, d5058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12821 p hg
    simpa only [d1552, d5058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1552, d5058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12833 p hg
    simpa only [d1552, d5058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12835 (p : Pattern) (guard : d0 p = 1) : d353 p ≤ (0 : Int) + d1686 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12836 (p : Pattern) (guard : d4985 p = 1) : d1553 p ≤ (0 : Int) + d4986 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d1553, d4986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12709 p hg
    simpa only [d4985, d1553, d4986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d1553, d4986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12835 p hg
    simpa only [d4985, d1553, d4986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12837 (p : Pattern) (guard : d4985 p = 1) : d1554 p ≤ (0 : Int) + d4986 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12836 p hg
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12716 p hg
    simpa only [d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12838 (p : Pattern) (guard : d4985 p = 1) : d1555 p ≤ (0 : Int) + d4989 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1555, d4989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12837 p hg
    simpa only [d1555, d4989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1555, d4989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12724 p hg
    simpa only [d1555, d4989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12839 (p : Pattern) (guard : d4985 p = 1) : d1556 p ≤ (0 : Int) + d4993 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1556, d4993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12838 p hg
    simpa only [d1556, d4993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1556, d4993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12730 p hg
    simpa only [d1556, d4993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12840 (p : Pattern) (guard : d4985 p = 1) : d1557 p ≤ (0 : Int) + d5001 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1557, d5001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12839 p hg
    simpa only [d1557, d5001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1557, d5001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12743 p hg
    simpa only [d1557, d5001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12841 (p : Pattern) (guard : d4985 p = 1) : d1558 p ≤ (0 : Int) + d5003 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1558, d5003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12713 p hg
    simpa only [d1558, d5003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1558, d5003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12749 p hg
    simpa only [d1558, d5003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12842 (p : Pattern) (guard : d4985 p = 1) : d1559 p ≤ (0 : Int) + d5005 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1559, d5005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12841 p hg
    simpa only [d1559, d5005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1559, d5005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12751 p hg
    simpa only [d1559, d5005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12843 (p : Pattern) (guard : d4985 p = 1) : d1560 p ≤ (0 : Int) + d5011 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1560, d5011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12842 p hg
    simpa only [d1560, d5011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1560, d5011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12760 p hg
    simpa only [d1560, d5011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12844 (p : Pattern) (guard : d4985 p = 1) : d1561 p ≤ (0 : Int) + d5015 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1561, d5015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12843 p hg
    simpa only [d1561, d5015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1561, d5015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12767 p hg
    simpa only [d1561, d5015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12845 (p : Pattern) (guard : d4985 p = 1) : d1562 p ≤ (0 : Int) + d5016 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1562, d5016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12840 p hg
    simpa only [d1562, d5016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1562, d5016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12844 p hg
    simpa only [d1562, d5016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12846 (p : Pattern) (guard : d4985 p = 1) : d1563 p ≤ (0 : Int) + d5045 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1563, d5045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12845 p hg
    simpa only [d1563, d5045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1563, d5045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12803 p hg
    simpa only [d1563, d5045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12847 (p : Pattern) (guard : d4985 p = 1) : d1564 p ≤ (0 : Int) + d5054 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1564, d5054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12803 p hg
    simpa only [d1564, d5054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1564, d5054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12819 p hg
    simpa only [d1564, d5054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12848 (p : Pattern) (guard : d4985 p = 1) : d1565 p ≤ (0 : Int) + d5055 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1565, d5055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12846 p hg
    simpa only [d1565, d5055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1565, d5055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12847 p hg
    simpa only [d1565, d5055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12849 (p : Pattern) (guard : d4985 p = 1) : d1529 p ≤ (0 : Int) + d4986 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12716 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12723 p hg
    simpa only [d1529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12850 (p : Pattern) (guard : d4985 p = 1) : d1530 p ≤ (0 : Int) + d4989 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1530, d4989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12849 p hg
    simpa only [d1530, d4989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1530, d4989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12724 p hg
    simpa only [d1530, d4989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12851 (p : Pattern) (guard : d4985 p = 1) : d1531 p ≤ (0 : Int) + d4993 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1531, d4993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12850 p hg
    simpa only [d1531, d4993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1531, d4993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12730 p hg
    simpa only [d1531, d4993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12852 (p : Pattern) (guard : d4985 p = 1) : d1566 p ≤ (0 : Int) + d5001 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1566, d5001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12851 p hg
    simpa only [d1566, d5001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1566, d5001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12743 p hg
    simpa only [d1566, d5001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12853 (p : Pattern) (guard : d4985 p = 1) : d1567 p ≤ (0 : Int) + d5016 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1567, d5016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12852 p hg
    simpa only [d1567, d5016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1567, d5016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12829 p hg
    simpa only [d1567, d5016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12854 (p : Pattern) (guard : d4985 p = 1) : d1568 p ≤ (0 : Int) + d5045 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1568, d5045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12853 p hg
    simpa only [d1568, d5045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1568, d5045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12803 p hg
    simpa only [d1568, d5045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12855 (p : Pattern) (guard : d4985 p = 1) : d1569 p ≤ (0 : Int) + d5057 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1569, d5057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12854 p hg
    simpa only [d1569, d5057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1569, d5057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12832 p hg
    simpa only [d1569, d5057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12856 (p : Pattern) (guard : d4985 p = 1) : d1570 p ≤ (0 : Int) + d5058 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1570, d5058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12848 p hg
    simpa only [d1570, d5058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1570, d5058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12855 p hg
    simpa only [d1570, d5058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12857 (p : Pattern) (guard : d4985 p = 1) : d1571 p ≤ (0 : Int) + d5058 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12834 p hg
    simpa only [d1571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12856 p hg
    simpa only [d1571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12858 (p : Pattern) (guard : d4473 p = 1) : d103 p ≤ (0 : Int) + d103 p := by
  omega
theorem compare12859 (p : Pattern) (guard : d0 p = 1) : d353 p ≤ (0 : Int) + d1875 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12860 (p : Pattern) (guard : d4985 p = 1) : d1572 p ≤ (0 : Int) + d5059 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d1572, d5059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12858 p hg
    simpa only [d4985, d1572, d5059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d1572, d5059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12859 p hg
    simpa only [d4985, d1572, d5059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12861 (p : Pattern) (guard : d0 p = 1) : d343 p ≤ (0 : Int) + d1875 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12862 (p : Pattern) (guard : d4985 p = 1) : d1573 p ≤ (0 : Int) + d5059 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d1573, d5059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12858 p hg
    simpa only [d4985, d1573, d5059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d1573, d5059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12861 p hg
    simpa only [d4985, d1573, d5059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12863 (p : Pattern) (guard : d4985 p = 1) : d1574 p ≤ (0 : Int) + d5059 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12860 p hg
    simpa only [d1574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12862 p hg
    simpa only [d1574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12864 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1875 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12865 (p : Pattern) (guard : d4985 p = 1) : d124 p ≤ (0 : Int) + d5059 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d124, d5059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12858 p hg
    simpa only [d4985, d124, d5059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d124, d5059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12864 p hg
    simpa only [d4985, d124, d5059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12866 (p : Pattern) (guard : d4473 p = 1) : d107 p ≤ (0 : Int) + d107 p := by
  omega
theorem compare12867 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1883 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12868 (p : Pattern) (guard : d4985 p = 1) : d125 p ≤ (0 : Int) + d5060 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d125, d5060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12866 p hg
    simpa only [d4985, d125, d5060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d125, d5060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12867 p hg
    simpa only [d4985, d125, d5060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12869 (p : Pattern) (guard : d4985 p = 1) : d126 p ≤ (0 : Int) + d5061 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d126, d5061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d126, d5061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d126, d5061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12868 p hg
    simpa only [d126, d5061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12870 (p : Pattern) (guard : d4985 p = 1) : d1575 p ≤ (0 : Int) + d5062 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1575, d5062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12863 p hg
    simpa only [d1575, d5062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1575, d5062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12869 p hg
    simpa only [d1575, d5062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12871 (p : Pattern) (guard : d4985 p = 1) : d128 p ≤ (0 : Int) + d5063 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d128, d5063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12755 p hg
    simpa only [d128, d5063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d128, d5063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12728 p hg
    simpa only [d128, d5063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12872 (p : Pattern) (guard : d4985 p = 1) : d129 p ≤ (0 : Int) + d5064 p := by
  cases selected : p 162 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d129, d5064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12869 p hg
    simpa only [d129, d5064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d129, d5064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12871 p hg
    simpa only [d129, d5064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12873 (p : Pattern) (guard : d4985 p = 1) : d1576 p ≤ (0 : Int) + d5065 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d1576, d5065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12870 p hg
    simpa only [d1576, d5065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d1576, d5065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12872 p hg
    simpa only [d1576, d5065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12874 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1898 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12875 (p : Pattern) (guard : d4985 p = 1) : d124 p ≤ (0 : Int) + d5066 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d124, d5066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12858 p hg
    simpa only [d4985, d124, d5066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d124, d5066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12874 p hg
    simpa only [d4985, d124, d5066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12876 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d1905 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12877 (p : Pattern) (guard : d4985 p = 1) : d124 p ≤ (0 : Int) + d5067 p := by
  cases selected : p 182 with
  | false =>
    have hg : d4473 p = 1 := by simpa only [d4985, d124, d5067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12858 p hg
    simpa only [d4985, d124, d5067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4985, d124, d5067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12876 p hg
    simpa only [d4985, d124, d5067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12878 (p : Pattern) (guard : d4985 p = 1) : d124 p ≤ (0 : Int) + d5068 p := by
  cases selected : p 163 with
  | false =>
    have hg : d4985 p = 1 := by simpa only [d5068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12875 p hg
    simpa only [d5068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4985 p = 1 := by simpa only [d5068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12877 p hg
    simpa only [d5068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12879 (p : Pattern) (guard : d4985 p = 1) : d126 p ≤ (0 : Int) + d126 p := by
  omega
end NetHack.Sokoban22Refined85
