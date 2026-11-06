/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons006
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare980 (p : Pattern) (guard : d918 p = 1) : d27 p ≤ (0 : Int) + d920 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d918, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare946 p hg
    simpa only [d918, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d918, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare979 p hg
    simpa only [d918, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare981 (p : Pattern) (guard : d918 p = 1) : d28 p ≤ (0 : Int) + d920 p := by
  cases selected : p 133 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare963 p hg
    simpa only [d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare980 p hg
    simpa only [d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare982 (p : Pattern) (guard : d917 p = 1) : d30 p ≤ (0 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare672 p hg
    simpa only [d917, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d917, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare983 (p : Pattern) (guard : d917 p = 1) : d31 p ≤ (0 : Int) + d744 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d31, d744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare948 p hg
    simpa only [d31, d744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d31, d744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare982 p hg
    simpa only [d31, d744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare984 (p : Pattern) (guard : d1 p = 1) : d29 p ≤ (0 : Int) + d3 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d29, d3, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare103 p hg
    simpa only [d29, d3, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d29, d3, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare222 p hg
    simpa only [d29, d3, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare985 (p : Pattern) (guard : d917 p = 1) : d30 p ≤ (0 : Int) + d3 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d917, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare984 p hg
    simpa only [d917, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d917, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare967 p hg
    simpa only [d917, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare986 (p : Pattern) (guard : d917 p = 1) : d32 p ≤ (0 : Int) + d744 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d32, d744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare985 p hg
    simpa only [d32, d744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d32, d744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare952 p hg
    simpa only [d32, d744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare987 (p : Pattern) (guard : d917 p = 1) : d33 p ≤ (0 : Int) + d744 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare983 p hg
    simpa only [d33, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare986 p hg
    simpa only [d33, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare988 (p : Pattern) (guard : d917 p = 1) : d34 p ≤ (0 : Int) + d919 p := by
  cases selected : p 139 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d34, d919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare987 p hg
    simpa only [d34, d919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d34, d919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare977 p hg
    simpa only [d34, d919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare989 (p : Pattern) (guard : d917 p = 1) : d35 p ≤ (0 : Int) + d920 p := by
  cases selected : p 138 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d35, d920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare987 p hg
    simpa only [d35, d920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d35, d920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare988 p hg
    simpa only [d35, d920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare990 (p : Pattern) (guard : d918 p = 1) : d36 p ≤ (0 : Int) + d920 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d918, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare946 p hg
    simpa only [d918, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d918, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare989 p hg
    simpa only [d918, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare991 (p : Pattern) (guard : d0 p = 1) : d42 p ≤ (0 : Int) + d924 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare992 (p : Pattern) (guard : d917 p = 1) : d19 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare964 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare952 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare993 (p : Pattern) (guard : d917 p = 1) : d20 p ≤ (0 : Int) + d921 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d20, d921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare965 p hg
    simpa only [d20, d921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d20, d921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare992 p hg
    simpa only [d20, d921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare994 (p : Pattern) (guard : d917 p = 1) : d23 p ≤ (0 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare971 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare952 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare995 (p : Pattern) (guard : d917 p = 1) : d24 p ≤ (0 : Int) + d922 p := by
  cases selected : p 158 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d24, d922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare972 p hg
    simpa only [d24, d922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d24, d922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare994 p hg
    simpa only [d24, d922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare996 (p : Pattern) (guard : d917 p = 1) : d25 p ≤ (0 : Int) + d923 p := by
  cases selected : p 139 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d25, d923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare993 p hg
    simpa only [d25, d923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d25, d923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare995 p hg
    simpa only [d25, d923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare997 (p : Pattern) (guard : d917 p = 1) : d26 p ≤ (0 : Int) + d924 p := by
  cases selected : p 138 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d26, d924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare993 p hg
    simpa only [d26, d924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d26, d924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare996 p hg
    simpa only [d26, d924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare998 (p : Pattern) (guard : d918 p = 1) : d43 p ≤ (0 : Int) + d924 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d918, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare991 p hg
    simpa only [d918, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d918, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare997 p hg
    simpa only [d918, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare999 (p : Pattern) (guard : d918 p = 1) : d44 p ≤ (0 : Int) + d925 p := by
  cases selected : p 133 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d44, d925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare990 p hg
    simpa only [d44, d925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d44, d925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare998 p hg
    simpa only [d44, d925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1000 (p : Pattern) (guard : d918 p = 1) : d45 p ≤ (0 : Int) + d926 p := by
  cases selected : p 132 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d45, d926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare981 p hg
    simpa only [d45, d926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d45, d926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare999 p hg
    simpa only [d45, d926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1001 (p : Pattern) (guard : d0 p = 1) : d15 p ≤ (0 : Int) + d919 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1002 (p : Pattern) (guard : d918 p = 1) : d15 p ≤ (0 : Int) + d919 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1001 p hg
    simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare961 p hg
    simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1003 (p : Pattern) (guard : d918 p = 1) : d46 p ≤ (0 : Int) + d919 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d918, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1001 p hg
    simpa only [d918, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d918, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare978 p hg
    simpa only [d918, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1004 (p : Pattern) (guard : d918 p = 1) : d47 p ≤ (0 : Int) + d919 p := by
  cases selected : p 133 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1002 p hg
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1003 p hg
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1005 (p : Pattern) (guard : d918 p = 1) : d48 p ≤ (0 : Int) + d919 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d918, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1001 p hg
    simpa only [d918, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d918, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare988 p hg
    simpa only [d918, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1006 (p : Pattern) (guard : d0 p = 1) : d41 p ≤ (0 : Int) + d923 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1007 (p : Pattern) (guard : d918 p = 1) : d49 p ≤ (0 : Int) + d923 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d918, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1006 p hg
    simpa only [d918, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d918, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare996 p hg
    simpa only [d918, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1008 (p : Pattern) (guard : d918 p = 1) : d50 p ≤ (0 : Int) + d927 p := by
  cases selected : p 133 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d50, d927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1005 p hg
    simpa only [d50, d927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d50, d927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1007 p hg
    simpa only [d50, d927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1009 (p : Pattern) (guard : d918 p = 1) : d51 p ≤ (0 : Int) + d928 p := by
  cases selected : p 132 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d51, d928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1004 p hg
    simpa only [d51, d928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d51, d928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1008 p hg
    simpa only [d51, d928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1010 (p : Pattern) (guard : d0 p = 1) : d53 p ≤ (0 : Int) + d930 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1011 (p : Pattern) (guard : d917 p = 1) : d52 p ≤ (0 : Int) + d929 p := by
  cases selected : p 139 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d52, d929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare954 p hg
    simpa only [d52, d929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d52, d929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare952 p hg
    simpa only [d52, d929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1012 (p : Pattern) (guard : d917 p = 1) : d53 p ≤ (0 : Int) + d930 p := by
  cases selected : p 138 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d53, d930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare961 p hg
    simpa only [d53, d930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d53, d930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1011 p hg
    simpa only [d53, d930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1013 (p : Pattern) (guard : d918 p = 1) : d53 p ≤ (0 : Int) + d930 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1010 p hg
    simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1012 p hg
    simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1014 (p : Pattern) (guard : d917 p = 1) : d54 p ≤ (0 : Int) + d929 p := by
  cases selected : p 139 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d54, d929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare970 p hg
    simpa only [d54, d929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d54, d929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare952 p hg
    simpa only [d54, d929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1015 (p : Pattern) (guard : d917 p = 1) : d55 p ≤ (0 : Int) + d930 p := by
  cases selected : p 138 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d55, d930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare978 p hg
    simpa only [d55, d930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d55, d930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1014 p hg
    simpa only [d55, d930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1016 (p : Pattern) (guard : d918 p = 1) : d56 p ≤ (0 : Int) + d930 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d918, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1010 p hg
    simpa only [d918, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d918, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1015 p hg
    simpa only [d918, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1017 (p : Pattern) (guard : d918 p = 1) : d57 p ≤ (0 : Int) + d930 p := by
  cases selected : p 133 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1013 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1016 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1018 (p : Pattern) (guard : d917 p = 1) : d58 p ≤ (0 : Int) + d929 p := by
  cases selected : p 139 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d58, d929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare987 p hg
    simpa only [d58, d929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d58, d929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare952 p hg
    simpa only [d58, d929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1019 (p : Pattern) (guard : d917 p = 1) : d59 p ≤ (0 : Int) + d930 p := by
  cases selected : p 138 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d59, d930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare988 p hg
    simpa only [d59, d930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d59, d930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1018 p hg
    simpa only [d59, d930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1020 (p : Pattern) (guard : d918 p = 1) : d60 p ≤ (0 : Int) + d930 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d918, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1010 p hg
    simpa only [d918, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d918, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1019 p hg
    simpa only [d918, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1021 (p : Pattern) (guard : d0 p = 1) : d62 p ≤ (0 : Int) + d932 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1022 (p : Pattern) (guard : d917 p = 1) : d54 p ≤ (0 : Int) + d931 p := by
  cases selected : p 139 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d54, d931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare993 p hg
    simpa only [d54, d931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d54, d931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare952 p hg
    simpa only [d54, d931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1023 (p : Pattern) (guard : d917 p = 1) : d55 p ≤ (0 : Int) + d932 p := by
  cases selected : p 138 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d55, d932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare996 p hg
    simpa only [d55, d932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d55, d932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1022 p hg
    simpa only [d55, d932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1024 (p : Pattern) (guard : d918 p = 1) : d63 p ≤ (0 : Int) + d932 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d918, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1021 p hg
    simpa only [d918, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d918, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1023 p hg
    simpa only [d918, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1025 (p : Pattern) (guard : d918 p = 1) : d64 p ≤ (0 : Int) + d933 p := by
  cases selected : p 133 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d64, d933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1020 p hg
    simpa only [d64, d933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d64, d933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1024 p hg
    simpa only [d64, d933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1026 (p : Pattern) (guard : d918 p = 1) : d65 p ≤ (0 : Int) + d934 p := by
  cases selected : p 132 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d65, d934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1017 p hg
    simpa only [d65, d934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d65, d934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1025 p hg
    simpa only [d65, d934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1027 (p : Pattern) (guard : d918 p = 1) : d66 p ≤ (0 : Int) + d935 p := by
  cases selected : p 113 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d66, d935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1009 p hg
    simpa only [d66, d935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d66, d935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1026 p hg
    simpa only [d66, d935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1028 (p : Pattern) (guard : d918 p = 1) : d67 p ≤ (0 : Int) + d936 p := by
  cases selected : p 112 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d67, d936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1000 p hg
    simpa only [d67, d936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d67, d936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1027 p hg
    simpa only [d67, d936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1029 (p : Pattern) (guard : d0 p = 1) : d69 p ≤ (0 : Int) + d938 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1030 (p : Pattern) (guard : d917 p = 1) : d70 p ≤ (0 : Int) + d937 p := by
  cases selected : p 139 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d70, d937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare995 p hg
    simpa only [d70, d937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d70, d937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare952 p hg
    simpa only [d70, d937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1031 (p : Pattern) (guard : d917 p = 1) : d71 p ≤ (0 : Int) + d938 p := by
  cases selected : p 138 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d71, d938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare995 p hg
    simpa only [d71, d938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d71, d938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1030 p hg
    simpa only [d71, d938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1032 (p : Pattern) (guard : d918 p = 1) : d72 p ≤ (0 : Int) + d938 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d918, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1029 p hg
    simpa only [d918, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d918, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1031 p hg
    simpa only [d918, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1033 (p : Pattern) (guard : d918 p = 1) : d73 p ≤ (0 : Int) + d939 p := by
  cases selected : p 133 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d73, d939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare980 p hg
    simpa only [d73, d939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d73, d939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1032 p hg
    simpa only [d73, d939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1034 (p : Pattern) (guard : d918 p = 1) : d74 p ≤ (0 : Int) + d940 p := by
  cases selected : p 132 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d74, d940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare981 p hg
    simpa only [d74, d940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d74, d940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1033 p hg
    simpa only [d74, d940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1035 (p : Pattern) (guard : d0 p = 1) : d68 p ≤ (0 : Int) + d937 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1036 (p : Pattern) (guard : d918 p = 1) : d75 p ≤ (0 : Int) + d937 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d918, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1035 p hg
    simpa only [d918, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d918, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1030 p hg
    simpa only [d918, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1037 (p : Pattern) (guard : d918 p = 1) : d76 p ≤ (0 : Int) + d941 p := by
  cases selected : p 133 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d76, d941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare980 p hg
    simpa only [d76, d941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d76, d941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1036 p hg
    simpa only [d76, d941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1038 (p : Pattern) (guard : d918 p = 1) : d77 p ≤ (0 : Int) + d942 p := by
  cases selected : p 132 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d77, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare981 p hg
    simpa only [d77, d942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d77, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1037 p hg
    simpa only [d77, d942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1039 (p : Pattern) (guard : d918 p = 1) : d78 p ≤ (0 : Int) + d943 p := by
  cases selected : p 113 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d78, d943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1034 p hg
    simpa only [d78, d943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d78, d943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1038 p hg
    simpa only [d78, d943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1040 (p : Pattern) (guard : d918 p = 1) : d79 p ≤ (0 : Int) + d944 p := by
  cases selected : p 133 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d79, d944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1003 p hg
    simpa only [d79, d944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d79, d944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1036 p hg
    simpa only [d79, d944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1041 (p : Pattern) (guard : d918 p = 1) : d80 p ≤ (0 : Int) + d945 p := by
  cases selected : p 132 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d80, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1004 p hg
    simpa only [d80, d945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d80, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1040 p hg
    simpa only [d80, d945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1042 (p : Pattern) (guard : d918 p = 1) : d81 p ≤ (0 : Int) + d946 p := by
  cases selected : p 133 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d81, d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1016 p hg
    simpa only [d81, d946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d81, d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1036 p hg
    simpa only [d81, d946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1043 (p : Pattern) (guard : d918 p = 1) : d82 p ≤ (0 : Int) + d947 p := by
  cases selected : p 132 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d82, d947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1017 p hg
    simpa only [d82, d947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d82, d947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1042 p hg
    simpa only [d82, d947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1044 (p : Pattern) (guard : d918 p = 1) : d83 p ≤ (0 : Int) + d948 p := by
  cases selected : p 113 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d83, d948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1041 p hg
    simpa only [d83, d948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d83, d948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1043 p hg
    simpa only [d83, d948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1045 (p : Pattern) (guard : d918 p = 1) : d84 p ≤ (0 : Int) + d949 p := by
  cases selected : p 112 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d84, d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1039 p hg
    simpa only [d84, d949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d84, d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1044 p hg
    simpa only [d84, d949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1046 (p : Pattern) (guard : d918 p = 1) : d85 p ≤ (0 : Int) + d950 p := by
  cases selected : p 106 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d85, d950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1028 p hg
    simpa only [d85, d950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d85, d950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1045 p hg
    simpa only [d85, d950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1047 (p : Pattern) (guard : d0 p = 1) : d86 p ≤ (0 : Int) + d951 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1048 (p : Pattern) (guard : d917 p = 1) : d86 p ≤ (0 : Int) + d951 p := by
  cases selected : p 138 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d86, d951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare954 p hg
    simpa only [d86, d951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d86, d951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1011 p hg
    simpa only [d86, d951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1049 (p : Pattern) (guard : d918 p = 1) : d86 p ≤ (0 : Int) + d951 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1047 p hg
    simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1048 p hg
    simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1050 (p : Pattern) (guard : d917 p = 1) : d87 p ≤ (0 : Int) + d951 p := by
  cases selected : p 138 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d87, d951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare970 p hg
    simpa only [d87, d951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d87, d951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1014 p hg
    simpa only [d87, d951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1051 (p : Pattern) (guard : d918 p = 1) : d88 p ≤ (0 : Int) + d951 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d918, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1047 p hg
    simpa only [d918, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d918, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1050 p hg
    simpa only [d918, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1052 (p : Pattern) (guard : d918 p = 1) : d89 p ≤ (0 : Int) + d951 p := by
  cases selected : p 133 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1049 p hg
    simpa only [d89, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1051 p hg
    simpa only [d89, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1053 (p : Pattern) (guard : d917 p = 1) : d90 p ≤ (0 : Int) + d951 p := by
  cases selected : p 138 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d90, d951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare987 p hg
    simpa only [d90, d951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d90, d951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1018 p hg
    simpa only [d90, d951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1054 (p : Pattern) (guard : d918 p = 1) : d91 p ≤ (0 : Int) + d951 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d918, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1047 p hg
    simpa only [d918, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d918, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1053 p hg
    simpa only [d918, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1055 (p : Pattern) (guard : d0 p = 1) : d92 p ≤ (0 : Int) + d952 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1056 (p : Pattern) (guard : d917 p = 1) : d87 p ≤ (0 : Int) + d952 p := by
  cases selected : p 138 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d87, d952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare993 p hg
    simpa only [d87, d952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d87, d952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1022 p hg
    simpa only [d87, d952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1057 (p : Pattern) (guard : d918 p = 1) : d93 p ≤ (0 : Int) + d952 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d918, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1055 p hg
    simpa only [d918, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d918, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1056 p hg
    simpa only [d918, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1058 (p : Pattern) (guard : d918 p = 1) : d94 p ≤ (0 : Int) + d953 p := by
  cases selected : p 133 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d94, d953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1054 p hg
    simpa only [d94, d953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d94, d953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1057 p hg
    simpa only [d94, d953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1059 (p : Pattern) (guard : d918 p = 1) : d95 p ≤ (0 : Int) + d954 p := by
  cases selected : p 132 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d95, d954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1052 p hg
    simpa only [d95, d954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d95, d954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1058 p hg
    simpa only [d95, d954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1060 (p : Pattern) (guard : d918 p = 1) : d96 p ≤ (0 : Int) + d955 p := by
  cases selected : p 113 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d96, d955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1000 p hg
    simpa only [d96, d955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d96, d955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1059 p hg
    simpa only [d96, d955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1061 (p : Pattern) (guard : d0 p = 1) : d98 p ≤ (0 : Int) + d957 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1062 (p : Pattern) (guard : d917 p = 1) : d97 p ≤ (0 : Int) + d956 p := by
  cases selected : p 139 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d97, d956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare960 p hg
    simpa only [d97, d956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d97, d956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare952 p hg
    simpa only [d97, d956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1063 (p : Pattern) (guard : d917 p = 1) : d98 p ≤ (0 : Int) + d957 p := by
  cases selected : p 138 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d98, d957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare960 p hg
    simpa only [d98, d957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d98, d957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1062 p hg
    simpa only [d98, d957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1064 (p : Pattern) (guard : d918 p = 1) : d98 p ≤ (0 : Int) + d957 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1061 p hg
    simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1063 p hg
    simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1065 (p : Pattern) (guard : d917 p = 1) : d70 p ≤ (0 : Int) + d956 p := by
  cases selected : p 139 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d70, d956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare977 p hg
    simpa only [d70, d956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d70, d956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare952 p hg
    simpa only [d70, d956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1066 (p : Pattern) (guard : d917 p = 1) : d71 p ≤ (0 : Int) + d957 p := by
  cases selected : p 138 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d71, d957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare977 p hg
    simpa only [d71, d957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d71, d957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1065 p hg
    simpa only [d71, d957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1067 (p : Pattern) (guard : d918 p = 1) : d99 p ≤ (0 : Int) + d957 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d918, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1061 p hg
    simpa only [d918, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d918, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1066 p hg
    simpa only [d918, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1068 (p : Pattern) (guard : d918 p = 1) : d100 p ≤ (0 : Int) + d957 p := by
  cases selected : p 133 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1064 p hg
    simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1067 p hg
    simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1069 (p : Pattern) (guard : d918 p = 1) : d101 p ≤ (0 : Int) + d958 p := by
  cases selected : p 133 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d101, d958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1067 p hg
    simpa only [d101, d958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d101, d958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1032 p hg
    simpa only [d101, d958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1070 (p : Pattern) (guard : d918 p = 1) : d102 p ≤ (0 : Int) + d959 p := by
  cases selected : p 132 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d102, d959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1068 p hg
    simpa only [d102, d959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d102, d959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1069 p hg
    simpa only [d102, d959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1071 (p : Pattern) (guard : d918 p = 1) : d103 p ≤ (0 : Int) + d960 p := by
  cases selected : p 112 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d103, d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1060 p hg
    simpa only [d103, d960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d103, d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1070 p hg
    simpa only [d103, d960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1072 (p : Pattern) (guard : d918 p = 1) : d104 p ≤ (0 : Int) + d961 p := by
  cases selected : p 133 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d104, d961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1051 p hg
    simpa only [d104, d961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d104, d961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1036 p hg
    simpa only [d104, d961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1073 (p : Pattern) (guard : d918 p = 1) : d105 p ≤ (0 : Int) + d962 p := by
  cases selected : p 132 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d105, d962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1052 p hg
    simpa only [d105, d962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d105, d962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1072 p hg
    simpa only [d105, d962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1074 (p : Pattern) (guard : d918 p = 1) : d106 p ≤ (0 : Int) + d963 p := by
  cases selected : p 113 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d106, d963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1038 p hg
    simpa only [d106, d963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d106, d963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1073 p hg
    simpa only [d106, d963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1075 (p : Pattern) (guard : d918 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare1076 (p : Pattern) (guard : d918 p = 1) : d107 p ≤ (0 : Int) + d964 p := by
  cases selected : p 133 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d107, d964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1067 p hg
    simpa only [d107, d964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d107, d964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1075 p hg
    simpa only [d107, d964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1077 (p : Pattern) (guard : d918 p = 1) : d108 p ≤ (0 : Int) + d965 p := by
  cases selected : p 132 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d108, d965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1068 p hg
    simpa only [d108, d965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d108, d965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1076 p hg
    simpa only [d108, d965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1078 (p : Pattern) (guard : d0 p = 1) : d97 p ≤ (0 : Int) + d956 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1079 (p : Pattern) (guard : d918 p = 1) : d97 p ≤ (0 : Int) + d956 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1078 p hg
    simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1062 p hg
    simpa only [d918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1080 (p : Pattern) (guard : d918 p = 1) : d109 p ≤ (0 : Int) + d956 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d918, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1078 p hg
    simpa only [d918, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d918, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1065 p hg
    simpa only [d918, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1081 (p : Pattern) (guard : d918 p = 1) : d110 p ≤ (0 : Int) + d956 p := by
  cases selected : p 133 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1079 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1080 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1082 (p : Pattern) (guard : d918 p = 1) : d111 p ≤ (0 : Int) + d966 p := by
  cases selected : p 133 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d111, d966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1080 p hg
    simpa only [d111, d966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d111, d966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1075 p hg
    simpa only [d111, d966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1083 (p : Pattern) (guard : d918 p = 1) : d112 p ≤ (0 : Int) + d967 p := by
  cases selected : p 132 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d112, d967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1081 p hg
    simpa only [d112, d967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d112, d967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1082 p hg
    simpa only [d112, d967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1084 (p : Pattern) (guard : d918 p = 1) : d113 p ≤ (0 : Int) + d968 p := by
  cases selected : p 113 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d113, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1077 p hg
    simpa only [d113, d968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d113, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1083 p hg
    simpa only [d113, d968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1085 (p : Pattern) (guard : d918 p = 1) : d114 p ≤ (0 : Int) + d969 p := by
  cases selected : p 112 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d114, d969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1074 p hg
    simpa only [d114, d969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d114, d969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1084 p hg
    simpa only [d114, d969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1086 (p : Pattern) (guard : d918 p = 1) : d115 p ≤ (0 : Int) + d970 p := by
  cases selected : p 106 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d115, d970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1071 p hg
    simpa only [d115, d970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d115, d970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1085 p hg
    simpa only [d115, d970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1087 (p : Pattern) (guard : d918 p = 1) : d116 p ≤ (0 : Int) + d971 p := by
  cases selected : p 86 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d116, d971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1046 p hg
    simpa only [d116, d971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d116, d971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1086 p hg
    simpa only [d116, d971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1088 (p : Pattern) (guard : d918 p = 1) : d117 p ≤ (0 : Int) + d972 p := by
  cases selected : p 112 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d117, d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1038 p hg
    simpa only [d117, d972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d117, d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1044 p hg
    simpa only [d117, d972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1089 (p : Pattern) (guard : d918 p = 1) : d118 p ≤ (0 : Int) + d973 p := by
  cases selected : p 106 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d118, d973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1028 p hg
    simpa only [d118, d973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d118, d973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1088 p hg
    simpa only [d118, d973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1090 (p : Pattern) (guard : d917 p = 1) : d119 p ≤ (0 : Int) + d744 p := by
  cases selected : p 139 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare987 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare970 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1091 (p : Pattern) (guard : d917 p = 1) : d120 p ≤ (0 : Int) + d951 p := by
  cases selected : p 138 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d120, d951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1090 p hg
    simpa only [d120, d951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d120, d951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1018 p hg
    simpa only [d120, d951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1092 (p : Pattern) (guard : d918 p = 1) : d121 p ≤ (0 : Int) + d951 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d918, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1047 p hg
    simpa only [d918, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d918, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1091 p hg
    simpa only [d918, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1093 (p : Pattern) (guard : d918 p = 1) : d122 p ≤ (0 : Int) + d953 p := by
  cases selected : p 133 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d122, d953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1092 p hg
    simpa only [d122, d953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d122, d953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1057 p hg
    simpa only [d122, d953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1094 (p : Pattern) (guard : d918 p = 1) : d123 p ≤ (0 : Int) + d954 p := by
  cases selected : p 132 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d123, d954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1052 p hg
    simpa only [d123, d954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d123, d954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1093 p hg
    simpa only [d123, d954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1095 (p : Pattern) (guard : d918 p = 1) : d124 p ≤ (0 : Int) + d955 p := by
  cases selected : p 113 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d124, d955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1000 p hg
    simpa only [d124, d955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d124, d955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1094 p hg
    simpa only [d124, d955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1096 (p : Pattern) (guard : d918 p = 1) : d125 p ≤ (0 : Int) + d974 p := by
  cases selected : p 133 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d125, d974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1080 p hg
    simpa only [d125, d974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d125, d974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1036 p hg
    simpa only [d125, d974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1097 (p : Pattern) (guard : d918 p = 1) : d126 p ≤ (0 : Int) + d975 p := by
  cases selected : p 132 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d126, d975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1081 p hg
    simpa only [d126, d975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d126, d975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1096 p hg
    simpa only [d126, d975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1098 (p : Pattern) (guard : d918 p = 1) : d127 p ≤ (0 : Int) + d976 p := by
  cases selected : p 113 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d127, d976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1070 p hg
    simpa only [d127, d976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d127, d976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1097 p hg
    simpa only [d127, d976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1099 (p : Pattern) (guard : d918 p = 1) : d128 p ≤ (0 : Int) + d977 p := by
  cases selected : p 112 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d128, d977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1095 p hg
    simpa only [d128, d977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d128, d977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1098 p hg
    simpa only [d128, d977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1100 (p : Pattern) (guard : d918 p = 1) : d129 p ≤ (0 : Int) + d978 p := by
  cases selected : p 113 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d129, d978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1038 p hg
    simpa only [d129, d978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d129, d978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1043 p hg
    simpa only [d129, d978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1101 (p : Pattern) (guard : d918 p = 1) : d130 p ≤ (0 : Int) + d979 p := by
  cases selected : p 113 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d130, d979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1083 p hg
    simpa only [d130, d979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d130, d979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1075 p hg
    simpa only [d130, d979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1102 (p : Pattern) (guard : d918 p = 1) : d131 p ≤ (0 : Int) + d980 p := by
  cases selected : p 112 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d131, d980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1100 p hg
    simpa only [d131, d980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d131, d980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1101 p hg
    simpa only [d131, d980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1103 (p : Pattern) (guard : d918 p = 1) : d132 p ≤ (0 : Int) + d981 p := by
  cases selected : p 106 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d132, d981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1099 p hg
    simpa only [d132, d981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d132, d981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1102 p hg
    simpa only [d132, d981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1104 (p : Pattern) (guard : d918 p = 1) : d133 p ≤ (0 : Int) + d982 p := by
  cases selected : p 86 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d133, d982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1089 p hg
    simpa only [d133, d982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d133, d982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1103 p hg
    simpa only [d133, d982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1105 (p : Pattern) (guard : d918 p = 1) : d134 p ≤ (0 : Int) + d983 p := by
  cases selected : p 80 with
  | false =>
    have hg : d918 p = 1 := by simpa only [d134, d983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1087 p hg
    simpa only [d134, d983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d918 p = 1 := by simpa only [d134, d983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1104 p hg
    simpa only [d134, d983, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1106 (p : Pattern) (guard : d915 p = 1) : d16 p ≤ (0 : Int) + d16 p := by
  omega
theorem compare1107 (p : Pattern) (guard : d984 p = 1) : d28 p ≤ (0 : Int) + d293 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d28, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1106 p hg
    simpa only [d984, d28, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d28, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare788 p hg
    simpa only [d984, d28, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1108 (p : Pattern) (guard : d0 p = 1) : d35 p ≤ (0 : Int) + d16 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1109 (p : Pattern) (guard : d915 p = 1) : d36 p ≤ (0 : Int) + d16 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare787 p hg
    simpa only [d915, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1108 p hg
    simpa only [d915, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1110 (p : Pattern) (guard : d0 p = 1) : d43 p ≤ (0 : Int) + d140 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1111 (p : Pattern) (guard : d984 p = 1) : d44 p ≤ (0 : Int) + d293 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d44, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1109 p hg
    simpa only [d984, d44, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d44, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1110 p hg
    simpa only [d984, d44, d293, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1112 (p : Pattern) (guard : d984 p = 1) : d45 p ≤ (0 : Int) + d293 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1107 p hg
    simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1111 p hg
    simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1113 (p : Pattern) (guard : d915 p = 1) : d15 p ≤ (0 : Int) + d15 p := by
  omega
theorem compare1114 (p : Pattern) (guard : d984 p = 1) : d47 p ≤ (0 : Int) + d294 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d47, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1113 p hg
    simpa only [d984, d47, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d47, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare792 p hg
    simpa only [d984, d47, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1115 (p : Pattern) (guard : d0 p = 1) : d34 p ≤ (0 : Int) + d15 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1116 (p : Pattern) (guard : d915 p = 1) : d48 p ≤ (0 : Int) + d15 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d915, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare209 p hg
    simpa only [d915, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d915, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1115 p hg
    simpa only [d915, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1117 (p : Pattern) (guard : d0 p = 1) : d49 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1118 (p : Pattern) (guard : d984 p = 1) : d50 p ≤ (0 : Int) + d294 p := by
  cases selected : p 133 with
  | false =>
    have hg : d915 p = 1 := by simpa only [d984, d50, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1116 p hg
    simpa only [d984, d50, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d984, d50, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1117 p hg
    simpa only [d984, d50, d294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1119 (p : Pattern) (guard : d984 p = 1) : d51 p ≤ (0 : Int) + d294 p := by
  cases selected : p 132 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1114 p hg
    simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d984 p = 1 := by simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1118 p hg
    simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
