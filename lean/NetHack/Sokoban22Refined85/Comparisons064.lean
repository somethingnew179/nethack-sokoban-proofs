/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons063
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare8960 (p : Pattern) (guard : d4617 p = 1) : d998 p ≤ (0 : Int) + d799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8959 p hg
    simpa only [d4617, d998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8680 p hg
    simpa only [d4617, d998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8961 (p : Pattern) (guard : d4618 p = 1) : d999 p ≤ (0 : Int) + d799 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8960 p hg
    simpa only [d4618, d999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8924 p hg
    simpa only [d4618, d999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8962 (p : Pattern) (guard : d4618 p = 1) : d1000 p ≤ (0 : Int) + d4766 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1000, d4766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8958 p hg
    simpa only [d1000, d4766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1000, d4766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8961 p hg
    simpa only [d1000, d4766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8963 (p : Pattern) (guard : d0 p = 1) : d1001 p ≤ (0 : Int) + d804 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8964 (p : Pattern) (guard : d4617 p = 1) : d1002 p ≤ (0 : Int) + d804 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d1002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8963 p hg
    simpa only [d4617, d1002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d1002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8928 p hg
    simpa only [d4617, d1002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8965 (p : Pattern) (guard : d4618 p = 1) : d1003 p ≤ (0 : Int) + d804 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d1003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8964 p hg
    simpa only [d4618, d1003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d1003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8930 p hg
    simpa only [d4618, d1003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8966 (p : Pattern) (guard : d0 p = 1) : d966 p ≤ (0 : Int) + d810 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8967 (p : Pattern) (guard : d4617 p = 1) : d1004 p ≤ (0 : Int) + d810 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d1004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8966 p hg
    simpa only [d4617, d1004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d1004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8696 p hg
    simpa only [d4617, d1004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8968 (p : Pattern) (guard : d4618 p = 1) : d1005 p ≤ (0 : Int) + d810 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d1005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8967 p hg
    simpa only [d4618, d1005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d1005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8934 p hg
    simpa only [d4618, d1005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8969 (p : Pattern) (guard : d4618 p = 1) : d1006 p ≤ (0 : Int) + d4767 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1006, d4767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8965 p hg
    simpa only [d1006, d4767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1006, d4767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8968 p hg
    simpa only [d1006, d4767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8970 (p : Pattern) (guard : d4618 p = 1) : d1007 p ≤ (0 : Int) + d4768 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1007, d4768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8962 p hg
    simpa only [d1007, d4768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1007, d4768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8969 p hg
    simpa only [d1007, d4768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8971 (p : Pattern) (guard : d0 p = 1) : d1008 p ≤ (0 : Int) + d804 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8972 (p : Pattern) (guard : d4617 p = 1) : d1009 p ≤ (0 : Int) + d804 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d1009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8971 p hg
    simpa only [d4617, d1009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d1009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8928 p hg
    simpa only [d4617, d1009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8973 (p : Pattern) (guard : d4618 p = 1) : d1010 p ≤ (0 : Int) + d804 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d1010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8972 p hg
    simpa only [d4618, d1010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d1010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8930 p hg
    simpa only [d4618, d1010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8974 (p : Pattern) (guard : d4618 p = 1) : d1011 p ≤ (0 : Int) + d4767 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1011, d4767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8973 p hg
    simpa only [d1011, d4767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1011, d4767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8968 p hg
    simpa only [d1011, d4767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8975 (p : Pattern) (guard : d4618 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare8976 (p : Pattern) (guard : d4618 p = 1) : d1012 p ≤ (0 : Int) + d4771 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1012, d4771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8974 p hg
    simpa only [d1012, d4771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1012, d4771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8975 p hg
    simpa only [d1012, d4771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8977 (p : Pattern) (guard : d4618 p = 1) : d1013 p ≤ (0 : Int) + d4772 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1013, d4772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8970 p hg
    simpa only [d1013, d4772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1013, d4772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8976 p hg
    simpa only [d1013, d4772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8978 (p : Pattern) (guard : d4618 p = 1) : d1014 p ≤ (0 : Int) + d4773 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1014, d4773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8953 p hg
    simpa only [d1014, d4773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1014, d4773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8977 p hg
    simpa only [d1014, d4773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8979 (p : Pattern) (guard : d0 p = 1) : d1015 p ≤ (0 : Int) + d791 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8980 (p : Pattern) (guard : d4395 p = 1) : d1016 p ≤ (0 : Int) + d791 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1016, d791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8914 p hg
    simpa only [d4395, d1016, d791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1016, d791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8670 p hg
    simpa only [d4395, d1016, d791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8981 (p : Pattern) (guard : d4617 p = 1) : d1017 p ≤ (0 : Int) + d791 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d1017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8979 p hg
    simpa only [d4617, d1017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d1017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8980 p hg
    simpa only [d4617, d1017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8982 (p : Pattern) (guard : d0 p = 1) : d1019 p ≤ (0 : Int) + d791 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8983 (p : Pattern) (guard : d4618 p = 1) : d1020 p ≤ (0 : Int) + d791 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d1020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8981 p hg
    simpa only [d4618, d1020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d1020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8982 p hg
    simpa only [d4618, d1020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8984 (p : Pattern) (guard : d0 p = 1) : d1021 p ≤ (0 : Int) + d799 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8985 (p : Pattern) (guard : d4617 p = 1) : d1022 p ≤ (0 : Int) + d799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8984 p hg
    simpa only [d4617, d1022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8680 p hg
    simpa only [d4617, d1022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8986 (p : Pattern) (guard : d4618 p = 1) : d1023 p ≤ (0 : Int) + d799 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d1023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8985 p hg
    simpa only [d4618, d1023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d1023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8924 p hg
    simpa only [d4618, d1023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8987 (p : Pattern) (guard : d4618 p = 1) : d1024 p ≤ (0 : Int) + d4766 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1024, d4766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8983 p hg
    simpa only [d1024, d4766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1024, d4766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8986 p hg
    simpa only [d1024, d4766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8988 (p : Pattern) (guard : d0 p = 1) : d1025 p ≤ (0 : Int) + d804 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8989 (p : Pattern) (guard : d4617 p = 1) : d1026 p ≤ (0 : Int) + d804 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d1026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8988 p hg
    simpa only [d4617, d1026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d1026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8928 p hg
    simpa only [d4617, d1026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8990 (p : Pattern) (guard : d4618 p = 1) : d1027 p ≤ (0 : Int) + d804 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8989 p hg
    simpa only [d4618, d1027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8930 p hg
    simpa only [d4618, d1027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8991 (p : Pattern) (guard : d4618 p = 1) : d1028 p ≤ (0 : Int) + d4767 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1028, d4767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8990 p hg
    simpa only [d1028, d4767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1028, d4767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8968 p hg
    simpa only [d1028, d4767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8992 (p : Pattern) (guard : d4618 p = 1) : d1029 p ≤ (0 : Int) + d4768 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1029, d4768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8987 p hg
    simpa only [d1029, d4768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1029, d4768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8991 p hg
    simpa only [d1029, d4768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8993 (p : Pattern) (guard : d4618 p = 1) : d1030 p ≤ (0 : Int) + d4769 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1030, d4769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8936 p hg
    simpa only [d1030, d4769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1030, d4769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8951 p hg
    simpa only [d1030, d4769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8994 (p : Pattern) (guard : d4618 p = 1) : d1031 p ≤ (0 : Int) + d4770 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1031, d4770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8992 p hg
    simpa only [d1031, d4770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1031, d4770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8993 p hg
    simpa only [d1031, d4770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8995 (p : Pattern) (guard : d0 p = 1) : d978 p ≤ (0 : Int) + d791 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8996 (p : Pattern) (guard : d4617 p = 1) : d1032 p ≤ (0 : Int) + d791 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d1032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8995 p hg
    simpa only [d4617, d1032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d1032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8955 p hg
    simpa only [d4617, d1032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8997 (p : Pattern) (guard : d4618 p = 1) : d1033 p ≤ (0 : Int) + d791 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8996 p hg
    simpa only [d4618, d1033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8957 p hg
    simpa only [d4618, d1033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8998 (p : Pattern) (guard : d0 p = 1) : d981 p ≤ (0 : Int) + d799 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8999 (p : Pattern) (guard : d4617 p = 1) : d1034 p ≤ (0 : Int) + d799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d1034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8998 p hg
    simpa only [d4617, d1034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d1034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8680 p hg
    simpa only [d4617, d1034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9000 (p : Pattern) (guard : d4618 p = 1) : d1035 p ≤ (0 : Int) + d799 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d1035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8999 p hg
    simpa only [d4618, d1035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d1035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8924 p hg
    simpa only [d4618, d1035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9001 (p : Pattern) (guard : d4618 p = 1) : d1036 p ≤ (0 : Int) + d4766 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1036, d4766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8997 p hg
    simpa only [d1036, d4766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1036, d4766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9000 p hg
    simpa only [d1036, d4766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9002 (p : Pattern) (guard : d4618 p = 1) : d1037 p ≤ (0 : Int) + d4768 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1037, d4768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9001 p hg
    simpa only [d1037, d4768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1037, d4768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8969 p hg
    simpa only [d1037, d4768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9003 (p : Pattern) (guard : d4618 p = 1) : d1038 p ≤ (0 : Int) + d4771 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1038, d4771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8969 p hg
    simpa only [d1038, d4771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1038, d4771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8975 p hg
    simpa only [d1038, d4771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9004 (p : Pattern) (guard : d4618 p = 1) : d1039 p ≤ (0 : Int) + d4772 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1039, d4772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9002 p hg
    simpa only [d1039, d4772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1039, d4772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9003 p hg
    simpa only [d1039, d4772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9005 (p : Pattern) (guard : d4618 p = 1) : d1040 p ≤ (0 : Int) + d4773 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1040, d4773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8994 p hg
    simpa only [d1040, d4773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1040, d4773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9004 p hg
    simpa only [d1040, d4773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9006 (p : Pattern) (guard : d4618 p = 1) : d1041 p ≤ (0 : Int) + d4773 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8978 p hg
    simpa only [d1041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9005 p hg
    simpa only [d1041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9007 (p : Pattern) (guard : d0 p = 1) : d1042 p ≤ (0 : Int) + d857 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9008 (p : Pattern) (guard : d1 p = 1) : d1043 p ≤ (0 : Int) + d118 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2046 p hg
    simpa only [d1043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3757 p hg
    simpa only [d1043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9009 (p : Pattern) (guard : d0 p = 1) : d371 p ≤ (0 : Int) + d149 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9010 (p : Pattern) (guard : d4395 p = 1) : d1044 p ≤ (0 : Int) + d857 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1044, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9008 p hg
    simpa only [d4395, d1044, d857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1044, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9009 p hg
    simpa only [d4395, d1044, d857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9011 (p : Pattern) (guard : d4617 p = 1) : d1045 p ≤ (0 : Int) + d857 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d1045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9007 p hg
    simpa only [d4617, d1045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d1045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9010 p hg
    simpa only [d4617, d1045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9012 (p : Pattern) (guard : d0 p = 1) : d1048 p ≤ (0 : Int) + d857 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9013 (p : Pattern) (guard : d4618 p = 1) : d1049 p ≤ (0 : Int) + d857 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d1049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9011 p hg
    simpa only [d4618, d1049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d1049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9012 p hg
    simpa only [d4618, d1049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9014 (p : Pattern) (guard : d0 p = 1) : d1050 p ≤ (0 : Int) + d864 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9015 (p : Pattern) (guard : d4617 p = 1) : d1052 p ≤ (0 : Int) + d864 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d1052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9014 p hg
    simpa only [d4617, d1052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d1052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8785 p hg
    simpa only [d4617, d1052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9016 (p : Pattern) (guard : d0 p = 1) : d1055 p ≤ (0 : Int) + d864 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9017 (p : Pattern) (guard : d4618 p = 1) : d1056 p ≤ (0 : Int) + d864 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d1056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9015 p hg
    simpa only [d4618, d1056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d1056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9016 p hg
    simpa only [d4618, d1056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9018 (p : Pattern) (guard : d4618 p = 1) : d1057 p ≤ (0 : Int) + d4774 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1057, d4774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9013 p hg
    simpa only [d1057, d4774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1057, d4774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9017 p hg
    simpa only [d1057, d4774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9019 (p : Pattern) (guard : d0 p = 1) : d1058 p ≤ (0 : Int) + d869 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9020 (p : Pattern) (guard : d4395 p = 1) : d1059 p ≤ (0 : Int) + d869 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1059, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1435 p hg
    simpa only [d4395, d1059, d869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1059, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8792 p hg
    simpa only [d4395, d1059, d869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9021 (p : Pattern) (guard : d4617 p = 1) : d1060 p ≤ (0 : Int) + d869 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9019 p hg
    simpa only [d4617, d1060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9020 p hg
    simpa only [d4617, d1060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9022 (p : Pattern) (guard : d0 p = 1) : d1062 p ≤ (0 : Int) + d869 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9023 (p : Pattern) (guard : d4618 p = 1) : d1063 p ≤ (0 : Int) + d869 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9021 p hg
    simpa only [d4618, d1063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9022 p hg
    simpa only [d4618, d1063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9024 (p : Pattern) (guard : d0 p = 1) : d1059 p ≤ (0 : Int) + d874 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9025 (p : Pattern) (guard : d4617 p = 1) : d1065 p ≤ (0 : Int) + d874 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9024 p hg
    simpa only [d4617, d1065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8801 p hg
    simpa only [d4617, d1065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9026 (p : Pattern) (guard : d0 p = 1) : d1066 p ≤ (0 : Int) + d874 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9027 (p : Pattern) (guard : d4618 p = 1) : d1067 p ≤ (0 : Int) + d874 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9025 p hg
    simpa only [d4618, d1067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9026 p hg
    simpa only [d4618, d1067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9028 (p : Pattern) (guard : d4618 p = 1) : d1068 p ≤ (0 : Int) + d4775 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1068, d4775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9023 p hg
    simpa only [d1068, d4775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1068, d4775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9027 p hg
    simpa only [d1068, d4775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9029 (p : Pattern) (guard : d4618 p = 1) : d1069 p ≤ (0 : Int) + d4776 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1069, d4776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9018 p hg
    simpa only [d1069, d4776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1069, d4776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9028 p hg
    simpa only [d1069, d4776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9030 (p : Pattern) (guard : d0 p = 1) : d1070 p ≤ (0 : Int) + d869 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9031 (p : Pattern) (guard : d4617 p = 1) : d1071 p ≤ (0 : Int) + d869 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d1071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9030 p hg
    simpa only [d4617, d1071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d1071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9020 p hg
    simpa only [d4617, d1071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9032 (p : Pattern) (guard : d4618 p = 1) : d1072 p ≤ (0 : Int) + d869 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d1072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9031 p hg
    simpa only [d4618, d1072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d1072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9022 p hg
    simpa only [d4618, d1072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9033 (p : Pattern) (guard : d0 p = 1) : d1073 p ≤ (0 : Int) + d874 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9034 (p : Pattern) (guard : d4617 p = 1) : d1074 p ≤ (0 : Int) + d874 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d1074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9033 p hg
    simpa only [d4617, d1074, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d1074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8801 p hg
    simpa only [d4617, d1074, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9035 (p : Pattern) (guard : d4618 p = 1) : d1075 p ≤ (0 : Int) + d874 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d1075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9034 p hg
    simpa only [d4618, d1075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d1075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9026 p hg
    simpa only [d4618, d1075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9036 (p : Pattern) (guard : d4618 p = 1) : d1076 p ≤ (0 : Int) + d4775 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1076, d4775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9032 p hg
    simpa only [d1076, d4775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1076, d4775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9035 p hg
    simpa only [d1076, d4775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9037 (p : Pattern) (guard : d0 p = 1) : d159 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9038 (p : Pattern) (guard : d4617 p = 1) : d160 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9037 p hg
    simpa only [d4617, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7817 p hg
    simpa only [d4617, d160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9039 (p : Pattern) (guard : d4618 p = 1) : d161 p ≤ (0 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9038 p hg
    simpa only [d4618, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4618, d161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9040 (p : Pattern) (guard : d4618 p = 1) : d162 p ≤ (0 : Int) + d12 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9039 p hg
    simpa only [d162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8975 p hg
    simpa only [d162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9041 (p : Pattern) (guard : d4618 p = 1) : d1077 p ≤ (0 : Int) + d4777 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1077, d4777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9036 p hg
    simpa only [d1077, d4777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1077, d4777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9040 p hg
    simpa only [d1077, d4777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9042 (p : Pattern) (guard : d4618 p = 1) : d1078 p ≤ (0 : Int) + d4778 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1078, d4778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9029 p hg
    simpa only [d1078, d4778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1078, d4778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9041 p hg
    simpa only [d1078, d4778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9043 (p : Pattern) (guard : d0 p = 1) : d1079 p ≤ (0 : Int) + d857 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9044 (p : Pattern) (guard : d4395 p = 1) : d1080 p ≤ (0 : Int) + d857 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1080, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9008 p hg
    simpa only [d4395, d1080, d857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1080, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8792 p hg
    simpa only [d4395, d1080, d857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9045 (p : Pattern) (guard : d4617 p = 1) : d1081 p ≤ (0 : Int) + d857 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d1081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9043 p hg
    simpa only [d4617, d1081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d1081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9044 p hg
    simpa only [d4617, d1081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9046 (p : Pattern) (guard : d0 p = 1) : d1083 p ≤ (0 : Int) + d857 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9047 (p : Pattern) (guard : d4618 p = 1) : d1084 p ≤ (0 : Int) + d857 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d1084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9045 p hg
    simpa only [d4618, d1084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d1084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9046 p hg
    simpa only [d4618, d1084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9048 (p : Pattern) (guard : d0 p = 1) : d1085 p ≤ (0 : Int) + d864 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9049 (p : Pattern) (guard : d4617 p = 1) : d1086 p ≤ (0 : Int) + d864 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9048 p hg
    simpa only [d4617, d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8785 p hg
    simpa only [d4617, d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9050 (p : Pattern) (guard : d4618 p = 1) : d1087 p ≤ (0 : Int) + d864 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9049 p hg
    simpa only [d4618, d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9016 p hg
    simpa only [d4618, d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9051 (p : Pattern) (guard : d4618 p = 1) : d1088 p ≤ (0 : Int) + d4774 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1088, d4774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9047 p hg
    simpa only [d1088, d4774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1088, d4774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9050 p hg
    simpa only [d1088, d4774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9052 (p : Pattern) (guard : d0 p = 1) : d1089 p ≤ (0 : Int) + d869 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9053 (p : Pattern) (guard : d4617 p = 1) : d1090 p ≤ (0 : Int) + d869 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9052 p hg
    simpa only [d4617, d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9020 p hg
    simpa only [d4617, d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9054 (p : Pattern) (guard : d4618 p = 1) : d1091 p ≤ (0 : Int) + d869 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9053 p hg
    simpa only [d4618, d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9022 p hg
    simpa only [d4618, d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9055 (p : Pattern) (guard : d4618 p = 1) : d1092 p ≤ (0 : Int) + d4775 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1092, d4775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9054 p hg
    simpa only [d1092, d4775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1092, d4775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9027 p hg
    simpa only [d1092, d4775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9056 (p : Pattern) (guard : d4618 p = 1) : d1093 p ≤ (0 : Int) + d4776 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1093, d4776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9051 p hg
    simpa only [d1093, d4776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1093, d4776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9055 p hg
    simpa only [d1093, d4776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9057 (p : Pattern) (guard : d4618 p = 1) : d1094 p ≤ (0 : Int) + d4777 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1094, d4777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9055 p hg
    simpa only [d1094, d4777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1094, d4777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8975 p hg
    simpa only [d1094, d4777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9058 (p : Pattern) (guard : d4618 p = 1) : d1095 p ≤ (0 : Int) + d4778 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1095, d4778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9056 p hg
    simpa only [d1095, d4778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1095, d4778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9057 p hg
    simpa only [d1095, d4778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9059 (p : Pattern) (guard : d4618 p = 1) : d1096 p ≤ (0 : Int) + d4778 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9042 p hg
    simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9058 p hg
    simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9060 (p : Pattern) (guard : d4618 p = 1) : d1097 p ≤ (0 : Int) + d4779 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1097, d4779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8978 p hg
    simpa only [d1097, d4779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1097, d4779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9059 p hg
    simpa only [d1097, d4779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9061 (p : Pattern) (guard : d4618 p = 1) : d1098 p ≤ (0 : Int) + d4780 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1098, d4780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9006 p hg
    simpa only [d1098, d4780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1098, d4780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9060 p hg
    simpa only [d1098, d4780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9062 (p : Pattern) (guard : d0 p = 1) : d1001 p ≤ (0 : Int) + d899 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9063 (p : Pattern) (guard : d4395 p = 1) : d966 p ≤ (0 : Int) + d899 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d966, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare846 p hg
    simpa only [d4395, d966, d899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d966, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8839 p hg
    simpa only [d4395, d966, d899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9064 (p : Pattern) (guard : d4617 p = 1) : d1002 p ≤ (0 : Int) + d899 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d1002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9062 p hg
    simpa only [d4617, d1002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d1002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9063 p hg
    simpa only [d4617, d1002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9065 (p : Pattern) (guard : d0 p = 1) : d969 p ≤ (0 : Int) + d899 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9066 (p : Pattern) (guard : d4618 p = 1) : d1003 p ≤ (0 : Int) + d899 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d1003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9064 p hg
    simpa only [d4618, d1003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d1003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9065 p hg
    simpa only [d4618, d1003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9067 (p : Pattern) (guard : d0 p = 1) : d968 p ≤ (0 : Int) + d903 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9068 (p : Pattern) (guard : d1 p = 1) : d808 p ≤ (0 : Int) + d20 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare835 p hg
    simpa only [d808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare847 p hg
    simpa only [d808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9069 (p : Pattern) (guard : d4395 p = 1) : d972 p ≤ (0 : Int) + d903 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d972, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9068 p hg
    simpa only [d4395, d972, d903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d972, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8846 p hg
    simpa only [d4395, d972, d903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9070 (p : Pattern) (guard : d4617 p = 1) : d1099 p ≤ (0 : Int) + d903 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9067 p hg
    simpa only [d4617, d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9069 p hg
    simpa only [d4617, d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9071 (p : Pattern) (guard : d0 p = 1) : d1101 p ≤ (0 : Int) + d903 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9072 (p : Pattern) (guard : d4618 p = 1) : d1102 p ≤ (0 : Int) + d903 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d1102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9070 p hg
    simpa only [d4618, d1102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d1102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9071 p hg
    simpa only [d4618, d1102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9073 (p : Pattern) (guard : d4618 p = 1) : d1103 p ≤ (0 : Int) + d4781 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1103, d4781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9066 p hg
    simpa only [d1103, d4781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1103, d4781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9072 p hg
    simpa only [d1103, d4781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9074 (p : Pattern) (guard : d4618 p = 1) : d1104 p ≤ (0 : Int) + d4782 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1104, d4782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9001 p hg
    simpa only [d1104, d4782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1104, d4782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9073 p hg
    simpa only [d1104, d4782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9075 (p : Pattern) (guard : d4618 p = 1) : d1105 p ≤ (0 : Int) + d4783 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1105, d4783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9073 p hg
    simpa only [d1105, d4783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1105, d4783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8975 p hg
    simpa only [d1105, d4783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9076 (p : Pattern) (guard : d4618 p = 1) : d1106 p ≤ (0 : Int) + d4784 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1106, d4784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9074 p hg
    simpa only [d1106, d4784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1106, d4784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9075 p hg
    simpa only [d1106, d4784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9077 (p : Pattern) (guard : d4618 p = 1) : d1107 p ≤ (0 : Int) + d4785 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1107, d4785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8994 p hg
    simpa only [d1107, d4785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1107, d4785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9076 p hg
    simpa only [d1107, d4785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9078 (p : Pattern) (guard : d4618 p = 1) : d1108 p ≤ (0 : Int) + d4786 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1108, d4786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8978 p hg
    simpa only [d1108, d4786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1108, d4786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9077 p hg
    simpa only [d1108, d4786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9079 (p : Pattern) (guard : d0 p = 1) : d1109 p ≤ (0 : Int) + d864 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9080 (p : Pattern) (guard : d4617 p = 1) : d1110 p ≤ (0 : Int) + d864 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d1110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9079 p hg
    simpa only [d4617, d1110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d1110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8785 p hg
    simpa only [d4617, d1110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9081 (p : Pattern) (guard : d4618 p = 1) : d1111 p ≤ (0 : Int) + d864 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d1111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9080 p hg
    simpa only [d4618, d1111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d1111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9016 p hg
    simpa only [d4618, d1111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9082 (p : Pattern) (guard : d4618 p = 1) : d1112 p ≤ (0 : Int) + d4774 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1112, d4774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9013 p hg
    simpa only [d1112, d4774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1112, d4774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9081 p hg
    simpa only [d1112, d4774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9083 (p : Pattern) (guard : d4618 p = 1) : d1113 p ≤ (0 : Int) + d4776 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1113, d4776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9082 p hg
    simpa only [d1113, d4776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1113, d4776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9028 p hg
    simpa only [d1113, d4776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9084 (p : Pattern) (guard : d4618 p = 1) : d1114 p ≤ (0 : Int) + d4775 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1114, d4775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9032 p hg
    simpa only [d1114, d4775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1114, d4775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9027 p hg
    simpa only [d1114, d4775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9085 (p : Pattern) (guard : d4618 p = 1) : d1115 p ≤ (0 : Int) + d4777 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1115, d4777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9084 p hg
    simpa only [d1115, d4777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1115, d4777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9040 p hg
    simpa only [d1115, d4777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9086 (p : Pattern) (guard : d4618 p = 1) : d1116 p ≤ (0 : Int) + d4778 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1116, d4778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9083 p hg
    simpa only [d1116, d4778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1116, d4778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9085 p hg
    simpa only [d1116, d4778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9087 (p : Pattern) (guard : d0 p = 1) : d1117 p ≤ (0 : Int) + d922 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9088 (p : Pattern) (guard : d1 p = 1) : d291 p ≤ (0 : Int) + d269 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1364 p hg
    simpa only [d291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2440 p hg
    simpa only [d291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9089 (p : Pattern) (guard : d4395 p = 1) : d1118 p ≤ (0 : Int) + d922 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4395, d1118, d922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9088 p hg
    simpa only [d4395, d1118, d922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4395, d1118, d922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8792 p hg
    simpa only [d4395, d1118, d922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9090 (p : Pattern) (guard : d4617 p = 1) : d1119 p ≤ (0 : Int) + d922 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d1119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9087 p hg
    simpa only [d4617, d1119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d1119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9089 p hg
    simpa only [d4617, d1119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9091 (p : Pattern) (guard : d0 p = 1) : d1122 p ≤ (0 : Int) + d922 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9092 (p : Pattern) (guard : d4618 p = 1) : d1123 p ≤ (0 : Int) + d922 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d1123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9090 p hg
    simpa only [d4618, d1123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d1123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9091 p hg
    simpa only [d4618, d1123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9093 (p : Pattern) (guard : d0 p = 1) : d1059 p ≤ (0 : Int) + d926 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9094 (p : Pattern) (guard : d4617 p = 1) : d1125 p ≤ (0 : Int) + d926 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4617, d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9093 p hg
    simpa only [d4617, d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4395 p = 1 := by simpa only [d4617, d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8880 p hg
    simpa only [d4617, d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9095 (p : Pattern) (guard : d0 p = 1) : d1130 p ≤ (0 : Int) + d926 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9096 (p : Pattern) (guard : d4618 p = 1) : d1131 p ≤ (0 : Int) + d926 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4617 p = 1 := by simpa only [d4618, d1131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9094 p hg
    simpa only [d4618, d1131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4618, d1131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9095 p hg
    simpa only [d4618, d1131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9097 (p : Pattern) (guard : d4618 p = 1) : d1132 p ≤ (0 : Int) + d4787 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4618 p = 1 := by simpa only [d1132, d4787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9092 p hg
    simpa only [d1132, d4787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4618 p = 1 := by simpa only [d1132, d4787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9096 p hg
    simpa only [d1132, d4787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare9098 (p : Pattern) (guard : d0 p = 1) : d1089 p ≤ (0 : Int) + d245 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare9099 (p : Pattern) (guard : d1 p = 1) : d268 p ≤ (0 : Int) + d116 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1249 p hg
    simpa only [d268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d268, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
