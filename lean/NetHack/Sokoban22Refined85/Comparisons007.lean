/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons006
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare980 (p : Pattern) (guard : d1 p = 1) : d87 p ≤ (0 : Int) + d250 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d87, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare963 p hg
    simpa only [d87, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d87, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare979 p hg
    simpa only [d87, d250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare981 (p : Pattern) (guard : d1 p = 1) : d88 p ≤ (0 : Int) + d251 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d88, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare934 p hg
    simpa only [d88, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d88, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare980 p hg
    simpa only [d88, d251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare982 (p : Pattern) (guard : d1 p = 1) : d19 p ≤ (0 : Int) + d25 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare928 p hg
    simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d19, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare983 (p : Pattern) (guard : d1 p = 1) : d20 p ≤ (0 : Int) + d26 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d20, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare928 p hg
    simpa only [d20, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d20, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare982 p hg
    simpa only [d20, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare984 (p : Pattern) (guard : d1 p = 1) : d21 p ≤ (0 : Int) + d252 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d21, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare936 p hg
    simpa only [d21, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d21, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare983 p hg
    simpa only [d21, d252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare985 (p : Pattern) (guard : d1 p = 1) : d22 p ≤ (0 : Int) + d253 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d22, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare682 p hg
    simpa only [d22, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d22, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare984 p hg
    simpa only [d22, d253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare986 (p : Pattern) (guard : d1 p = 1) : d21 p ≤ (0 : Int) + d254 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d21, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare945 p hg
    simpa only [d21, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d21, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare983 p hg
    simpa only [d21, d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare987 (p : Pattern) (guard : d1 p = 1) : d28 p ≤ (0 : Int) + d255 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d28, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare986 p hg
    simpa only [d28, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d28, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare947 p hg
    simpa only [d28, d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare988 (p : Pattern) (guard : d1 p = 1) : d29 p ≤ (0 : Int) + d256 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d29, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare985 p hg
    simpa only [d29, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d29, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare987 p hg
    simpa only [d29, d256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare989 (p : Pattern) (guard : d1 p = 1) : d6 p ≤ (0 : Int) + d11 p := by
  change (6 : Int) ≤ (0 : Int) + 11
  decide
theorem compare990 (p : Pattern) (guard : d1 p = 1) : d34 p ≤ (0 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d34, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare989 p hg
    simpa only [d34, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d34, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d34, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare991 (p : Pattern) (guard : d1 p = 1) : d35 p ≤ (0 : Int) + d40 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d35, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare989 p hg
    simpa only [d35, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d35, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare990 p hg
    simpa only [d35, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare992 (p : Pattern) (guard : d1 p = 1) : d36 p ≤ (0 : Int) + d41 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d36, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare991 p hg
    simpa only [d36, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d36, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d36, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare993 (p : Pattern) (guard : d1 p = 1) : d78 p ≤ (0 : Int) + d62 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d78, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare991 p hg
    simpa only [d78, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d78, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare992 p hg
    simpa only [d78, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare994 (p : Pattern) (guard : d1 p = 1) : d79 p ≤ (0 : Int) + d257 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d79, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare954 p hg
    simpa only [d79, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d79, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare993 p hg
    simpa only [d79, d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare995 (p : Pattern) (guard : d1 p = 1) : d80 p ≤ (0 : Int) + d258 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d80, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare994 p hg
    simpa only [d80, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d80, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare735 p hg
    simpa only [d80, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare996 (p : Pattern) (guard : d1 p = 1) : d81 p ≤ (0 : Int) + d259 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d81, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare995 p hg
    simpa only [d81, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d81, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d81, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare997 (p : Pattern) (guard : d1 p = 1) : d82 p ≤ (0 : Int) + d260 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d82, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare988 p hg
    simpa only [d82, d260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d82, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare996 p hg
    simpa only [d82, d260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare998 (p : Pattern) (guard : d1 p = 1) : d87 p ≤ (0 : Int) + d261 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d87, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare997 p hg
    simpa only [d87, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d87, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare979 p hg
    simpa only [d87, d261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare999 (p : Pattern) (guard : d1 p = 1) : d99 p ≤ (0 : Int) + d262 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d99, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare998 p hg
    simpa only [d99, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d99, d262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d99, d262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1000 (p : Pattern) (guard : d1 p = 1) : d100 p ≤ (0 : Int) + d263 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d100, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare981 p hg
    simpa only [d100, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d100, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare999 p hg
    simpa only [d100, d263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1001 (p : Pattern) (guard : d1 p = 1) : d101 p ≤ (0 : Int) + d264 p := by
  cases selected : p 115 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d101, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare888 p hg
    simpa only [d101, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d101, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1000 p hg
    simpa only [d101, d264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1002 (p : Pattern) (guard : d0 p = 1) : d264 p ≤ (0 : Int) + d264 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1003 (p : Pattern) (guard : d4042 p = 1) : d265 p ≤ (0 : Int) + d264 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4042, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1001 p hg
    simpa only [d4042, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4042, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1002 p hg
    simpa only [d4042, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1004 (p : Pattern) (guard : d4042 p = 1) : d266 p ≤ (0 : Int) + d4055 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4042 p = 1 := by simpa only [d266, d4055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare865 p hg
    simpa only [d266, d4055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4042 p = 1 := by simpa only [d266, d4055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1003 p hg
    simpa only [d266, d4055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1005 (p : Pattern) (guard : d4042 p = 1) : d267 p ≤ (0 : Int) + d4056 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4042 p = 1 := by simpa only [d267, d4056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare776 p hg
    simpa only [d267, d4056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4042 p = 1 := by simpa only [d267, d4056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1004 p hg
    simpa only [d267, d4056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1006 (p : Pattern) (guard : d0 p = 1) : d209 p ≤ (0 : Int) + d446 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1007 (p : Pattern) (guard : d4042 p = 1) : d210 p ≤ (0 : Int) + d485 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4042, d210, d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5 p hg
    simpa only [d4042, d210, d485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4042, d210, d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1006 p hg
    simpa only [d4042, d210, d485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1008 (p : Pattern) (guard : d0 p = 1) : d264 p ≤ (0 : Int) + d478 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1009 (p : Pattern) (guard : d4042 p = 1) : d265 p ≤ (0 : Int) + d486 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4042, d265, d486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5 p hg
    simpa only [d4042, d265, d486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4042, d265, d486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1008 p hg
    simpa only [d4042, d265, d486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1010 (p : Pattern) (guard : d4042 p = 1) : d266 p ≤ (0 : Int) + d487 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4042 p = 1 := by simpa only [d266, d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1007 p hg
    simpa only [d266, d487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4042 p = 1 := by simpa only [d266, d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1009 p hg
    simpa only [d266, d487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1011 (p : Pattern) (guard : d4042 p = 1) : d267 p ≤ (0 : Int) + d488 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4042 p = 1 := by simpa only [d267, d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare539 p hg
    simpa only [d267, d488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4042 p = 1 := by simpa only [d267, d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1010 p hg
    simpa only [d267, d488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1012 (p : Pattern) (guard : d0 p = 1) : d209 p ≤ (0 : Int) + d101 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1013 (p : Pattern) (guard : d4042 p = 1) : d210 p ≤ (0 : Int) + d101 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4042, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5 p hg
    simpa only [d4042, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4042, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1012 p hg
    simpa only [d4042, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1014 (p : Pattern) (guard : d0 p = 1) : d265 p ≤ (0 : Int) + d479 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1015 (p : Pattern) (guard : d4048 p = 1) : d266 p ≤ (0 : Int) + d483 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4042 p = 1 := by simpa only [d4048, d266, d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1013 p hg
    simpa only [d4048, d266, d483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4048, d266, d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1014 p hg
    simpa only [d4048, d266, d483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1016 (p : Pattern) (guard : d4052 p = 1) : d267 p ≤ (0 : Int) + d484 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4040 p = 1 := by simpa only [d4052, d267, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7 p hg
    simpa only [d4052, d267, d484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4048 p = 1 := by simpa only [d4052, d267, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1015 p hg
    simpa only [d4052, d267, d484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1017 (p : Pattern) (guard : d4042 p = 1) : d169 p ≤ (0 : Int) + d169 p := by
  omega
theorem compare1018 (p : Pattern) (guard : d0 p = 1) : d264 p ≤ (0 : Int) + d309 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1019 (p : Pattern) (guard : d4042 p = 1) : d265 p ≤ (0 : Int) + d310 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4042, d265, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5 p hg
    simpa only [d4042, d265, d310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4042, d265, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1018 p hg
    simpa only [d4042, d265, d310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1020 (p : Pattern) (guard : d4042 p = 1) : d266 p ≤ (0 : Int) + d311 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4042 p = 1 := by simpa only [d266, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1013 p hg
    simpa only [d266, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4042 p = 1 := by simpa only [d266, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1019 p hg
    simpa only [d266, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1021 (p : Pattern) (guard : d4042 p = 1) : d267 p ≤ (0 : Int) + d312 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4042 p = 1 := by simpa only [d267, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1017 p hg
    simpa only [d267, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4042 p = 1 := by simpa only [d267, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1020 p hg
    simpa only [d267, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1022 (p : Pattern) (guard : d0 p = 1) : d446 p ≤ (0 : Int) + d101 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1023 (p : Pattern) (guard : d4042 p = 1) : d485 p ≤ (0 : Int) + d101 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4042, d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5 p hg
    simpa only [d4042, d485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4042, d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1022 p hg
    simpa only [d4042, d485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1024 (p : Pattern) (guard : d0 p = 1) : d485 p ≤ (0 : Int) + d447 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1025 (p : Pattern) (guard : d4048 p = 1) : d485 p ≤ (0 : Int) + d482 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4042 p = 1 := by simpa only [d4048, d482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1023 p hg
    simpa only [d4048, d482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4048, d482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1024 p hg
    simpa only [d4048, d482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1026 (p : Pattern) (guard : d0 p = 1) : d486 p ≤ (0 : Int) + d479 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1027 (p : Pattern) (guard : d4048 p = 1) : d487 p ≤ (0 : Int) + d483 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4042 p = 1 := by simpa only [d4048, d487, d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1023 p hg
    simpa only [d4048, d487, d483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4048, d487, d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1026 p hg
    simpa only [d4048, d487, d483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1028 (p : Pattern) (guard : d4048 p = 1) : d488 p ≤ (0 : Int) + d484 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4048 p = 1 := by simpa only [d488, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1025 p hg
    simpa only [d488, d484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4048 p = 1 := by simpa only [d488, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1027 p hg
    simpa only [d488, d484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1029 (p : Pattern) (guard : d0 p = 1) : d485 p ≤ (1 : Int) + d101 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1030 (p : Pattern) (guard : d0 p = 1) : d446 p ≤ (1 : Int) + d101 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1031 (p : Pattern) (guard : d4042 p = 1) : d485 p ≤ (1 : Int) + d101 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4042, d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24 p hg
    simpa only [d4042, d485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4042, d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1030 p hg
    simpa only [d4042, d485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1032 (p : Pattern) (guard : d4043 p = 1) : d485 p ≤ (1 : Int) + d101 p := by
  cases selected : p 49 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1029 p hg
    simpa only [d4043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4042 p = 1 := by simpa only [d4043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1031 p hg
    simpa only [d4043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1033 (p : Pattern) (guard : d0 p = 1) : d478 p ≤ (1 : Int) + d101 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1034 (p : Pattern) (guard : d4042 p = 1) : d486 p ≤ (1 : Int) + d101 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4042, d486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24 p hg
    simpa only [d4042, d486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4042, d486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1033 p hg
    simpa only [d4042, d486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1035 (p : Pattern) (guard : d4043 p = 1) : d487 p ≤ (1 : Int) + d101 p := by
  cases selected : p 49 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4043, d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1029 p hg
    simpa only [d4043, d487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4042 p = 1 := by simpa only [d4043, d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1034 p hg
    simpa only [d4043, d487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1036 (p : Pattern) (guard : d4043 p = 1) : d488 p ≤ (1 : Int) + d101 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4043 p = 1 := by simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1032 p hg
    simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4043 p = 1 := by simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1035 p hg
    simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1037 (p : Pattern) (guard : d0 p = 1) : d446 p ≤ (0 : Int) + d167 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1038 (p : Pattern) (guard : d4042 p = 1) : d485 p ≤ (0 : Int) + d168 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4042, d485, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5 p hg
    simpa only [d4042, d485, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4042, d485, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1037 p hg
    simpa only [d4042, d485, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1039 (p : Pattern) (guard : d4042 p = 1) : d485 p ≤ (0 : Int) + d169 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4042 p = 1 := by simpa only [d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1023 p hg
    simpa only [d169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4042 p = 1 := by simpa only [d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1038 p hg
    simpa only [d169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1040 (p : Pattern) (guard : d0 p = 1) : d478 p ≤ (0 : Int) + d309 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1041 (p : Pattern) (guard : d4042 p = 1) : d486 p ≤ (0 : Int) + d310 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4042, d486, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5 p hg
    simpa only [d4042, d486, d310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4042, d486, d310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1040 p hg
    simpa only [d4042, d486, d310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1042 (p : Pattern) (guard : d4042 p = 1) : d487 p ≤ (0 : Int) + d311 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4042 p = 1 := by simpa only [d487, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1023 p hg
    simpa only [d487, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4042 p = 1 := by simpa only [d487, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1041 p hg
    simpa only [d487, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1043 (p : Pattern) (guard : d4042 p = 1) : d488 p ≤ (0 : Int) + d312 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4042 p = 1 := by simpa only [d488, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1039 p hg
    simpa only [d488, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4042 p = 1 := by simpa only [d488, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1042 p hg
    simpa only [d488, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1044 (p : Pattern) (guard : d1 p = 1) : d88 p ≤ (0 : Int) + d88 p := by
  omega
theorem compare1045 (p : Pattern) (guard : d1 p = 1) : d87 p ≤ (0 : Int) + d87 p := by
  omega
theorem compare1046 (p : Pattern) (guard : d1 p = 1) : d89 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare870 p hg
    simpa only [d89, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare734 p hg
    simpa only [d89, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1047 (p : Pattern) (guard : d1 p = 1) : d90 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1046 p hg
    simpa only [d90, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare735 p hg
    simpa only [d90, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1048 (p : Pattern) (guard : d1 p = 1) : d92 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1047 p hg
    simpa only [d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare763 p hg
    simpa only [d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1049 (p : Pattern) (guard : d1 p = 1) : d94 p ≤ (0 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1048 p hg
    simpa only [d94, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare765 p hg
    simpa only [d94, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1050 (p : Pattern) (guard : d1 p = 1) : d96 p ≤ (0 : Int) + d12 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1049 p hg
    simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare767 p hg
    simpa only [d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1051 (p : Pattern) (guard : d1 p = 1) : d97 p ≤ (0 : Int) + d99 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d97, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1045 p hg
    simpa only [d97, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d97, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1050 p hg
    simpa only [d97, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1052 (p : Pattern) (guard : d1 p = 1) : d98 p ≤ (0 : Int) + d100 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d98, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1044 p hg
    simpa only [d98, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d98, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1051 p hg
    simpa only [d98, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1053 (p : Pattern) (guard : d0 p = 1) : d100 p ≤ (0 : Int) + d100 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1054 (p : Pattern) (guard : d4058 p = 1) : d101 p ≤ (0 : Int) + d100 p := by
  cases selected : p 115 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4058, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1052 p hg
    simpa only [d4058, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4058, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1053 p hg
    simpa only [d4058, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1055 (p : Pattern) (guard : d0 p = 1) : d446 p ≤ (0 : Int) + d100 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1056 (p : Pattern) (guard : d4059 p = 1) : d485 p ≤ (0 : Int) + d100 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d4059, d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1054 p hg
    simpa only [d4059, d485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4059, d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1055 p hg
    simpa only [d4059, d485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1057 (p : Pattern) (guard : d0 p = 1) : d446 p ≤ (0 : Int) + d166 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1058 (p : Pattern) (guard : d4059 p = 1) : d485 p ≤ (0 : Int) + d4060 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d4059, d485, d4060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1054 p hg
    simpa only [d4059, d485, d4060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4059, d485, d4060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1057 p hg
    simpa only [d4059, d485, d4060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1059 (p : Pattern) (guard : d4059 p = 1) : d485 p ≤ (0 : Int) + d4061 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4059 p = 1 := by simpa only [d4061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1056 p hg
    simpa only [d4061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4059 p = 1 := by simpa only [d4061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1058 p hg
    simpa only [d4061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1060 (p : Pattern) (guard : d0 p = 1) : d478 p ≤ (0 : Int) + d308 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1061 (p : Pattern) (guard : d4059 p = 1) : d486 p ≤ (0 : Int) + d4062 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d4059, d486, d4062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1054 p hg
    simpa only [d4059, d486, d4062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4059, d486, d4062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1060 p hg
    simpa only [d4059, d486, d4062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1062 (p : Pattern) (guard : d4059 p = 1) : d487 p ≤ (0 : Int) + d4063 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4059 p = 1 := by simpa only [d487, d4063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1056 p hg
    simpa only [d487, d4063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4059 p = 1 := by simpa only [d487, d4063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1061 p hg
    simpa only [d487, d4063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1063 (p : Pattern) (guard : d4059 p = 1) : d488 p ≤ (0 : Int) + d4064 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4059 p = 1 := by simpa only [d488, d4064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1059 p hg
    simpa only [d488, d4064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4059 p = 1 := by simpa only [d488, d4064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1062 p hg
    simpa only [d488, d4064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1064 (p : Pattern) (guard : d0 p = 1) : d446 p ≤ (0 : Int) + d209 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1065 (p : Pattern) (guard : d4042 p = 1) : d485 p ≤ (0 : Int) + d210 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4042, d485, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5 p hg
    simpa only [d4042, d485, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4042, d485, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1064 p hg
    simpa only [d4042, d485, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1066 (p : Pattern) (guard : d0 p = 1) : d478 p ≤ (0 : Int) + d264 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1067 (p : Pattern) (guard : d4042 p = 1) : d486 p ≤ (0 : Int) + d265 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4042, d486, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5 p hg
    simpa only [d4042, d486, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4042, d486, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1066 p hg
    simpa only [d4042, d486, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1068 (p : Pattern) (guard : d4042 p = 1) : d487 p ≤ (0 : Int) + d266 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4042 p = 1 := by simpa only [d487, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1065 p hg
    simpa only [d487, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4042 p = 1 := by simpa only [d487, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1067 p hg
    simpa only [d487, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1069 (p : Pattern) (guard : d4042 p = 1) : d488 p ≤ (0 : Int) + d267 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4042 p = 1 := by simpa only [d488, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1039 p hg
    simpa only [d488, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4042 p = 1 := by simpa only [d488, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1068 p hg
    simpa only [d488, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1070 (p : Pattern) (guard : d0 p = 1) : d446 p ≤ (1 : Int) + d167 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1071 (p : Pattern) (guard : d4042 p = 1) : d485 p ≤ (1 : Int) + d168 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4042, d485, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24 p hg
    simpa only [d4042, d485, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4042, d485, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1070 p hg
    simpa only [d4042, d485, d168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1072 (p : Pattern) (guard : d4042 p = 1) : d485 p ≤ (1 : Int) + d169 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4042 p = 1 := by simpa only [d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1031 p hg
    simpa only [d169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4042 p = 1 := by simpa only [d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1071 p hg
    simpa only [d169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1073 (p : Pattern) (guard : d0 p = 1) : d446 p ≤ (1 : Int) + d209 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1074 (p : Pattern) (guard : d4042 p = 1) : d485 p ≤ (1 : Int) + d210 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4042, d485, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24 p hg
    simpa only [d4042, d485, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4042, d485, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1073 p hg
    simpa only [d4042, d485, d210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1075 (p : Pattern) (guard : d0 p = 1) : d478 p ≤ (1 : Int) + d264 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1076 (p : Pattern) (guard : d4042 p = 1) : d486 p ≤ (1 : Int) + d265 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4042, d486, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24 p hg
    simpa only [d4042, d486, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4042, d486, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1075 p hg
    simpa only [d4042, d486, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1077 (p : Pattern) (guard : d4042 p = 1) : d487 p ≤ (1 : Int) + d266 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4042 p = 1 := by simpa only [d487, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1074 p hg
    simpa only [d487, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4042 p = 1 := by simpa only [d487, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1076 p hg
    simpa only [d487, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1078 (p : Pattern) (guard : d4042 p = 1) : d488 p ≤ (1 : Int) + d267 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4042 p = 1 := by simpa only [d488, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1072 p hg
    simpa only [d488, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4042 p = 1 := by simpa only [d488, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1077 p hg
    simpa only [d488, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1079 (p : Pattern) (guard : d0 p = 1) : d485 p ≤ (0 : Int) + d168 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1080 (p : Pattern) (guard : d4048 p = 1) : d485 p ≤ (0 : Int) + d169 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4042 p = 1 := by simpa only [d4048, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1023 p hg
    simpa only [d4048, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4048, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1079 p hg
    simpa only [d4048, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1081 (p : Pattern) (guard : d0 p = 1) : d486 p ≤ (0 : Int) + d310 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1082 (p : Pattern) (guard : d4048 p = 1) : d487 p ≤ (0 : Int) + d311 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4042 p = 1 := by simpa only [d4048, d487, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1023 p hg
    simpa only [d4048, d487, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4048, d487, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1081 p hg
    simpa only [d4048, d487, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1083 (p : Pattern) (guard : d4048 p = 1) : d488 p ≤ (0 : Int) + d312 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4048 p = 1 := by simpa only [d488, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1080 p hg
    simpa only [d488, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4048 p = 1 := by simpa only [d488, d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1082 p hg
    simpa only [d488, d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1084 (p : Pattern) (guard : d0 p = 1) : d487 p ≤ (0 : Int) + d480 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1085 (p : Pattern) (guard : d4047 p = 1) : d488 p ≤ (0 : Int) + d481 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4042 p = 1 := by simpa only [d4047, d488, d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1039 p hg
    simpa only [d4047, d488, d481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4047, d488, d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1084 p hg
    simpa only [d4047, d488, d481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1086 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d0 p := by
  omega
theorem compare1087 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (1 : Int) + d0 p := by
  omega
theorem compare1088 (p : Pattern) (guard : d0 p = 1) : d309 p ≤ (0 : Int) + d478 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1089 (p : Pattern) (guard : d4042 p = 1) : d310 p ≤ (0 : Int) + d486 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4042, d310, d486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5 p hg
    simpa only [d4042, d310, d486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4042, d310, d486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1088 p hg
    simpa only [d4042, d310, d486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1090 (p : Pattern) (guard : d4042 p = 1) : d311 p ≤ (0 : Int) + d487 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4042 p = 1 := by simpa only [d311, d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare536 p hg
    simpa only [d311, d487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4042 p = 1 := by simpa only [d311, d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1089 p hg
    simpa only [d311, d487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1091 (p : Pattern) (guard : d4042 p = 1) : d312 p ≤ (0 : Int) + d488 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4042 p = 1 := by simpa only [d312, d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare539 p hg
    simpa only [d312, d488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4042 p = 1 := by simpa only [d312, d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1090 p hg
    simpa only [d312, d488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1092 (p : Pattern) (guard : d4041 p = 1) : d101 p ≤ (2 : Int) + d101 p := by
  omega
theorem compare1093 (p : Pattern) (guard : d0 p = 1) : d168 p ≤ (2 : Int) + d101 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1094 (p : Pattern) (guard : d4049 p = 1) : d169 p ≤ (2 : Int) + d101 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4041 p = 1 := by simpa only [d4049, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1092 p hg
    simpa only [d4049, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4049, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1093 p hg
    simpa only [d4049, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1095 (p : Pattern) (guard : d0 p = 1) : d310 p ≤ (2 : Int) + d101 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1096 (p : Pattern) (guard : d4049 p = 1) : d311 p ≤ (2 : Int) + d101 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4041 p = 1 := by simpa only [d4049, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1092 p hg
    simpa only [d4049, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4049, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1095 p hg
    simpa only [d4049, d311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1097 (p : Pattern) (guard : d4049 p = 1) : d312 p ≤ (2 : Int) + d101 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4049 p = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1094 p hg
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4049 p = 1 := by simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1096 p hg
    simpa only [d312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1098 (p : Pattern) (guard : d0 p = 1) : d100 p ≤ (0 : Int) + d426 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1099 (p : Pattern) (guard : d4058 p = 1) : d101 p ≤ (0 : Int) + d489 p := by
  cases selected : p 115 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4058, d101, d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare777 p hg
    simpa only [d4058, d101, d489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4058, d101, d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1098 p hg
    simpa only [d4058, d101, d489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1100 (p : Pattern) (guard : d0 p = 1) : d100 p ≤ (0 : Int) + d445 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1101 (p : Pattern) (guard : d4058 p = 1) : d101 p ≤ (0 : Int) + d490 p := by
  cases selected : p 115 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4058, d101, d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare777 p hg
    simpa only [d4058, d101, d490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4058, d101, d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1100 p hg
    simpa only [d4058, d101, d490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1102 (p : Pattern) (guard : d4058 p = 1) : d101 p ≤ (0 : Int) + d491 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1099 p hg
    simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4058 p = 1 := by simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1101 p hg
    simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1103 (p : Pattern) (guard : d1 p = 1) : d164 p ≤ (0 : Int) + d164 p := by
  omega
theorem compare1104 (p : Pattern) (guard : d0 p = 1) : d166 p ≤ (0 : Int) + d445 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1105 (p : Pattern) (guard : d4058 p = 1) : d167 p ≤ (0 : Int) + d492 p := by
  cases selected : p 115 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4058, d167, d492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1103 p hg
    simpa only [d4058, d167, d492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4058, d167, d492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1104 p hg
    simpa only [d4058, d167, d492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1106 (p : Pattern) (guard : d4058 p = 1) : d168 p ≤ (0 : Int) + d493 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d168, d493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1099 p hg
    simpa only [d168, d493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4058 p = 1 := by simpa only [d168, d493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1105 p hg
    simpa only [d168, d493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1107 (p : Pattern) (guard : d4058 p = 1) : d169 p ≤ (0 : Int) + d494 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d169, d494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1102 p hg
    simpa only [d169, d494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4058 p = 1 := by simpa only [d169, d494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1106 p hg
    simpa only [d169, d494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1108 (p : Pattern) (guard : d1 p = 1) : d225 p ≤ (0 : Int) + d225 p := by
  omega
theorem compare1109 (p : Pattern) (guard : d0 p = 1) : d308 p ≤ (0 : Int) + d477 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1110 (p : Pattern) (guard : d4058 p = 1) : d309 p ≤ (0 : Int) + d495 p := by
  cases selected : p 115 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4058, d309, d495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1108 p hg
    simpa only [d4058, d309, d495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4058, d309, d495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1109 p hg
    simpa only [d4058, d309, d495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1111 (p : Pattern) (guard : d4058 p = 1) : d310 p ≤ (0 : Int) + d496 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d310, d496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1099 p hg
    simpa only [d310, d496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4058 p = 1 := by simpa only [d310, d496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1110 p hg
    simpa only [d310, d496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1112 (p : Pattern) (guard : d4058 p = 1) : d311 p ≤ (0 : Int) + d497 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d311, d497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1102 p hg
    simpa only [d311, d497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4058 p = 1 := by simpa only [d311, d497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1111 p hg
    simpa only [d311, d497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1113 (p : Pattern) (guard : d4058 p = 1) : d312 p ≤ (0 : Int) + d498 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4058 p = 1 := by simpa only [d312, d498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1107 p hg
    simpa only [d312, d498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4058 p = 1 := by simpa only [d312, d498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1112 p hg
    simpa only [d312, d498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1114 (p : Pattern) (guard : d1 p = 1) : d312 p ≤ (2 : Int) + d312 p := by
  omega
theorem compare1115 (p : Pattern) (guard : d0 p = 1) : d309 p ≤ (0 : Int) + d264 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare1116 (p : Pattern) (guard : d4042 p = 1) : d310 p ≤ (0 : Int) + d265 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4042, d310, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5 p hg
    simpa only [d4042, d310, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4042, d310, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1115 p hg
    simpa only [d4042, d310, d265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1117 (p : Pattern) (guard : d4042 p = 1) : d311 p ≤ (0 : Int) + d266 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4042 p = 1 := by simpa only [d311, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare570 p hg
    simpa only [d311, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4042 p = 1 := by simpa only [d311, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1116 p hg
    simpa only [d311, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1118 (p : Pattern) (guard : d4042 p = 1) : d312 p ≤ (0 : Int) + d267 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4042 p = 1 := by simpa only [d312, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1017 p hg
    simpa only [d312, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4042 p = 1 := by simpa only [d312, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1117 p hg
    simpa only [d312, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare1119 (p : Pattern) (guard : d0 p = 1) : d97 p ≤ (0 : Int) + d413 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban22Refined85
