/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons249
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare35000 (p : Pattern) (guard : d8106 p = 1) : d66 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d66, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34834 p hg
    simpa only [d8106, d66, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d66, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d66, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35001 (p : Pattern) (guard : d8107 p = 1) : d67 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d67, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d8107, d67, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d67, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35000 p hg
    simpa only [d8107, d67, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35002 (p : Pattern) (guard : d8113 p = 1) : d69 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d69, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35001 p hg
    simpa only [d8113, d69, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d69, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34684 p hg
    simpa only [d8113, d69, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35003 (p : Pattern) (guard : d8119 p = 1) : d75 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d75, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35002 p hg
    simpa only [d8119, d75, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d75, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34692 p hg
    simpa only [d8119, d75, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35004 (p : Pattern) (guard : d8120 p = 1) : d76 p ≤ (0 : Int) + d392 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d76, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34998 p hg
    simpa only [d8120, d76, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d76, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35003 p hg
    simpa only [d8120, d76, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35005 (p : Pattern) (guard : d8121 p = 1) : d77 p ≤ (0 : Int) + d393 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d77, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34964 p hg
    simpa only [d8121, d77, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d77, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35004 p hg
    simpa only [d8121, d77, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35006 (p : Pattern) (guard : d8102 p = 1) : d16 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34655 p hg
    simpa only [d8102, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34830 p hg
    simpa only [d8102, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35007 (p : Pattern) (guard : d8108 p = 1) : d22 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d22, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35006 p hg
    simpa only [d8108, d22, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d22, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34856 p hg
    simpa only [d8108, d22, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35008 (p : Pattern) (guard : d8113 p = 1) : d28 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d28, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34821 p hg
    simpa only [d8113, d28, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d28, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34704 p hg
    simpa only [d8113, d28, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35009 (p : Pattern) (guard : d8114 p = 1) : d29 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d29, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35007 p hg
    simpa only [d8114, d29, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d29, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35008 p hg
    simpa only [d8114, d29, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35010 (p : Pattern) (guard : d8101 p = 1) : d53 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d53, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34527 p hg
    simpa only [d8101, d53, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d53, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34589 p hg
    simpa only [d8101, d53, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35011 (p : Pattern) (guard : d8107 p = 1) : d79 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d79, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35010 p hg
    simpa only [d8107, d79, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d79, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34712 p hg
    simpa only [d8107, d79, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35012 (p : Pattern) (guard : d8113 p = 1) : d80 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d80, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35011 p hg
    simpa only [d8113, d80, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d80, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34607 p hg
    simpa only [d8113, d80, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35013 (p : Pattern) (guard : d8119 p = 1) : d81 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d81, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35012 p hg
    simpa only [d8119, d81, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d81, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d81, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35014 (p : Pattern) (guard : d8120 p = 1) : d82 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d82, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35009 p hg
    simpa only [d8120, d82, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d82, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35013 p hg
    simpa only [d8120, d82, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35015 (p : Pattern) (guard : d8084 p = 1) : d31 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d31, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34584 p hg
    simpa only [d8084, d31, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d31, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34407 p hg
    simpa only [d8084, d31, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35016 (p : Pattern) (guard : d8089 p = 1) : d31 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35015 p hg
    simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34472 p hg
    simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35017 (p : Pattern) (guard : d8094 p = 1) : d31 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35016 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34525 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35018 (p : Pattern) (guard : d8100 p = 1) : d31 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35017 p hg
    simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34678 p hg
    simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35019 (p : Pattern) (guard : d8106 p = 1) : d53 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d53, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35018 p hg
    simpa only [d8106, d53, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d53, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34721 p hg
    simpa only [d8106, d53, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35020 (p : Pattern) (guard : d8107 p = 1) : d54 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d54, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34847 p hg
    simpa only [d8107, d54, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d54, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35019 p hg
    simpa only [d8107, d54, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35021 (p : Pattern) (guard : d8112 p = 1) : d55 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d55, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34853 p hg
    simpa only [d8112, d55, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d55, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34724 p hg
    simpa only [d8112, d55, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35022 (p : Pattern) (guard : d8113 p = 1) : d56 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d56, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35020 p hg
    simpa only [d8113, d56, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d56, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35021 p hg
    simpa only [d8113, d56, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35023 (p : Pattern) (guard : d8119 p = 1) : d65 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d65, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35022 p hg
    simpa only [d8119, d65, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d65, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34731 p hg
    simpa only [d8119, d65, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35024 (p : Pattern) (guard : d8125 p = 1) : d86 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d86, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35023 p hg
    simpa only [d8125, d86, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d86, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34737 p hg
    simpa only [d8125, d86, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35025 (p : Pattern) (guard : d8126 p = 1) : d87 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d87, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35014 p hg
    simpa only [d8126, d87, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d87, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35024 p hg
    simpa only [d8126, d87, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35026 (p : Pattern) (guard : d8127 p = 1) : d88 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d88, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35005 p hg
    simpa only [d8127, d88, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d88, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35025 p hg
    simpa only [d8127, d88, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35027 (p : Pattern) (guard : d8132 p = 1) : d413 p ≤ (0 : Int) + d413 p := by
  omega
theorem compare35028 (p : Pattern) (guard : d8133 p = 1) : d499 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d499, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35026 p hg
    simpa only [d8133, d499, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d499, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35027 p hg
    simpa only [d8133, d499, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35029 (p : Pattern) (guard : d8102 p = 1) : d16 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34782 p hg
    simpa only [d8102, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34878 p hg
    simpa only [d8102, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35030 (p : Pattern) (guard : d8107 p = 1) : d21 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d21, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34847 p hg
    simpa only [d8107, d21, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d21, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34890 p hg
    simpa only [d8107, d21, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35031 (p : Pattern) (guard : d8108 p = 1) : d22 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d22, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35029 p hg
    simpa only [d8108, d22, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d22, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35030 p hg
    simpa only [d8108, d22, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35032 (p : Pattern) (guard : d8113 p = 1) : d28 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d28, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34854 p hg
    simpa only [d8113, d28, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d28, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34704 p hg
    simpa only [d8113, d28, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35033 (p : Pattern) (guard : d8114 p = 1) : d29 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d29, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35031 p hg
    simpa only [d8114, d29, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d29, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35032 p hg
    simpa only [d8114, d29, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35034 (p : Pattern) (guard : d8101 p = 1) : d33 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d33, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34812 p hg
    simpa only [d8101, d33, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d33, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34589 p hg
    simpa only [d8101, d33, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35035 (p : Pattern) (guard : d8107 p = 1) : d38 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d38, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35034 p hg
    simpa only [d8107, d38, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d38, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d8107, d38, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35036 (p : Pattern) (guard : d8113 p = 1) : d45 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d45, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35035 p hg
    simpa only [d8113, d45, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d45, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34867 p hg
    simpa only [d8113, d45, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35037 (p : Pattern) (guard : d8119 p = 1) : d51 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d51, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35036 p hg
    simpa only [d8119, d51, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d51, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34872 p hg
    simpa only [d8119, d51, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35038 (p : Pattern) (guard : d8120 p = 1) : d52 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d52, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35033 p hg
    simpa only [d8120, d52, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d52, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35037 p hg
    simpa only [d8120, d52, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35039 (p : Pattern) (guard : d8085 p = 1) : d14 p ≤ (0 : Int) + d349 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34372 p hg
    simpa only [d8085, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34339 p hg
    simpa only [d8085, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35040 (p : Pattern) (guard : d8090 p = 1) : d14 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35039 p hg
    simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34417 p hg
    simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35041 (p : Pattern) (guard : d8095 p = 1) : d14 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35040 p hg
    simpa only [d8095, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34637 p hg
    simpa only [d8095, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35042 (p : Pattern) (guard : d8101 p = 1) : d16 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d16, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35041 p hg
    simpa only [d8101, d16, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d16, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34696 p hg
    simpa only [d8101, d16, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35043 (p : Pattern) (guard : d8084 p = 1) : d31 p ≤ (0 : Int) + d315 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d31, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34656 p hg
    simpa only [d8084, d31, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d31, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34407 p hg
    simpa only [d8084, d31, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35044 (p : Pattern) (guard : d8089 p = 1) : d31 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35043 p hg
    simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34472 p hg
    simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35045 (p : Pattern) (guard : d8094 p = 1) : d31 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35044 p hg
    simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34525 p hg
    simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35046 (p : Pattern) (guard : d8100 p = 1) : d31 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35045 p hg
    simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34678 p hg
    simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35047 (p : Pattern) (guard : d8106 p = 1) : d53 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d53, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35046 p hg
    simpa only [d8106, d53, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d53, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34721 p hg
    simpa only [d8106, d53, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35048 (p : Pattern) (guard : d8107 p = 1) : d54 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d54, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35042 p hg
    simpa only [d8107, d54, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d54, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35047 p hg
    simpa only [d8107, d54, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35049 (p : Pattern) (guard : d8084 p = 1) : d18 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d18, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34663 p hg
    simpa only [d8084, d18, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d18, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34358 p hg
    simpa only [d8084, d18, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35050 (p : Pattern) (guard : d8089 p = 1) : d18 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35049 p hg
    simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34363 p hg
    simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35051 (p : Pattern) (guard : d8094 p = 1) : d18 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35050 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34440 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35052 (p : Pattern) (guard : d8100 p = 1) : d18 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35051 p hg
    simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34642 p hg
    simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35053 (p : Pattern) (guard : d8106 p = 1) : d20 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d20, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35052 p hg
    simpa only [d8106, d20, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d20, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34700 p hg
    simpa only [d8106, d20, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35054 (p : Pattern) (guard : d8112 p = 1) : d55 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d55, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35053 p hg
    simpa only [d8112, d55, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d55, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34724 p hg
    simpa only [d8112, d55, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35055 (p : Pattern) (guard : d8113 p = 1) : d56 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d56, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35048 p hg
    simpa only [d8113, d56, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d56, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35054 p hg
    simpa only [d8113, d56, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35056 (p : Pattern) (guard : d8112 p = 1) : d61 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d61, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34890 p hg
    simpa only [d8112, d61, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d61, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34727 p hg
    simpa only [d8112, d61, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35057 (p : Pattern) (guard : d8118 p = 1) : d64 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d64, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35056 p hg
    simpa only [d8118, d64, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d64, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34730 p hg
    simpa only [d8118, d64, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35058 (p : Pattern) (guard : d8119 p = 1) : d65 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d65, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35055 p hg
    simpa only [d8119, d65, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d65, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35057 p hg
    simpa only [d8119, d65, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35059 (p : Pattern) (guard : d8106 p = 1) : d37 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d37, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34926 p hg
    simpa only [d8106, d37, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d37, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34711 p hg
    simpa only [d8106, d37, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35060 (p : Pattern) (guard : d8112 p = 1) : d67 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d67, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35059 p hg
    simpa only [d8112, d67, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d67, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34897 p hg
    simpa only [d8112, d67, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35061 (p : Pattern) (guard : d8118 p = 1) : d69 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d69, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35060 p hg
    simpa only [d8118, d69, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d69, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34900 p hg
    simpa only [d8118, d69, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35062 (p : Pattern) (guard : d8124 p = 1) : d75 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d75, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35061 p hg
    simpa only [d8124, d75, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d75, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34904 p hg
    simpa only [d8124, d75, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35063 (p : Pattern) (guard : d8125 p = 1) : d76 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d76, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35058 p hg
    simpa only [d8125, d76, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d76, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35062 p hg
    simpa only [d8125, d76, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35064 (p : Pattern) (guard : d8126 p = 1) : d77 p ≤ (0 : Int) + d419 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d77, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35038 p hg
    simpa only [d8126, d77, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d77, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35063 p hg
    simpa only [d8126, d77, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35065 (p : Pattern) (guard : d8107 p = 1) : d16 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34830 p hg
    simpa only [d8107, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34927 p hg
    simpa only [d8107, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35066 (p : Pattern) (guard : d8113 p = 1) : d22 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d22, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35065 p hg
    simpa only [d8113, d22, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d22, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34912 p hg
    simpa only [d8113, d22, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35067 (p : Pattern) (guard : d8119 p = 1) : d29 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d29, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35066 p hg
    simpa only [d8119, d29, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d29, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34915 p hg
    simpa only [d8119, d29, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35068 (p : Pattern) (guard : d8125 p = 1) : d82 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d82, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35067 p hg
    simpa only [d8125, d82, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d82, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34921 p hg
    simpa only [d8125, d82, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35069 (p : Pattern) (guard : d8084 p = 1) : d14 p ≤ (0 : Int) + d329 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d14, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33816 p hg
    simpa only [d8084, d14, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d14, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34338 p hg
    simpa only [d8084, d14, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35070 (p : Pattern) (guard : d8089 p = 1) : d14 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35069 p hg
    simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34416 p hg
    simpa only [d8089, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35071 (p : Pattern) (guard : d8094 p = 1) : d14 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35070 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34636 p hg
    simpa only [d8094, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35072 (p : Pattern) (guard : d8100 p = 1) : d14 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35071 p hg
    simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d8100, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35073 (p : Pattern) (guard : d8106 p = 1) : d16 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d16, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35072 p hg
    simpa only [d8106, d16, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d16, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34908 p hg
    simpa only [d8106, d16, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35074 (p : Pattern) (guard : d8112 p = 1) : d54 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d54, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35073 p hg
    simpa only [d8112, d54, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d54, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34928 p hg
    simpa only [d8112, d54, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35075 (p : Pattern) (guard : d8118 p = 1) : d56 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d56, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35074 p hg
    simpa only [d8118, d56, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d56, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34931 p hg
    simpa only [d8118, d56, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35076 (p : Pattern) (guard : d8124 p = 1) : d65 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d65, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35075 p hg
    simpa only [d8124, d65, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d65, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34934 p hg
    simpa only [d8124, d65, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35077 (p : Pattern) (guard : d8130 p = 1) : d86 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d86, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35076 p hg
    simpa only [d8130, d86, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d86, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34938 p hg
    simpa only [d8130, d86, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35078 (p : Pattern) (guard : d8131 p = 1) : d87 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d87, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35068 p hg
    simpa only [d8131, d87, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d87, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35077 p hg
    simpa only [d8131, d87, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35079 (p : Pattern) (guard : d8132 p = 1) : d88 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d88, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35064 p hg
    simpa only [d8132, d88, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d88, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35078 p hg
    simpa only [d8132, d88, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35080 (p : Pattern) (guard : d8137 p = 1) : d425 p ≤ (0 : Int) + d425 p := by
  omega
theorem compare35081 (p : Pattern) (guard : d8138 p = 1) : d500 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d500, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35079 p hg
    simpa only [d8138, d500, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d500, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35080 p hg
    simpa only [d8138, d500, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35082 (p : Pattern) (guard : d8139 p = 1) : d501 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8133 p = 1 := by simpa only [d8139, d501, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35028 p hg
    simpa only [d8139, d501, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8138 p = 1 := by simpa only [d8139, d501, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35081 p hg
    simpa only [d8139, d501, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35083 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (0 : Int) + d428 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14646 p hg
    simpa only [d428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1583 p hg
    simpa only [d428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35084 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (0 : Int) + d9 p := by
  change (1 : Int) ≤ (0 : Int) + 9
  decide
theorem compare35085 (p : Pattern) (guard : d1 p = 1) : d102 p ≤ (0 : Int) + d23 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d102, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35084 p hg
    simpa only [d102, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d102, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d102, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35086 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (0 : Int) + d429 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d103, d429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35083 p hg
    simpa only [d103, d429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d103, d429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35085 p hg
    simpa only [d103, d429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35087 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (0 : Int) + d23 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35084 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1561 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35088 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d103, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35087 p hg
    simpa only [d103, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d103, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1562 p hg
    simpa only [d103, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35089 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (0 : Int) + d430 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35086 p hg
    simpa only [d430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35088 p hg
    simpa only [d430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35090 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (0 : Int) + d8 p := by
  change (1 : Int) ≤ (0 : Int) + 8
  decide
theorem compare35091 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (0 : Int) + d190 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35090 p hg
    simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1561 p hg
    simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35092 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (0 : Int) + d315 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d103, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35091 p hg
    simpa only [d103, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d103, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1562 p hg
    simpa only [d103, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35093 (p : Pattern) (guard : d5843 p = 1) : d102 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1561 p hg
    simpa only [d5843, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5843, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35094 (p : Pattern) (guard : d8084 p = 1) : d103 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1561 p hg
    simpa only [d8084, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35093 p hg
    simpa only [d8084, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35095 (p : Pattern) (guard : d8085 p = 1) : d103 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35092 p hg
    simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35094 p hg
    simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35096 (p : Pattern) (guard : d8086 p = 1) : d103 p ≤ (0 : Int) + d431 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35089 p hg
    simpa only [d8086, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35095 p hg
    simpa only [d8086, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35097 (p : Pattern) (guard : d8085 p = 1) : d103 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35088 p hg
    simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35094 p hg
    simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35098 (p : Pattern) (guard : d5843 p = 1) : d1 p ≤ (0 : Int) + d12 p := by
  change (1 : Int) ≤ (0 : Int) + 12
  decide
theorem compare35099 (p : Pattern) (guard : d5847 p = 1) : d103 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35098 p hg
    simpa only [d5847, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17788 p hg
    simpa only [d5847, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35100 (p : Pattern) (guard : d8089 p = 1) : d103 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35094 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35099 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35101 (p : Pattern) (guard : d8090 p = 1) : d103 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35097 p hg
    simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35100 p hg
    simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35102 (p : Pattern) (guard : d8091 p = 1) : d103 p ≤ (0 : Int) + d432 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35096 p hg
    simpa only [d8091, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35101 p hg
    simpa only [d8091, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35103 (p : Pattern) (guard : d8090 p = 1) : d103 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35095 p hg
    simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35100 p hg
    simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35104 (p : Pattern) (guard : d8095 p = 1) : d104 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d104, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35103 p hg
    simpa only [d8095, d104, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d104, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d104, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35105 (p : Pattern) (guard : d8096 p = 1) : d105 p ≤ (0 : Int) + d433 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d105, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35102 p hg
    simpa only [d8096, d105, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d105, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35104 p hg
    simpa only [d8096, d105, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35106 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (0 : Int) + d4 p := by
  change (1 : Int) ≤ (0 : Int) + 4
  decide
theorem compare35107 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (0 : Int) + d17 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35106 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1561 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35108 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (0 : Int) + d339 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d103, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35107 p hg
    simpa only [d103, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d103, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1562 p hg
    simpa only [d103, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35109 (p : Pattern) (guard : d8085 p = 1) : d103 p ≤ (0 : Int) + d340 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35108 p hg
    simpa only [d8085, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35094 p hg
    simpa only [d8085, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35110 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (0 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4578 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1561 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35111 (p : Pattern) (guard : d8084 p = 1) : d103 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d103, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35110 p hg
    simpa only [d8084, d103, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d103, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35093 p hg
    simpa only [d8084, d103, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35112 (p : Pattern) (guard : d8089 p = 1) : d103 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35111 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35099 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35113 (p : Pattern) (guard : d8090 p = 1) : d103 p ≤ (0 : Int) + d341 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35109 p hg
    simpa only [d8090, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35112 p hg
    simpa only [d8090, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35114 (p : Pattern) (guard : d5854 p = 1) : d103 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35099 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11610 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35115 (p : Pattern) (guard : d8094 p = 1) : d103 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35100 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35114 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35116 (p : Pattern) (guard : d8095 p = 1) : d103 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35113 p hg
    simpa only [d8095, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35115 p hg
    simpa only [d8095, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35117 (p : Pattern) (guard : d8094 p = 1) : d103 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35112 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35114 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35118 (p : Pattern) (guard : d8100 p = 1) : d104 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d104, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35117 p hg
    simpa only [d8100, d104, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d104, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d104, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35119 (p : Pattern) (guard : d8101 p = 1) : d105 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d105, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35116 p hg
    simpa only [d8101, d105, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d105, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35118 p hg
    simpa only [d8101, d105, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35120 (p : Pattern) (guard : d8102 p = 1) : d105 p ≤ (0 : Int) + d434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35105 p hg
    simpa only [d8102, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35119 p hg
    simpa only [d8102, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35121 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (0 : Int) + d106 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1253 p hg
    simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1561 p hg
    simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35122 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (0 : Int) + d348 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d103, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35121 p hg
    simpa only [d103, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d103, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1562 p hg
    simpa only [d103, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35123 (p : Pattern) (guard : d8085 p = 1) : d103 p ≤ (0 : Int) + d349 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35122 p hg
    simpa only [d8085, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35094 p hg
    simpa only [d8085, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35124 (p : Pattern) (guard : d8090 p = 1) : d103 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35123 p hg
    simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35100 p hg
    simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35125 (p : Pattern) (guard : d8095 p = 1) : d103 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35124 p hg
    simpa only [d8095, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35115 p hg
    simpa only [d8095, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35126 (p : Pattern) (guard : d8100 p = 1) : d104 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35115 p hg
    simpa only [d8100, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35127 (p : Pattern) (guard : d8101 p = 1) : d105 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d105, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35125 p hg
    simpa only [d8101, d105, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d105, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35126 p hg
    simpa only [d8101, d105, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35128 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (0 : Int) + d8 p := by
  change (5 : Int) ≤ (0 : Int) + 8
  decide
theorem compare35129 (p : Pattern) (guard : d1 p = 1) : d5 p ≤ (0 : Int) + d190 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35128 p hg
    simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1319 p hg
    simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35130 (p : Pattern) (guard : d5843 p = 1) : d106 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1319 p hg
    simpa only [d5843, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5843, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35131 (p : Pattern) (guard : d8084 p = 1) : d107 p ≤ (0 : Int) + d315 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d107, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35129 p hg
    simpa only [d8084, d107, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d107, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35130 p hg
    simpa only [d8084, d107, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35132 (p : Pattern) (guard : d5843 p = 1) : d5 p ≤ (0 : Int) + d12 p := by
  change (5 : Int) ≤ (0 : Int) + 12
  decide
theorem compare35133 (p : Pattern) (guard : d5847 p = 1) : d107 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35132 p hg
    simpa only [d5847, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17797 p hg
    simpa only [d5847, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35134 (p : Pattern) (guard : d8089 p = 1) : d107 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35131 p hg
    simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35133 p hg
    simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35135 (p : Pattern) (guard : d5854 p = 1) : d107 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35133 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11614 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35136 (p : Pattern) (guard : d8094 p = 1) : d107 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35134 p hg
    simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35135 p hg
    simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35137 (p : Pattern) (guard : d8099 p = 1) : d107 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35135 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11614 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35138 (p : Pattern) (guard : d8100 p = 1) : d107 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35136 p hg
    simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35137 p hg
    simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare35139 (p : Pattern) (guard : d8105 p = 1) : d108 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35137 p hg
    simpa only [d8105, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
