/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons271
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare38080 (p : Pattern) (guard : d8141 p = 1) : d4019 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8135 p = 1 := by simpa only [d8141, d4019, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38078 p hg
    simpa only [d8141, d4019, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8141, d4019, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38079 p hg
    simpa only [d8141, d4019, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38081 (p : Pattern) (guard : d8142 p = 1) : d4020 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d4020, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38072 p hg
    simpa only [d8142, d4020, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d4020, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38080 p hg
    simpa only [d8142, d4020, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38082 (p : Pattern) (guard : d0 p = 1) : d3830 p ≤ (0 : Int) + d373 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare38083 (p : Pattern) (guard : d8117 p = 1) : d4004 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d4004, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37993 p hg
    simpa only [d8117, d4004, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d4004, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38082 p hg
    simpa only [d8117, d4004, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38084 (p : Pattern) (guard : d0 p = 1) : d4021 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare38085 (p : Pattern) (guard : d8123 p = 1) : d4022 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d4022, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38083 p hg
    simpa only [d8123, d4022, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d4022, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38084 p hg
    simpa only [d8123, d4022, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38086 (p : Pattern) (guard : d0 p = 1) : d4024 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare38087 (p : Pattern) (guard : d8129 p = 1) : d4025 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d4025, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38085 p hg
    simpa only [d8129, d4025, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d4025, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38086 p hg
    simpa only [d8129, d4025, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38088 (p : Pattern) (guard : d0 p = 1) : d4028 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare38089 (p : Pattern) (guard : d8135 p = 1) : d4029 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d4029, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38087 p hg
    simpa only [d8135, d4029, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d4029, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38088 p hg
    simpa only [d8135, d4029, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38090 (p : Pattern) (guard : d0 p = 1) : d4018 p ≤ (0 : Int) + d421 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare38091 (p : Pattern) (guard : d8141 p = 1) : d4030 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8135 p = 1 := by simpa only [d8141, d4030, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38089 p hg
    simpa only [d8141, d4030, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8141, d4030, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38090 p hg
    simpa only [d8141, d4030, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38092 (p : Pattern) (guard : d8147 p = 1) : d4031 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8141 p = 1 := by simpa only [d8147, d4031, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38091 p hg
    simpa only [d8147, d4031, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8147, d4031, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8147, d4031, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38093 (p : Pattern) (guard : d8148 p = 1) : d4032 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8142 p = 1 := by simpa only [d8148, d4032, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38081 p hg
    simpa only [d8148, d4032, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8147 p = 1 := by simpa only [d8148, d4032, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38092 p hg
    simpa only [d8148, d4032, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38094 (p : Pattern) (guard : d8149 p = 1) : d4033 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8143 p = 1 := by simpa only [d8149, d4033, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38033 p hg
    simpa only [d8149, d4033, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8148 p = 1 := by simpa only [d8149, d4033, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38093 p hg
    simpa only [d8149, d4033, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38095 (p : Pattern) (guard : d8150 p = 1) : d4034 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8144 p = 1 := by simpa only [d8150, d4034, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37885 p hg
    simpa only [d8150, d4034, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8149 p = 1 := by simpa only [d8150, d4034, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38094 p hg
    simpa only [d8150, d4034, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38096 (p : Pattern) (guard : d8151 p = 1) : d4035 p ≤ (0 : Int) + d447 p := by
  cases selected : p 49 with
  | false =>
    have hg : d8145 p = 1 := by simpa only [d8151, d4035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37673 p hg
    simpa only [d8151, d4035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8150 p = 1 := by simpa only [d8151, d4035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38095 p hg
    simpa only [d8151, d4035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38097 (p : Pattern) (guard : d8152 p = 1) : d4036 p ≤ (0 : Int) + d447 p := by
  cases selected : p 48 with
  | false =>
    have hg : d8146 p = 1 := by simpa only [d8152, d4036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37402 p hg
    simpa only [d8152, d4036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8151 p = 1 := by simpa only [d8152, d4036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38096 p hg
    simpa only [d8152, d4036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38098 (p : Pattern) (guard : d8115 p = 1) : d392 p ≤ (0 : Int) + d392 p := by
  omega
theorem compare38099 (p : Pattern) (guard : d8116 p = 1) : d653 p ≤ (0 : Int) + d393 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8110 p = 1 := by simpa only [d8116, d653, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34459 p hg
    simpa only [d8116, d653, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8115 p = 1 := by simpa only [d8116, d653, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38098 p hg
    simpa only [d8116, d653, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38100 (p : Pattern) (guard : d8120 p = 1) : d399 p ≤ (0 : Int) + d399 p := by
  omega
theorem compare38101 (p : Pattern) (guard : d8121 p = 1) : d654 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d654, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34579 p hg
    simpa only [d8121, d654, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d654, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38100 p hg
    simpa only [d8121, d654, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38102 (p : Pattern) (guard : d8122 p = 1) : d655 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8116 p = 1 := by simpa only [d8122, d655, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38099 p hg
    simpa only [d8122, d655, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8121 p = 1 := by simpa only [d8122, d655, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38101 p hg
    simpa only [d8122, d655, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38103 (p : Pattern) (guard : d8097 p = 1) : d16 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34354 p hg
    simpa only [d8097, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34582 p hg
    simpa only [d8097, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38104 (p : Pattern) (guard : d8103 p = 1) : d22 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d22, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38103 p hg
    simpa only [d8103, d22, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d22, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34632 p hg
    simpa only [d8103, d22, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38105 (p : Pattern) (guard : d8108 p = 1) : d28 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d28, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34555 p hg
    simpa only [d8108, d28, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d28, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34560 p hg
    simpa only [d8108, d28, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38106 (p : Pattern) (guard : d8109 p = 1) : d29 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d29, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38104 p hg
    simpa only [d8109, d29, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d29, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38105 p hg
    simpa only [d8109, d29, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38107 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34585 p hg
    simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1508 p hg
    simpa only [d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38108 (p : Pattern) (guard : d8086 p = 1) : d31 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38107 p hg
    simpa only [d8086, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34409 p hg
    simpa only [d8086, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38109 (p : Pattern) (guard : d8091 p = 1) : d31 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38108 p hg
    simpa only [d8091, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34474 p hg
    simpa only [d8091, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38110 (p : Pattern) (guard : d8096 p = 1) : d53 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d53, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38109 p hg
    simpa only [d8096, d53, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d53, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34476 p hg
    simpa only [d8096, d53, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38111 (p : Pattern) (guard : d8102 p = 1) : d79 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d79, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38110 p hg
    simpa only [d8102, d79, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d79, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34571 p hg
    simpa only [d8102, d79, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38112 (p : Pattern) (guard : d8108 p = 1) : d80 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d80, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38111 p hg
    simpa only [d8108, d80, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d80, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34575 p hg
    simpa only [d8108, d80, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38113 (p : Pattern) (guard : d8114 p = 1) : d81 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d81, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38112 p hg
    simpa only [d8114, d81, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d81, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34577 p hg
    simpa only [d8114, d81, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38114 (p : Pattern) (guard : d8115 p = 1) : d82 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d82, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38106 p hg
    simpa only [d8115, d82, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d82, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38113 p hg
    simpa only [d8115, d82, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38115 (p : Pattern) (guard : d8120 p = 1) : d407 p ≤ (0 : Int) + d407 p := by
  omega
theorem compare38116 (p : Pattern) (guard : d8121 p = 1) : d656 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d656, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38114 p hg
    simpa only [d8121, d656, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d656, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38115 p hg
    simpa only [d8121, d656, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38117 (p : Pattern) (guard : d8102 p = 1) : d89 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d89, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34398 p hg
    simpa only [d8102, d89, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d89, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34574 p hg
    simpa only [d8102, d89, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38118 (p : Pattern) (guard : d8108 p = 1) : d90 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d90, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38117 p hg
    simpa only [d8108, d90, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d90, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34575 p hg
    simpa only [d8108, d90, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38119 (p : Pattern) (guard : d8113 p = 1) : d91 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34575 p hg
    simpa only [d8113, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34611 p hg
    simpa only [d8113, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38120 (p : Pattern) (guard : d8114 p = 1) : d92 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d92, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38118 p hg
    simpa only [d8114, d92, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d92, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38119 p hg
    simpa only [d8114, d92, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38121 (p : Pattern) (guard : d8119 p = 1) : d93 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38119 p hg
    simpa only [d8119, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38122 (p : Pattern) (guard : d8120 p = 1) : d94 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d94, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38120 p hg
    simpa only [d8120, d94, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d94, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38121 p hg
    simpa only [d8120, d94, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38123 (p : Pattern) (guard : d8125 p = 1) : d411 p ≤ (0 : Int) + d411 p := by
  omega
theorem compare38124 (p : Pattern) (guard : d8126 p = 1) : d657 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d657, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38122 p hg
    simpa only [d8126, d657, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d657, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38123 p hg
    simpa only [d8126, d657, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38125 (p : Pattern) (guard : d8127 p = 1) : d658 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d658, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38116 p hg
    simpa only [d8127, d658, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d658, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38124 p hg
    simpa only [d8127, d658, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38126 (p : Pattern) (guard : d8128 p = 1) : d659 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8122 p = 1 := by simpa only [d8128, d659, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38102 p hg
    simpa only [d8128, d659, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8127 p = 1 := by simpa only [d8128, d659, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38125 p hg
    simpa only [d8128, d659, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38127 (p : Pattern) (guard : d8120 p = 1) : d397 p ≤ (0 : Int) + d397 p := by
  omega
theorem compare38128 (p : Pattern) (guard : d8121 p = 1) : d660 p ≤ (0 : Int) + d419 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d660, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34652 p hg
    simpa only [d8121, d660, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d660, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38127 p hg
    simpa only [d8121, d660, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38129 (p : Pattern) (guard : d8125 p = 1) : d421 p ≤ (0 : Int) + d421 p := by
  omega
theorem compare38130 (p : Pattern) (guard : d8126 p = 1) : d661 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d661, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34716 p hg
    simpa only [d8126, d661, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d661, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38129 p hg
    simpa only [d8126, d661, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38131 (p : Pattern) (guard : d8127 p = 1) : d662 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d662, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38128 p hg
    simpa only [d8127, d662, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d662, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38130 p hg
    simpa only [d8127, d662, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38132 (p : Pattern) (guard : d8102 p = 1) : d16 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34582 p hg
    simpa only [d8102, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34720 p hg
    simpa only [d8102, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38133 (p : Pattern) (guard : d8108 p = 1) : d22 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d22, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38132 p hg
    simpa only [d8108, d22, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d22, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34823 p hg
    simpa only [d8108, d22, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38134 (p : Pattern) (guard : d8114 p = 1) : d29 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d29, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38133 p hg
    simpa only [d8114, d29, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d29, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34705 p hg
    simpa only [d8114, d29, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38135 (p : Pattern) (guard : d8120 p = 1) : d82 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d82, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38134 p hg
    simpa only [d8120, d82, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d82, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34715 p hg
    simpa only [d8120, d82, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38136 (p : Pattern) (guard : d8125 p = 1) : d410 p ≤ (0 : Int) + d410 p := by
  omega
theorem compare38137 (p : Pattern) (guard : d8126 p = 1) : d663 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d663, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38135 p hg
    simpa only [d8126, d663, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d663, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38136 p hg
    simpa only [d8126, d663, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38138 (p : Pattern) (guard : d8132 p = 1) : d664 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d664, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38137 p hg
    simpa only [d8132, d664, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d664, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36499 p hg
    simpa only [d8132, d664, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38139 (p : Pattern) (guard : d8133 p = 1) : d665 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d665, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38131 p hg
    simpa only [d8133, d665, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d665, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38138 p hg
    simpa only [d8133, d665, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38140 (p : Pattern) (guard : d8134 p = 1) : d666 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8128 p = 1 := by simpa only [d8134, d666, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38126 p hg
    simpa only [d8134, d666, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8133 p = 1 := by simpa only [d8134, d666, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38139 p hg
    simpa only [d8134, d666, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38141 (p : Pattern) (guard : d8120 p = 1) : d418 p ≤ (0 : Int) + d418 p := by
  omega
theorem compare38142 (p : Pattern) (guard : d8121 p = 1) : d667 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d667, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34778 p hg
    simpa only [d8121, d667, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d667, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38141 p hg
    simpa only [d8121, d667, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38143 (p : Pattern) (guard : d8125 p = 1) : d420 p ≤ (0 : Int) + d420 p := by
  omega
theorem compare38144 (p : Pattern) (guard : d8126 p = 1) : d668 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d668, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34826 p hg
    simpa only [d8126, d668, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d668, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38143 p hg
    simpa only [d8126, d668, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38145 (p : Pattern) (guard : d8127 p = 1) : d669 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d669, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38142 p hg
    simpa only [d8127, d669, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d669, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38144 p hg
    simpa only [d8127, d669, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38146 (p : Pattern) (guard : d8125 p = 1) : d399 p ≤ (0 : Int) + d399 p := by
  omega
theorem compare38147 (p : Pattern) (guard : d8126 p = 1) : d654 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d654, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35014 p hg
    simpa only [d8126, d654, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d654, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38146 p hg
    simpa only [d8126, d654, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38148 (p : Pattern) (guard : d8107 p = 1) : d89 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d89, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34767 p hg
    simpa only [d8107, d89, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d89, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34606 p hg
    simpa only [d8107, d89, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38149 (p : Pattern) (guard : d8113 p = 1) : d90 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d90, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38148 p hg
    simpa only [d8113, d90, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d90, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34607 p hg
    simpa only [d8113, d90, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38150 (p : Pattern) (guard : d8118 p = 1) : d91 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34607 p hg
    simpa only [d8118, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38151 (p : Pattern) (guard : d8119 p = 1) : d92 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d92, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38149 p hg
    simpa only [d8119, d92, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d92, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38150 p hg
    simpa only [d8119, d92, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38152 (p : Pattern) (guard : d8124 p = 1) : d93 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38150 p hg
    simpa only [d8124, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38153 (p : Pattern) (guard : d8125 p = 1) : d94 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d94, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38151 p hg
    simpa only [d8125, d94, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d94, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38152 p hg
    simpa only [d8125, d94, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38154 (p : Pattern) (guard : d8130 p = 1) : d12 p ≤ (0 : Int) + d12 p := by
  omega
theorem compare38155 (p : Pattern) (guard : d8131 p = 1) : d670 p ≤ (0 : Int) + d441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d670, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38153 p hg
    simpa only [d8131, d670, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d670, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38154 p hg
    simpa only [d8131, d670, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38156 (p : Pattern) (guard : d8132 p = 1) : d671 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d671, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38147 p hg
    simpa only [d8132, d671, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d671, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38155 p hg
    simpa only [d8132, d671, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38157 (p : Pattern) (guard : d8133 p = 1) : d672 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d672, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38145 p hg
    simpa only [d8133, d672, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d672, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38156 p hg
    simpa only [d8133, d672, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38158 (p : Pattern) (guard : d8125 p = 1) : d407 p ≤ (0 : Int) + d407 p := by
  omega
theorem compare38159 (p : Pattern) (guard : d8126 p = 1) : d673 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d673, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34874 p hg
    simpa only [d8126, d673, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d673, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38158 p hg
    simpa only [d8126, d673, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38160 (p : Pattern) (guard : d8130 p = 1) : d411 p ≤ (0 : Int) + d411 p := by
  omega
theorem compare38161 (p : Pattern) (guard : d8131 p = 1) : d674 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d674, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34922 p hg
    simpa only [d8131, d674, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d674, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38160 p hg
    simpa only [d8131, d674, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38162 (p : Pattern) (guard : d8132 p = 1) : d675 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d675, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38159 p hg
    simpa only [d8132, d675, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d675, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38161 p hg
    simpa only [d8132, d675, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38163 (p : Pattern) (guard : d8130 p = 1) : d421 p ≤ (0 : Int) + d421 p := by
  omega
theorem compare38164 (p : Pattern) (guard : d8131 p = 1) : d661 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d661, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35068 p hg
    simpa only [d8131, d661, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d661, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38163 p hg
    simpa only [d8131, d661, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38165 (p : Pattern) (guard : d8137 p = 1) : d676 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d676, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38164 p hg
    simpa only [d8137, d676, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d676, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36809 p hg
    simpa only [d8137, d676, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38166 (p : Pattern) (guard : d8138 p = 1) : d677 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d677, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38162 p hg
    simpa only [d8138, d677, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d677, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38165 p hg
    simpa only [d8138, d677, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38167 (p : Pattern) (guard : d8139 p = 1) : d678 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8133 p = 1 := by simpa only [d8139, d678, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38157 p hg
    simpa only [d8139, d678, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8138 p = 1 := by simpa only [d8139, d678, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38166 p hg
    simpa only [d8139, d678, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38168 (p : Pattern) (guard : d8140 p = 1) : d679 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8134 p = 1 := by simpa only [d8140, d679, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38140 p hg
    simpa only [d8140, d679, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8139 p = 1 := by simpa only [d8140, d679, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38167 p hg
    simpa only [d8140, d679, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38169 (p : Pattern) (guard : d8120 p = 1) : d392 p ≤ (0 : Int) + d392 p := by
  omega
theorem compare38170 (p : Pattern) (guard : d8121 p = 1) : d653 p ≤ (0 : Int) + d393 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d653, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34964 p hg
    simpa only [d8121, d653, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d653, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38169 p hg
    simpa only [d8121, d653, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38171 (p : Pattern) (guard : d8127 p = 1) : d655 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d655, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38170 p hg
    simpa only [d8127, d655, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d655, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38147 p hg
    simpa only [d8127, d655, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38172 (p : Pattern) (guard : d8107 p = 1) : d79 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d79, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34590 p hg
    simpa only [d8107, d79, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d79, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34712 p hg
    simpa only [d8107, d79, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38173 (p : Pattern) (guard : d8113 p = 1) : d80 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d80, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38172 p hg
    simpa only [d8113, d80, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d80, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34607 p hg
    simpa only [d8113, d80, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38174 (p : Pattern) (guard : d8119 p = 1) : d81 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d81, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38173 p hg
    simpa only [d8119, d81, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d81, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d81, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38175 (p : Pattern) (guard : d8120 p = 1) : d82 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d82, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34858 p hg
    simpa only [d8120, d82, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d82, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38174 p hg
    simpa only [d8120, d82, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38176 (p : Pattern) (guard : d8126 p = 1) : d656 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d656, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38175 p hg
    simpa only [d8126, d656, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d656, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38158 p hg
    simpa only [d8126, d656, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38177 (p : Pattern) (guard : d8107 p = 1) : d89 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d89, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34490 p hg
    simpa only [d8107, d89, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d89, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34606 p hg
    simpa only [d8107, d89, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38178 (p : Pattern) (guard : d8113 p = 1) : d90 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d90, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38177 p hg
    simpa only [d8113, d90, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d90, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34607 p hg
    simpa only [d8113, d90, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38179 (p : Pattern) (guard : d8119 p = 1) : d92 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d92, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38178 p hg
    simpa only [d8119, d92, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d92, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38150 p hg
    simpa only [d8119, d92, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38180 (p : Pattern) (guard : d8125 p = 1) : d94 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d94, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38179 p hg
    simpa only [d8125, d94, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d94, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38152 p hg
    simpa only [d8125, d94, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38181 (p : Pattern) (guard : d8131 p = 1) : d657 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d657, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38180 p hg
    simpa only [d8131, d657, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d657, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38160 p hg
    simpa only [d8131, d657, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38182 (p : Pattern) (guard : d8132 p = 1) : d658 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d658, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38176 p hg
    simpa only [d8132, d658, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d658, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38181 p hg
    simpa only [d8132, d658, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38183 (p : Pattern) (guard : d8133 p = 1) : d659 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d659, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38171 p hg
    simpa only [d8133, d659, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d659, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38182 p hg
    simpa only [d8133, d659, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38184 (p : Pattern) (guard : d8125 p = 1) : d397 p ≤ (0 : Int) + d397 p := by
  omega
theorem compare38185 (p : Pattern) (guard : d8126 p = 1) : d660 p ≤ (0 : Int) + d419 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d660, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35038 p hg
    simpa only [d8126, d660, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d660, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38184 p hg
    simpa only [d8126, d660, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38186 (p : Pattern) (guard : d8132 p = 1) : d662 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d662, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38185 p hg
    simpa only [d8132, d662, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d662, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38164 p hg
    simpa only [d8132, d662, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38187 (p : Pattern) (guard : d8107 p = 1) : d16 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34847 p hg
    simpa only [d8107, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35073 p hg
    simpa only [d8107, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38188 (p : Pattern) (guard : d8113 p = 1) : d22 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d22, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38187 p hg
    simpa only [d8113, d22, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d22, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35458 p hg
    simpa only [d8113, d22, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38189 (p : Pattern) (guard : d8119 p = 1) : d29 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d29, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38188 p hg
    simpa only [d8119, d29, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d29, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34915 p hg
    simpa only [d8119, d29, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38190 (p : Pattern) (guard : d8125 p = 1) : d82 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d82, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38189 p hg
    simpa only [d8125, d82, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d82, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34921 p hg
    simpa only [d8125, d82, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38191 (p : Pattern) (guard : d8130 p = 1) : d410 p ≤ (0 : Int) + d410 p := by
  omega
theorem compare38192 (p : Pattern) (guard : d8131 p = 1) : d663 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d663, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38190 p hg
    simpa only [d8131, d663, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d663, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38191 p hg
    simpa only [d8131, d663, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38193 (p : Pattern) (guard : d8137 p = 1) : d664 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d664, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38192 p hg
    simpa only [d8137, d664, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d664, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36809 p hg
    simpa only [d8137, d664, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38194 (p : Pattern) (guard : d8138 p = 1) : d665 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d665, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38186 p hg
    simpa only [d8138, d665, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d665, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38193 p hg
    simpa only [d8138, d665, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38195 (p : Pattern) (guard : d8139 p = 1) : d666 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8133 p = 1 := by simpa only [d8139, d666, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38183 p hg
    simpa only [d8139, d666, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8138 p = 1 := by simpa only [d8139, d666, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38194 p hg
    simpa only [d8139, d666, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38196 (p : Pattern) (guard : d8125 p = 1) : d418 p ≤ (0 : Int) + d418 p := by
  omega
theorem compare38197 (p : Pattern) (guard : d8126 p = 1) : d680 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d680, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35199 p hg
    simpa only [d8126, d680, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d680, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38196 p hg
    simpa only [d8126, d680, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38198 (p : Pattern) (guard : d8130 p = 1) : d420 p ≤ (0 : Int) + d420 p := by
  omega
theorem compare38199 (p : Pattern) (guard : d8131 p = 1) : d681 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d681, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35271 p hg
    simpa only [d8131, d681, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d681, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38198 p hg
    simpa only [d8131, d681, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38200 (p : Pattern) (guard : d8132 p = 1) : d682 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d682, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38197 p hg
    simpa only [d8132, d682, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d682, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38199 p hg
    simpa only [d8132, d682, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38201 (p : Pattern) (guard : d8107 p = 1) : d105 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35127 p hg
    simpa only [d8107, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35276 p hg
    simpa only [d8107, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38202 (p : Pattern) (guard : d8113 p = 1) : d111 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d111, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38201 p hg
    simpa only [d8113, d111, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d111, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35312 p hg
    simpa only [d8113, d111, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38203 (p : Pattern) (guard : d8118 p = 1) : d113 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d113, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35257 p hg
    simpa only [d8118, d113, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d113, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35261 p hg
    simpa only [d8118, d113, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38204 (p : Pattern) (guard : d8119 p = 1) : d114 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d114, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38202 p hg
    simpa only [d8119, d114, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d114, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38203 p hg
    simpa only [d8119, d114, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38205 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (0 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35277 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1571 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38206 (p : Pattern) (guard : d8084 p = 1) : d116 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d116, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38205 p hg
    simpa only [d8084, d116, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d116, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35165 p hg
    simpa only [d8084, d116, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38207 (p : Pattern) (guard : d8089 p = 1) : d116 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38206 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35168 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38208 (p : Pattern) (guard : d8094 p = 1) : d116 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38207 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35170 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38209 (p : Pattern) (guard : d8100 p = 1) : d116 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38208 p hg
    simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35212 p hg
    simpa only [d8100, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38210 (p : Pattern) (guard : d8106 p = 1) : d132 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d132, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38209 p hg
    simpa only [d8106, d132, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d132, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35214 p hg
    simpa only [d8106, d132, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38211 (p : Pattern) (guard : d8112 p = 1) : d149 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d149, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38210 p hg
    simpa only [d8112, d149, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d149, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35267 p hg
    simpa only [d8112, d149, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38212 (p : Pattern) (guard : d8118 p = 1) : d150 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d150, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38211 p hg
    simpa only [d8118, d150, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d150, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d150, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38213 (p : Pattern) (guard : d8124 p = 1) : d151 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d151, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38212 p hg
    simpa only [d8124, d151, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d151, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d151, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38214 (p : Pattern) (guard : d8125 p = 1) : d152 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d152, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38204 p hg
    simpa only [d8125, d152, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d152, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38213 p hg
    simpa only [d8125, d152, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38215 (p : Pattern) (guard : d8130 p = 1) : d399 p ≤ (0 : Int) + d399 p := by
  omega
theorem compare38216 (p : Pattern) (guard : d8131 p = 1) : d683 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d683, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38214 p hg
    simpa only [d8131, d683, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d683, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38215 p hg
    simpa only [d8131, d683, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38217 (p : Pattern) (guard : d8118 p = 1) : d159 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d159, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35157 p hg
    simpa only [d8118, d159, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d159, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d159, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38218 (p : Pattern) (guard : d8124 p = 1) : d160 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d160, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38217 p hg
    simpa only [d8124, d160, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d160, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d160, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38219 (p : Pattern) (guard : d8130 p = 1) : d161 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d161, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38218 p hg
    simpa only [d8130, d161, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d161, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36647 p hg
    simpa only [d8130, d161, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
