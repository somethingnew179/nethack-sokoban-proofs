/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons321
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare45080 (p : Pattern) (guard : d8113 p = 1) : d3290 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3290, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45079 p hg
    simpa only [d8113, d3290, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3290, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44708 p hg
    simpa only [d8113, d3290, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45081 (p : Pattern) (guard : d8119 p = 1) : d3296 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3296, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45080 p hg
    simpa only [d8119, d3296, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3296, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44716 p hg
    simpa only [d8119, d3296, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45082 (p : Pattern) (guard : d8120 p = 1) : d3297 p ≤ (0 : Int) + d392 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d3297, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45076 p hg
    simpa only [d8120, d3297, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d3297, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45081 p hg
    simpa only [d8120, d3297, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45083 (p : Pattern) (guard : d8121 p = 1) : d3298 p ≤ (0 : Int) + d393 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d3298, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45042 p hg
    simpa only [d8121, d3298, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d3298, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45082 p hg
    simpa only [d8121, d3298, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45084 (p : Pattern) (guard : d8127 p = 1) : d3314 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d3314, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45083 p hg
    simpa only [d8127, d3314, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d3314, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44902 p hg
    simpa only [d8127, d3314, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45085 (p : Pattern) (guard : d8107 p = 1) : d3302 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3302, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44585 p hg
    simpa only [d8107, d3302, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3302, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44736 p hg
    simpa only [d8107, d3302, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45086 (p : Pattern) (guard : d8113 p = 1) : d3303 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3303, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45085 p hg
    simpa only [d8113, d3303, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3303, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44601 p hg
    simpa only [d8113, d3303, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45087 (p : Pattern) (guard : d8119 p = 1) : d3304 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3304, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45086 p hg
    simpa only [d8119, d3304, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3304, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d3304, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45088 (p : Pattern) (guard : d8120 p = 1) : d3305 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d3305, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44917 p hg
    simpa only [d8120, d3305, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d3305, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45087 p hg
    simpa only [d8120, d3305, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45089 (p : Pattern) (guard : d8125 p = 1) : d3312 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3312, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44953 p hg
    simpa only [d8125, d3312, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3312, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44762 p hg
    simpa only [d8125, d3312, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45090 (p : Pattern) (guard : d8126 p = 1) : d3313 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d3313, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45088 p hg
    simpa only [d8126, d3313, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d3313, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45089 p hg
    simpa only [d8126, d3313, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45091 (p : Pattern) (guard : d8107 p = 1) : d3315 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3315, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44493 p hg
    simpa only [d8107, d3315, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3315, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44600 p hg
    simpa only [d8107, d3315, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45092 (p : Pattern) (guard : d8113 p = 1) : d3316 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3316, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45091 p hg
    simpa only [d8113, d3316, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3316, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44601 p hg
    simpa only [d8113, d3316, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45093 (p : Pattern) (guard : d8119 p = 1) : d3318 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3318, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45092 p hg
    simpa only [d8119, d3318, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3318, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44905 p hg
    simpa only [d8119, d3318, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45094 (p : Pattern) (guard : d8125 p = 1) : d3320 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3320, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45093 p hg
    simpa only [d8125, d3320, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3320, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44907 p hg
    simpa only [d8125, d3320, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45095 (p : Pattern) (guard : d8118 p = 1) : d3317 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3317, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45074 p hg
    simpa only [d8118, d3317, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3317, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d3317, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45096 (p : Pattern) (guard : d8124 p = 1) : d3319 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3319, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45095 p hg
    simpa only [d8124, d3319, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3319, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d3319, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45097 (p : Pattern) (guard : d8130 p = 1) : d3321 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3321, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45096 p hg
    simpa only [d8130, d3321, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3321, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36647 p hg
    simpa only [d8130, d3321, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45098 (p : Pattern) (guard : d8131 p = 1) : d3322 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d3322, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45094 p hg
    simpa only [d8131, d3322, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d3322, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45097 p hg
    simpa only [d8131, d3322, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45099 (p : Pattern) (guard : d8132 p = 1) : d3323 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d3323, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45090 p hg
    simpa only [d8132, d3323, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d3323, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45098 p hg
    simpa only [d8132, d3323, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45100 (p : Pattern) (guard : d8133 p = 1) : d3324 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d3324, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45084 p hg
    simpa only [d8133, d3324, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d3324, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45099 p hg
    simpa only [d8133, d3324, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45101 (p : Pattern) (guard : d8102 p = 1) : d3325 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3325, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44820 p hg
    simpa only [d8102, d3325, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3325, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44937 p hg
    simpa only [d8102, d3325, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45102 (p : Pattern) (guard : d8107 p = 1) : d3242 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3242, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44886 p hg
    simpa only [d8107, d3242, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3242, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44948 p hg
    simpa only [d8107, d3242, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45103 (p : Pattern) (guard : d8108 p = 1) : d3326 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3326, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45101 p hg
    simpa only [d8108, d3326, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3326, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45102 p hg
    simpa only [d8108, d3326, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45104 (p : Pattern) (guard : d8113 p = 1) : d3248 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3248, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44914 p hg
    simpa only [d8113, d3248, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3248, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44728 p hg
    simpa only [d8113, d3248, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45105 (p : Pattern) (guard : d8114 p = 1) : d3327 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d3327, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45103 p hg
    simpa only [d8114, d3327, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d3327, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45104 p hg
    simpa only [d8114, d3327, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45106 (p : Pattern) (guard : d8101 p = 1) : d3252 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3252, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44773 p hg
    simpa only [d8101, d3252, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3252, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44584 p hg
    simpa only [d8101, d3252, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45107 (p : Pattern) (guard : d8107 p = 1) : d3256 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3256, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45106 p hg
    simpa only [d8107, d3256, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3256, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44921 p hg
    simpa only [d8107, d3256, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45108 (p : Pattern) (guard : d8113 p = 1) : d3262 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3262, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45107 p hg
    simpa only [d8113, d3262, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3262, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44926 p hg
    simpa only [d8113, d3262, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45109 (p : Pattern) (guard : d8119 p = 1) : d3268 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3268, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45108 p hg
    simpa only [d8119, d3268, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3268, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44931 p hg
    simpa only [d8119, d3268, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45110 (p : Pattern) (guard : d8120 p = 1) : d3328 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d3328, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45105 p hg
    simpa only [d8120, d3328, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d3328, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45109 p hg
    simpa only [d8120, d3328, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45111 (p : Pattern) (guard : d8085 p = 1) : d3226 p ≤ (0 : Int) + d349 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44389 p hg
    simpa only [d8085, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44360 p hg
    simpa only [d8085, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45112 (p : Pattern) (guard : d8090 p = 1) : d3226 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45111 p hg
    simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44430 p hg
    simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45113 (p : Pattern) (guard : d8095 p = 1) : d3226 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45112 p hg
    simpa only [d8095, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44663 p hg
    simpa only [d8095, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45114 (p : Pattern) (guard : d8101 p = 1) : d3238 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3238, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45113 p hg
    simpa only [d8101, d3238, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3238, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44720 p hg
    simpa only [d8101, d3238, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45115 (p : Pattern) (guard : d8084 p = 1) : d3250 p ≤ (0 : Int) + d315 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3250, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34656 p hg
    simpa only [d8084, d3250, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3250, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3250, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45116 (p : Pattern) (guard : d8089 p = 1) : d3250 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45115 p hg
    simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44477 p hg
    simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45117 (p : Pattern) (guard : d8094 p = 1) : d3250 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45116 p hg
    simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44525 p hg
    simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45118 (p : Pattern) (guard : d8100 p = 1) : d3250 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45117 p hg
    simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44702 p hg
    simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45119 (p : Pattern) (guard : d8106 p = 1) : d3275 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3275, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45118 p hg
    simpa only [d8106, d3275, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3275, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44745 p hg
    simpa only [d8106, d3275, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45120 (p : Pattern) (guard : d8107 p = 1) : d3306 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3306, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45114 p hg
    simpa only [d8107, d3306, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3306, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45119 p hg
    simpa only [d8107, d3306, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45121 (p : Pattern) (guard : d8084 p = 1) : d3239 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3239, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34663 p hg
    simpa only [d8084, d3239, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3239, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3239, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45122 (p : Pattern) (guard : d8089 p = 1) : d3239 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45121 p hg
    simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44381 p hg
    simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45123 (p : Pattern) (guard : d8094 p = 1) : d3239 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45122 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44451 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45124 (p : Pattern) (guard : d8100 p = 1) : d3239 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45123 p hg
    simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44668 p hg
    simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45125 (p : Pattern) (guard : d8106 p = 1) : d3241 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3241, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45124 p hg
    simpa only [d8106, d3241, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3241, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44724 p hg
    simpa only [d8106, d3241, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45126 (p : Pattern) (guard : d8112 p = 1) : d3277 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3277, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45125 p hg
    simpa only [d8112, d3277, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3277, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44749 p hg
    simpa only [d8112, d3277, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45127 (p : Pattern) (guard : d8113 p = 1) : d3307 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3307, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45120 p hg
    simpa only [d8113, d3307, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3307, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45126 p hg
    simpa only [d8113, d3307, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45128 (p : Pattern) (guard : d8112 p = 1) : d3282 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3282, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44948 p hg
    simpa only [d8112, d3282, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3282, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44753 p hg
    simpa only [d8112, d3282, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45129 (p : Pattern) (guard : d8118 p = 1) : d3285 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3285, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45128 p hg
    simpa only [d8118, d3285, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3285, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44757 p hg
    simpa only [d8118, d3285, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45130 (p : Pattern) (guard : d8119 p = 1) : d3308 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3308, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45127 p hg
    simpa only [d8119, d3308, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3308, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45129 p hg
    simpa only [d8119, d3308, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45131 (p : Pattern) (guard : d8106 p = 1) : d3255 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3255, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44987 p hg
    simpa only [d8106, d3255, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3255, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44735 p hg
    simpa only [d8106, d3255, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45132 (p : Pattern) (guard : d8112 p = 1) : d3288 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3288, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45131 p hg
    simpa only [d8112, d3288, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3288, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44955 p hg
    simpa only [d8112, d3288, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45133 (p : Pattern) (guard : d8118 p = 1) : d3290 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3290, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45132 p hg
    simpa only [d8118, d3290, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3290, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44958 p hg
    simpa only [d8118, d3290, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45134 (p : Pattern) (guard : d8124 p = 1) : d3296 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3296, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45133 p hg
    simpa only [d8124, d3296, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3296, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44963 p hg
    simpa only [d8124, d3296, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45135 (p : Pattern) (guard : d8125 p = 1) : d3329 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3329, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45130 p hg
    simpa only [d8125, d3329, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3329, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45134 p hg
    simpa only [d8125, d3329, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45136 (p : Pattern) (guard : d8126 p = 1) : d3330 p ≤ (0 : Int) + d419 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d3330, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45110 p hg
    simpa only [d8126, d3330, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d3330, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45135 p hg
    simpa only [d8126, d3330, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45137 (p : Pattern) (guard : d8132 p = 1) : d3331 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d3331, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45136 p hg
    simpa only [d8132, d3331, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d3331, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45019 p hg
    simpa only [d8132, d3331, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45138 (p : Pattern) (guard : d8107 p = 1) : d3238 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44886 p hg
    simpa only [d8107, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45014 p hg
    simpa only [d8107, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45139 (p : Pattern) (guard : d8112 p = 1) : d3242 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3242, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44988 p hg
    simpa only [d8112, d3242, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3242, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44971 p hg
    simpa only [d8112, d3242, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45140 (p : Pattern) (guard : d8113 p = 1) : d3299 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3299, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45138 p hg
    simpa only [d8113, d3299, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3299, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45139 p hg
    simpa only [d8113, d3299, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45141 (p : Pattern) (guard : d8119 p = 1) : d3300 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d3300, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45140 p hg
    simpa only [d8119, d3300, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d3300, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44975 p hg
    simpa only [d8119, d3300, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45142 (p : Pattern) (guard : d8125 p = 1) : d3305 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d3305, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45141 p hg
    simpa only [d8125, d3305, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d3305, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44982 p hg
    simpa only [d8125, d3305, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45143 (p : Pattern) (guard : d8084 p = 1) : d3226 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3226, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33853 p hg
    simpa only [d8084, d3226, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3226, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3226, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45144 (p : Pattern) (guard : d8089 p = 1) : d3226 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45143 p hg
    simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44429 p hg
    simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45145 (p : Pattern) (guard : d8094 p = 1) : d3226 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45144 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44662 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45146 (p : Pattern) (guard : d8100 p = 1) : d3226 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45145 p hg
    simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44919 p hg
    simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45147 (p : Pattern) (guard : d8106 p = 1) : d3238 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3238, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45146 p hg
    simpa only [d8106, d3238, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3238, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44967 p hg
    simpa only [d8106, d3238, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45148 (p : Pattern) (guard : d8112 p = 1) : d3306 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3306, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45147 p hg
    simpa only [d8112, d3306, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3306, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44990 p hg
    simpa only [d8112, d3306, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45149 (p : Pattern) (guard : d8118 p = 1) : d3307 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d3307, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45148 p hg
    simpa only [d8118, d3307, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d3307, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44993 p hg
    simpa only [d8118, d3307, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45150 (p : Pattern) (guard : d8124 p = 1) : d3308 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d3308, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45149 p hg
    simpa only [d8124, d3308, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d3308, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare44998 p hg
    simpa only [d8124, d3308, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45151 (p : Pattern) (guard : d8130 p = 1) : d3312 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d3312, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45150 p hg
    simpa only [d8130, d3312, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d3312, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45002 p hg
    simpa only [d8130, d3312, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45152 (p : Pattern) (guard : d8131 p = 1) : d3313 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d3313, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45142 p hg
    simpa only [d8131, d3313, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d3313, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45151 p hg
    simpa only [d8131, d3313, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45153 (p : Pattern) (guard : d8137 p = 1) : d3332 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d3332, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45152 p hg
    simpa only [d8137, d3332, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d3332, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36809 p hg
    simpa only [d8137, d3332, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45154 (p : Pattern) (guard : d8138 p = 1) : d3333 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d3333, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45137 p hg
    simpa only [d8138, d3333, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d3333, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45153 p hg
    simpa only [d8138, d3333, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45155 (p : Pattern) (guard : d8139 p = 1) : d3334 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8133 p = 1 := by simpa only [d8139, d3334, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45100 p hg
    simpa only [d8139, d3334, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8138 p = 1 := by simpa only [d8139, d3334, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45154 p hg
    simpa only [d8139, d3334, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45156 (p : Pattern) (guard : d1 p = 1) : d3357 p ≤ (0 : Int) + d429 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3357, d429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35083 p hg
    simpa only [d3357, d429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3357, d429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35948 p hg
    simpa only [d3357, d429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45157 (p : Pattern) (guard : d1 p = 1) : d3358 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3358, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35087 p hg
    simpa only [d3358, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3358, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d3358, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45158 (p : Pattern) (guard : d1 p = 1) : d3359 p ≤ (0 : Int) + d430 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3359, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45156 p hg
    simpa only [d3359, d430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3359, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45157 p hg
    simpa only [d3359, d430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45159 (p : Pattern) (guard : d1 p = 1) : d3358 p ≤ (0 : Int) + d315 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3358, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35091 p hg
    simpa only [d3358, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3358, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d3358, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45160 (p : Pattern) (guard : d8084 p = 1) : d3358 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1561 p hg
    simpa only [d8084, d3358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45161 (p : Pattern) (guard : d8085 p = 1) : d3358 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45159 p hg
    simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45160 p hg
    simpa only [d8085, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45162 (p : Pattern) (guard : d8086 p = 1) : d3360 p ≤ (0 : Int) + d431 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d3360, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45158 p hg
    simpa only [d8086, d3360, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d3360, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45161 p hg
    simpa only [d8086, d3360, d431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45163 (p : Pattern) (guard : d8085 p = 1) : d3358 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45157 p hg
    simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45160 p hg
    simpa only [d8085, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45164 (p : Pattern) (guard : d5847 p = 1) : d3358 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35098 p hg
    simpa only [d5847, d3358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45165 (p : Pattern) (guard : d8089 p = 1) : d3358 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45160 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45164 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45166 (p : Pattern) (guard : d8090 p = 1) : d3358 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45163 p hg
    simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45165 p hg
    simpa only [d8090, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45167 (p : Pattern) (guard : d8091 p = 1) : d3361 p ≤ (0 : Int) + d432 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d3361, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45162 p hg
    simpa only [d8091, d3361, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d3361, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45166 p hg
    simpa only [d8091, d3361, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45168 (p : Pattern) (guard : d8090 p = 1) : d3358 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45161 p hg
    simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45165 p hg
    simpa only [d8090, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45169 (p : Pattern) (guard : d8095 p = 1) : d3362 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d3362, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45168 p hg
    simpa only [d8095, d3362, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d3362, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d3362, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45170 (p : Pattern) (guard : d8096 p = 1) : d3363 p ≤ (0 : Int) + d433 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d3363, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45167 p hg
    simpa only [d8096, d3363, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d3363, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45169 p hg
    simpa only [d8096, d3363, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45171 (p : Pattern) (guard : d1 p = 1) : d3358 p ≤ (0 : Int) + d339 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3358, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35107 p hg
    simpa only [d3358, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3358, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d3358, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45172 (p : Pattern) (guard : d8085 p = 1) : d3358 p ≤ (0 : Int) + d340 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45171 p hg
    simpa only [d8085, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45160 p hg
    simpa only [d8085, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45173 (p : Pattern) (guard : d8084 p = 1) : d3358 p ≤ (0 : Int) + d327 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3358, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35110 p hg
    simpa only [d8084, d3358, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3358, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3358, d327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45174 (p : Pattern) (guard : d8089 p = 1) : d3358 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45173 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45164 p hg
    simpa only [d8089, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45175 (p : Pattern) (guard : d8090 p = 1) : d3358 p ≤ (0 : Int) + d341 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45172 p hg
    simpa only [d8090, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45174 p hg
    simpa only [d8090, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45176 (p : Pattern) (guard : d5854 p = 1) : d3358 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45164 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26774 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45177 (p : Pattern) (guard : d8094 p = 1) : d3358 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45165 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45176 p hg
    simpa only [d8094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45178 (p : Pattern) (guard : d8095 p = 1) : d3358 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45175 p hg
    simpa only [d8095, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45177 p hg
    simpa only [d8095, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45179 (p : Pattern) (guard : d8094 p = 1) : d3358 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45174 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45176 p hg
    simpa only [d8094, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45180 (p : Pattern) (guard : d8100 p = 1) : d3362 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3362, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45179 p hg
    simpa only [d8100, d3362, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3362, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d3362, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45181 (p : Pattern) (guard : d8101 p = 1) : d3364 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3364, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45178 p hg
    simpa only [d8101, d3364, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3364, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45180 p hg
    simpa only [d8101, d3364, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45182 (p : Pattern) (guard : d8102 p = 1) : d3365 p ≤ (0 : Int) + d434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d3365, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45170 p hg
    simpa only [d8102, d3365, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d3365, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45181 p hg
    simpa only [d8102, d3365, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45183 (p : Pattern) (guard : d1 p = 1) : d3358 p ≤ (0 : Int) + d348 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3358, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35121 p hg
    simpa only [d3358, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3358, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d3358, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45184 (p : Pattern) (guard : d8085 p = 1) : d3358 p ≤ (0 : Int) + d349 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45183 p hg
    simpa only [d8085, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45160 p hg
    simpa only [d8085, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45185 (p : Pattern) (guard : d8090 p = 1) : d3358 p ≤ (0 : Int) + d350 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45184 p hg
    simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45165 p hg
    simpa only [d8090, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45186 (p : Pattern) (guard : d8095 p = 1) : d3358 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45185 p hg
    simpa only [d8095, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45177 p hg
    simpa only [d8095, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45187 (p : Pattern) (guard : d8100 p = 1) : d3362 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d3362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45177 p hg
    simpa only [d8100, d3362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d3362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d3362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45188 (p : Pattern) (guard : d8101 p = 1) : d3364 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3364, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45186 p hg
    simpa only [d8101, d3364, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3364, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45187 p hg
    simpa only [d8101, d3364, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45189 (p : Pattern) (guard : d8084 p = 1) : d3366 p ≤ (0 : Int) + d315 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3366, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35129 p hg
    simpa only [d8084, d3366, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3366, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3366, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45190 (p : Pattern) (guard : d5847 p = 1) : d3366 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35132 p hg
    simpa only [d5847, d3366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45191 (p : Pattern) (guard : d8089 p = 1) : d3366 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45189 p hg
    simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45190 p hg
    simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45192 (p : Pattern) (guard : d5854 p = 1) : d3366 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45190 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26786 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45193 (p : Pattern) (guard : d8094 p = 1) : d3366 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45191 p hg
    simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45192 p hg
    simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45194 (p : Pattern) (guard : d8099 p = 1) : d3366 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45192 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26786 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45195 (p : Pattern) (guard : d8100 p = 1) : d3366 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45193 p hg
    simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45194 p hg
    simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45196 (p : Pattern) (guard : d8105 p = 1) : d3367 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d3367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45194 p hg
    simpa only [d8105, d3367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d3367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d3367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45197 (p : Pattern) (guard : d8106 p = 1) : d3368 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3368, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45195 p hg
    simpa only [d8106, d3368, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3368, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45196 p hg
    simpa only [d8106, d3368, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45198 (p : Pattern) (guard : d8107 p = 1) : d3369 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3369, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45188 p hg
    simpa only [d8107, d3369, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3369, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45197 p hg
    simpa only [d8107, d3369, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45199 (p : Pattern) (guard : d8108 p = 1) : d3370 p ≤ (0 : Int) + d435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d3370, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45182 p hg
    simpa only [d8108, d3370, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d3370, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45198 p hg
    simpa only [d8108, d3370, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45200 (p : Pattern) (guard : d1 p = 1) : d3358 p ≤ (0 : Int) + d364 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3358, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35144 p hg
    simpa only [d3358, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3358, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d3358, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45201 (p : Pattern) (guard : d8085 p = 1) : d3358 p ≤ (0 : Int) + d365 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45200 p hg
    simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45160 p hg
    simpa only [d8085, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45202 (p : Pattern) (guard : d8090 p = 1) : d3358 p ≤ (0 : Int) + d366 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45201 p hg
    simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45165 p hg
    simpa only [d8090, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45203 (p : Pattern) (guard : d8095 p = 1) : d3358 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45202 p hg
    simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45177 p hg
    simpa only [d8095, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45204 (p : Pattern) (guard : d8101 p = 1) : d3364 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d3364, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45203 p hg
    simpa only [d8101, d3364, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d3364, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45187 p hg
    simpa only [d8101, d3364, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45205 (p : Pattern) (guard : d8084 p = 1) : d3366 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3366, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35150 p hg
    simpa only [d8084, d3366, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3366, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3366, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45206 (p : Pattern) (guard : d8089 p = 1) : d3366 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45205 p hg
    simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45190 p hg
    simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45207 (p : Pattern) (guard : d8094 p = 1) : d3366 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45206 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45192 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45208 (p : Pattern) (guard : d8100 p = 1) : d3366 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45207 p hg
    simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45194 p hg
    simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45209 (p : Pattern) (guard : d8106 p = 1) : d3368 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d3368, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45208 p hg
    simpa only [d8106, d3368, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d3368, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45196 p hg
    simpa only [d8106, d3368, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45210 (p : Pattern) (guard : d8107 p = 1) : d3369 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d3369, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45204 p hg
    simpa only [d8107, d3369, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d3369, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45209 p hg
    simpa only [d8107, d3369, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45211 (p : Pattern) (guard : d8112 p = 1) : d3371 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d3371, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45067 p hg
    simpa only [d8112, d3371, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d3371, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d3371, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45212 (p : Pattern) (guard : d8113 p = 1) : d3372 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d3372, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45210 p hg
    simpa only [d8113, d3372, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d3372, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45211 p hg
    simpa only [d8113, d3372, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45213 (p : Pattern) (guard : d8114 p = 1) : d3373 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d3373, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45199 p hg
    simpa only [d8114, d3373, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d3373, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45212 p hg
    simpa only [d8114, d3373, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45214 (p : Pattern) (guard : d1 p = 1) : d3358 p ≤ (0 : Int) + d317 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3358, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35160 p hg
    simpa only [d3358, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3358, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d3358, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45215 (p : Pattern) (guard : d8085 p = 1) : d3358 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45214 p hg
    simpa only [d8085, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45160 p hg
    simpa only [d8085, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45216 (p : Pattern) (guard : d8090 p = 1) : d3358 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45215 p hg
    simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45165 p hg
    simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45217 (p : Pattern) (guard : d8095 p = 1) : d3358 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45216 p hg
    simpa only [d8095, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45177 p hg
    simpa only [d8095, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45218 (p : Pattern) (guard : d8084 p = 1) : d3374 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d3374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1571 p hg
    simpa only [d8084, d3374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d3374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d8084, d3374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare45219 (p : Pattern) (guard : d5847 p = 1) : d3374 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d3374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35167 p hg
    simpa only [d5847, d3374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d3374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5847, d3374, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
