/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons295
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare41440 (p : Pattern) (guard : d8143 p = 1) : d166 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d166, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35376 p hg
    simpa only [d8143, d166, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d166, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41439 p hg
    simpa only [d8143, d166, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41441 (p : Pattern) (guard : d8144 p = 1) : d167 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d167, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41433 p hg
    simpa only [d8144, d167, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d167, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41440 p hg
    simpa only [d8144, d167, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41442 (p : Pattern) (guard : d8145 p = 1) : d168 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8139 p = 1 := by simpa only [d8145, d168, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41423 p hg
    simpa only [d8145, d168, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8144 p = 1 := by simpa only [d8145, d168, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41441 p hg
    simpa only [d8145, d168, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41443 (p : Pattern) (guard : d8146 p = 1) : d169 p ≤ (0 : Int) + d447 p := by
  cases selected : p 49 with
  | false =>
    have hg : d8140 p = 1 := by simpa only [d8146, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41407 p hg
    simpa only [d8146, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8145 p = 1 := by simpa only [d8146, d169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41442 p hg
    simpa only [d8146, d169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41444 (p : Pattern) (guard : d8135 p = 1) : d95 p ≤ (0 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38247 p hg
    simpa only [d8135, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8135, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41445 (p : Pattern) (guard : d8136 p = 1) : d96 p ≤ (0 : Int) + d441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d96, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38248 p hg
    simpa only [d8136, d96, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d96, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41444 p hg
    simpa only [d8136, d96, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41446 (p : Pattern) (guard : d8137 p = 1) : d97 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d97, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35635 p hg
    simpa only [d8137, d97, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d97, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41445 p hg
    simpa only [d8137, d97, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41447 (p : Pattern) (guard : d8138 p = 1) : d98 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d98, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35478 p hg
    simpa only [d8138, d98, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d98, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41446 p hg
    simpa only [d8138, d98, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41448 (p : Pattern) (guard : d8111 p = 1) : d170 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34896 p hg
    simpa only [d8111, d170, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5064 p hg
    simpa only [d8111, d170, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41449 (p : Pattern) (guard : d8112 p = 1) : d171 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d171, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35019 p hg
    simpa only [d8112, d171, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d171, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41448 p hg
    simpa only [d8112, d171, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41450 (p : Pattern) (guard : d8111 p = 1) : d172 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34896 p hg
    simpa only [d8111, d172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5067 p hg
    simpa only [d8111, d172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41451 (p : Pattern) (guard : d8117 p = 1) : d174 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41450 p hg
    simpa only [d8117, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8067 p hg
    simpa only [d8117, d174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41452 (p : Pattern) (guard : d8118 p = 1) : d175 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d175, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41449 p hg
    simpa only [d8118, d175, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d175, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41451 p hg
    simpa only [d8118, d175, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41453 (p : Pattern) (guard : d8117 p = 1) : d176 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34897 p hg
    simpa only [d8117, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8067 p hg
    simpa only [d8117, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41454 (p : Pattern) (guard : d8123 p = 1) : d177 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41453 p hg
    simpa only [d8123, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10096 p hg
    simpa only [d8123, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41455 (p : Pattern) (guard : d8124 p = 1) : d178 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d178, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41452 p hg
    simpa only [d8124, d178, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d178, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41454 p hg
    simpa only [d8124, d178, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41456 (p : Pattern) (guard : d8125 p = 1) : d179 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d179, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35496 p hg
    simpa only [d8125, d179, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d179, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41455 p hg
    simpa only [d8125, d179, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41457 (p : Pattern) (guard : d8117 p = 1) : d180 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41448 p hg
    simpa only [d8117, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3627 p hg
    simpa only [d8117, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41458 (p : Pattern) (guard : d0 p = 1) : d181 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41459 (p : Pattern) (guard : d8123 p = 1) : d182 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41457 p hg
    simpa only [d8123, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d8123, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41460 (p : Pattern) (guard : d8129 p = 1) : d185 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41459 p hg
    simpa only [d8129, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13607 p hg
    simpa only [d8129, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41461 (p : Pattern) (guard : d8130 p = 1) : d186 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d186, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35531 p hg
    simpa only [d8130, d186, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d186, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41460 p hg
    simpa only [d8130, d186, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41462 (p : Pattern) (guard : d8131 p = 1) : d187 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d187, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41456 p hg
    simpa only [d8131, d187, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d187, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41461 p hg
    simpa only [d8131, d187, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41463 (p : Pattern) (guard : d8118 p = 1) : d188 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d188, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35540 p hg
    simpa only [d8118, d188, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d188, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35545 p hg
    simpa only [d8118, d188, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41464 (p : Pattern) (guard : d8124 p = 1) : d189 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d189, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41463 p hg
    simpa only [d8124, d189, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d189, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35546 p hg
    simpa only [d8124, d189, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41465 (p : Pattern) (guard : d0 p = 1) : d193 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41466 (p : Pattern) (guard : d8117 p = 1) : d194 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34911 p hg
    simpa only [d8117, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41465 p hg
    simpa only [d8117, d194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41467 (p : Pattern) (guard : d8123 p = 1) : d195 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41466 p hg
    simpa only [d8123, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41468 (p : Pattern) (guard : d8129 p = 1) : d196 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41467 p hg
    simpa only [d8129, d196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41469 (p : Pattern) (guard : d8130 p = 1) : d197 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d197, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41464 p hg
    simpa only [d8130, d197, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d197, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41468 p hg
    simpa only [d8130, d197, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41470 (p : Pattern) (guard : d8117 p = 1) : d53 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35472 p hg
    simpa only [d8117, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8075 p hg
    simpa only [d8117, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41471 (p : Pattern) (guard : d8123 p = 1) : d199 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d199, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41470 p hg
    simpa only [d8123, d199, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d199, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6600 p hg
    simpa only [d8123, d199, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41472 (p : Pattern) (guard : d8129 p = 1) : d200 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d200, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41471 p hg
    simpa only [d8129, d200, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d200, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3318 p hg
    simpa only [d8129, d200, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41473 (p : Pattern) (guard : d8135 p = 1) : d204 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d204, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41472 p hg
    simpa only [d8135, d204, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d204, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4653 p hg
    simpa only [d8135, d204, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41474 (p : Pattern) (guard : d8136 p = 1) : d205 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d205, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41469 p hg
    simpa only [d8136, d205, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d205, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41473 p hg
    simpa only [d8136, d205, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41475 (p : Pattern) (guard : d8137 p = 1) : d206 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d206, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41462 p hg
    simpa only [d8137, d206, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d206, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41474 p hg
    simpa only [d8137, d206, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41476 (p : Pattern) (guard : d8118 p = 1) : d188 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d188, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35678 p hg
    simpa only [d8118, d188, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d188, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35545 p hg
    simpa only [d8118, d188, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41477 (p : Pattern) (guard : d8124 p = 1) : d189 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d189, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41476 p hg
    simpa only [d8124, d189, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d189, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35546 p hg
    simpa only [d8124, d189, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41478 (p : Pattern) (guard : d8130 p = 1) : d197 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d197, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41477 p hg
    simpa only [d8130, d197, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d197, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41468 p hg
    simpa only [d8130, d197, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41479 (p : Pattern) (guard : d8117 p = 1) : d53 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35629 p hg
    simpa only [d8117, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8075 p hg
    simpa only [d8117, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41480 (p : Pattern) (guard : d8123 p = 1) : d199 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d199, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41479 p hg
    simpa only [d8123, d199, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d199, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6600 p hg
    simpa only [d8123, d199, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41481 (p : Pattern) (guard : d8129 p = 1) : d200 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d200, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41480 p hg
    simpa only [d8129, d200, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d200, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3318 p hg
    simpa only [d8129, d200, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41482 (p : Pattern) (guard : d8135 p = 1) : d204 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d204, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41481 p hg
    simpa only [d8135, d204, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d204, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4653 p hg
    simpa only [d8135, d204, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41483 (p : Pattern) (guard : d8136 p = 1) : d205 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d205, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41478 p hg
    simpa only [d8136, d205, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d205, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41482 p hg
    simpa only [d8136, d205, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41484 (p : Pattern) (guard : d8142 p = 1) : d207 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d207, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41483 p hg
    simpa only [d8142, d207, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d207, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d207, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41485 (p : Pattern) (guard : d8143 p = 1) : d208 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d208, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41475 p hg
    simpa only [d8143, d208, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d208, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41484 p hg
    simpa only [d8143, d208, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41486 (p : Pattern) (guard : d8144 p = 1) : d209 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d209, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41447 p hg
    simpa only [d8144, d209, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d209, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41485 p hg
    simpa only [d8144, d209, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41487 (p : Pattern) (guard : d8145 p = 1) : d210 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8139 p = 1 := by simpa only [d8145, d210, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41423 p hg
    simpa only [d8145, d210, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8144 p = 1 := by simpa only [d8145, d210, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41486 p hg
    simpa only [d8145, d210, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41488 (p : Pattern) (guard : d8130 p = 1) : d86 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d86, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35531 p hg
    simpa only [d8130, d86, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d86, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34938 p hg
    simpa only [d8130, d86, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41489 (p : Pattern) (guard : d8131 p = 1) : d87 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d87, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38266 p hg
    simpa only [d8131, d87, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d87, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41488 p hg
    simpa only [d8131, d87, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41490 (p : Pattern) (guard : d8123 p = 1) : d91 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d91, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35606 p hg
    simpa only [d8123, d91, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d91, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d91, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41491 (p : Pattern) (guard : d8129 p = 1) : d93 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d93, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41490 p hg
    simpa only [d8129, d93, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d93, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d93, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41492 (p : Pattern) (guard : d8135 p = 1) : d95 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d95, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41491 p hg
    simpa only [d8135, d95, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d95, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8135, d95, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41493 (p : Pattern) (guard : d8136 p = 1) : d96 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d96, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38271 p hg
    simpa only [d8136, d96, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d96, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41492 p hg
    simpa only [d8136, d96, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41494 (p : Pattern) (guard : d8137 p = 1) : d97 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d97, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41489 p hg
    simpa only [d8137, d97, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d97, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41493 p hg
    simpa only [d8137, d97, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41495 (p : Pattern) (guard : d8138 p = 1) : d98 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d98, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35636 p hg
    simpa only [d8138, d98, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d98, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41494 p hg
    simpa only [d8138, d98, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41496 (p : Pattern) (guard : d8105 p = 1) : d14 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39765 p hg
    simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11458 p hg
    simpa only [d8105, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41497 (p : Pattern) (guard : d8111 p = 1) : d16 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d16, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41496 p hg
    simpa only [d8111, d16, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d16, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5054 p hg
    simpa only [d8111, d16, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41498 (p : Pattern) (guard : d8117 p = 1) : d54 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d54, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41497 p hg
    simpa only [d8117, d54, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d54, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8075 p hg
    simpa only [d8117, d54, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41499 (p : Pattern) (guard : d8123 p = 1) : d56 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d56, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41498 p hg
    simpa only [d8123, d56, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d56, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6474 p hg
    simpa only [d8123, d56, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41500 (p : Pattern) (guard : d8129 p = 1) : d65 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d65, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41499 p hg
    simpa only [d8129, d65, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d65, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3237 p hg
    simpa only [d8129, d65, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41501 (p : Pattern) (guard : d8135 p = 1) : d86 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d86, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41500 p hg
    simpa only [d8135, d86, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d86, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4600 p hg
    simpa only [d8135, d86, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41502 (p : Pattern) (guard : d8136 p = 1) : d87 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d87, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38281 p hg
    simpa only [d8136, d87, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d87, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41501 p hg
    simpa only [d8136, d87, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41503 (p : Pattern) (guard : d8142 p = 1) : d99 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d99, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41502 p hg
    simpa only [d8142, d99, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d99, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d99, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41504 (p : Pattern) (guard : d8143 p = 1) : d100 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d100, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35692 p hg
    simpa only [d8143, d100, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d100, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41503 p hg
    simpa only [d8143, d100, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41505 (p : Pattern) (guard : d8144 p = 1) : d101 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d101, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41495 p hg
    simpa only [d8144, d101, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d101, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41504 p hg
    simpa only [d8144, d101, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41506 (p : Pattern) (guard : d8117 p = 1) : d133 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d133, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35820 p hg
    simpa only [d8117, d133, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d133, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8252 p hg
    simpa only [d8117, d133, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41507 (p : Pattern) (guard : d0 p = 1) : d211 p ≤ (0 : Int) + d374 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41508 (p : Pattern) (guard : d8123 p = 1) : d212 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d212, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41506 p hg
    simpa only [d8123, d212, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d212, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41507 p hg
    simpa only [d8123, d212, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41509 (p : Pattern) (guard : d8129 p = 1) : d214 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d214, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41508 p hg
    simpa only [d8129, d214, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d214, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3335 p hg
    simpa only [d8129, d214, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41510 (p : Pattern) (guard : d8135 p = 1) : d221 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d221, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41509 p hg
    simpa only [d8135, d221, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d221, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4630 p hg
    simpa only [d8135, d221, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41511 (p : Pattern) (guard : d8136 p = 1) : d222 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d222, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38302 p hg
    simpa only [d8136, d222, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d222, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41510 p hg
    simpa only [d8136, d222, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41512 (p : Pattern) (guard : d8142 p = 1) : d224 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d224, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41511 p hg
    simpa only [d8142, d224, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d224, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38307 p hg
    simpa only [d8142, d224, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41513 (p : Pattern) (guard : d8143 p = 1) : d225 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d225, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35803 p hg
    simpa only [d8143, d225, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d225, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41512 p hg
    simpa only [d8143, d225, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41514 (p : Pattern) (guard : d0 p = 1) : d226 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41515 (p : Pattern) (guard : d8117 p = 1) : d227 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d227, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41425 p hg
    simpa only [d8117, d227, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d227, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41514 p hg
    simpa only [d8117, d227, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41516 (p : Pattern) (guard : d8123 p = 1) : d228 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d228, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41515 p hg
    simpa only [d8123, d228, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d228, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35778 p hg
    simpa only [d8123, d228, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41517 (p : Pattern) (guard : d8129 p = 1) : d232 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d232, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41516 p hg
    simpa only [d8129, d232, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d232, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13638 p hg
    simpa only [d8129, d232, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41518 (p : Pattern) (guard : d8130 p = 1) : d233 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d233, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35826 p hg
    simpa only [d8130, d233, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d233, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41517 p hg
    simpa only [d8130, d233, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41519 (p : Pattern) (guard : d8135 p = 1) : d239 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d239, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35843 p hg
    simpa only [d8135, d239, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d239, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4669 p hg
    simpa only [d8135, d239, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41520 (p : Pattern) (guard : d8136 p = 1) : d240 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d240, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41518 p hg
    simpa only [d8136, d240, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d240, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41519 p hg
    simpa only [d8136, d240, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41521 (p : Pattern) (guard : d8117 p = 1) : d105 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35783 p hg
    simpa only [d8117, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3808 p hg
    simpa only [d8117, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41522 (p : Pattern) (guard : d8123 p = 1) : d242 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d242, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41521 p hg
    simpa only [d8123, d242, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d242, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6644 p hg
    simpa only [d8123, d242, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41523 (p : Pattern) (guard : d8129 p = 1) : d243 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d243, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41522 p hg
    simpa only [d8129, d243, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d243, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3285 p hg
    simpa only [d8129, d243, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41524 (p : Pattern) (guard : d8135 p = 1) : d244 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d244, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41523 p hg
    simpa only [d8135, d244, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d244, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4630 p hg
    simpa only [d8135, d244, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41525 (p : Pattern) (guard : d0 p = 1) : d249 p ≤ (0 : Int) + d411 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41526 (p : Pattern) (guard : d8141 p = 1) : d250 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8135 p = 1 := by simpa only [d8141, d250, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41524 p hg
    simpa only [d8141, d250, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8141, d250, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41525 p hg
    simpa only [d8141, d250, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41527 (p : Pattern) (guard : d8142 p = 1) : d251 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d251, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41520 p hg
    simpa only [d8142, d251, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d251, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41526 p hg
    simpa only [d8142, d251, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41528 (p : Pattern) (guard : d8117 p = 1) : d105 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35797 p hg
    simpa only [d8117, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3816 p hg
    simpa only [d8117, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41529 (p : Pattern) (guard : d8123 p = 1) : d253 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d253, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41528 p hg
    simpa only [d8123, d253, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d253, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6658 p hg
    simpa only [d8123, d253, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41530 (p : Pattern) (guard : d8129 p = 1) : d256 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d256, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41529 p hg
    simpa only [d8129, d256, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d256, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3350 p hg
    simpa only [d8129, d256, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41531 (p : Pattern) (guard : d8135 p = 1) : d260 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d260, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41530 p hg
    simpa only [d8135, d260, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d260, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4678 p hg
    simpa only [d8135, d260, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41532 (p : Pattern) (guard : d0 p = 1) : d249 p ≤ (0 : Int) + d421 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41533 (p : Pattern) (guard : d8141 p = 1) : d261 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8135 p = 1 := by simpa only [d8141, d261, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41531 p hg
    simpa only [d8141, d261, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8141, d261, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41532 p hg
    simpa only [d8141, d261, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41534 (p : Pattern) (guard : d8147 p = 1) : d262 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8141 p = 1 := by simpa only [d8147, d262, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41533 p hg
    simpa only [d8147, d262, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8147, d262, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8147, d262, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41535 (p : Pattern) (guard : d8148 p = 1) : d263 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8142 p = 1 := by simpa only [d8148, d263, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41527 p hg
    simpa only [d8148, d263, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8147 p = 1 := by simpa only [d8148, d263, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41534 p hg
    simpa only [d8148, d263, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41536 (p : Pattern) (guard : d8149 p = 1) : d264 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8143 p = 1 := by simpa only [d8149, d264, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41513 p hg
    simpa only [d8149, d264, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8148 p = 1 := by simpa only [d8149, d264, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41535 p hg
    simpa only [d8149, d264, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41537 (p : Pattern) (guard : d8150 p = 1) : d265 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8144 p = 1 := by simpa only [d8150, d265, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41505 p hg
    simpa only [d8150, d265, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8149 p = 1 := by simpa only [d8150, d265, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41536 p hg
    simpa only [d8150, d265, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41538 (p : Pattern) (guard : d8151 p = 1) : d266 p ≤ (0 : Int) + d447 p := by
  cases selected : p 49 with
  | false =>
    have hg : d8145 p = 1 := by simpa only [d8151, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41487 p hg
    simpa only [d8151, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8150 p = 1 := by simpa only [d8151, d266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41537 p hg
    simpa only [d8151, d266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41539 (p : Pattern) (guard : d8152 p = 1) : d267 p ≤ (0 : Int) + d447 p := by
  cases selected : p 48 with
  | false =>
    have hg : d8146 p = 1 := by simpa only [d8152, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41443 p hg
    simpa only [d8152, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8151 p = 1 := by simpa only [d8152, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41538 p hg
    simpa only [d8152, d267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41540 (p : Pattern) (guard : d8121 p = 1) : d400 p ≤ (0 : Int) + d400 p := by
  omega
theorem compare41541 (p : Pattern) (guard : d8122 p = 1) : d517 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8116 p = 1 := by simpa only [d8122, d517, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34548 p hg
    simpa only [d8122, d517, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8121 p = 1 := by simpa only [d8122, d517, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41540 p hg
    simpa only [d8122, d517, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41542 (p : Pattern) (guard : d8091 p = 1) : d518 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d518, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34343 p hg
    simpa only [d8091, d518, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d518, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34365 p hg
    simpa only [d8091, d518, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41543 (p : Pattern) (guard : d8096 p = 1) : d519 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d519, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41542 p hg
    simpa only [d8096, d519, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d519, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34427 p hg
    simpa only [d8096, d519, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41544 (p : Pattern) (guard : d8095 p = 1) : d518 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34418 p hg
    simpa only [d8095, d518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34441 p hg
    simpa only [d8095, d518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41545 (p : Pattern) (guard : d8101 p = 1) : d520 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41544 p hg
    simpa only [d8101, d520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34504 p hg
    simpa only [d8101, d520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41546 (p : Pattern) (guard : d8102 p = 1) : d521 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d521, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41543 p hg
    simpa only [d8102, d521, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d521, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41545 p hg
    simpa only [d8102, d521, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41547 (p : Pattern) (guard : d8101 p = 1) : d522 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41544 p hg
    simpa only [d8101, d522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41548 (p : Pattern) (guard : d5843 p = 1) : d8 p ≤ (0 : Int) + d12 p := by
  change (8 : Int) ≤ (0 : Int) + 12
  decide
theorem compare41549 (p : Pattern) (guard : d5847 p = 1) : d191 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41548 p hg
    simpa only [d5847, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17896 p hg
    simpa only [d5847, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41550 (p : Pattern) (guard : d5854 p = 1) : d191 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41549 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11750 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41551 (p : Pattern) (guard : d8099 p = 1) : d191 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41550 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11750 p hg
    simpa only [d8099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41552 (p : Pattern) (guard : d8100 p = 1) : d523 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34441 p hg
    simpa only [d8100, d523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41551 p hg
    simpa only [d8100, d523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41553 (p : Pattern) (guard : d8106 p = 1) : d524 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41552 p hg
    simpa only [d8106, d524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41554 (p : Pattern) (guard : d8107 p = 1) : d525 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41547 p hg
    simpa only [d8107, d525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41553 p hg
    simpa only [d8107, d525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41555 (p : Pattern) (guard : d8108 p = 1) : d526 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d526, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41546 p hg
    simpa only [d8108, d526, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d526, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41554 p hg
    simpa only [d8108, d526, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41556 (p : Pattern) (guard : d8113 p = 1) : d529 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41554 p hg
    simpa only [d8113, d529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38661 p hg
    simpa only [d8113, d529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41557 (p : Pattern) (guard : d8114 p = 1) : d530 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d530, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41555 p hg
    simpa only [d8114, d530, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d530, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41556 p hg
    simpa only [d8114, d530, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41558 (p : Pattern) (guard : d8115 p = 1) : d531 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d531, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38106 p hg
    simpa only [d8115, d531, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d531, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41557 p hg
    simpa only [d8115, d531, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41559 (p : Pattern) (guard : d8100 p = 1) : d532 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34526 p hg
    simpa only [d8100, d532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34709 p hg
    simpa only [d8100, d532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41560 (p : Pattern) (guard : d8106 p = 1) : d533 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d8106, d533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41561 (p : Pattern) (guard : d8107 p = 1) : d534 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41545 p hg
    simpa only [d8107, d534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41560 p hg
    simpa only [d8107, d534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41562 (p : Pattern) (guard : d8112 p = 1) : d535 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41553 p hg
    simpa only [d8112, d535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38688 p hg
    simpa only [d8112, d535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41563 (p : Pattern) (guard : d8113 p = 1) : d536 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41561 p hg
    simpa only [d8113, d536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41562 p hg
    simpa only [d8113, d536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41564 (p : Pattern) (guard : d8112 p = 1) : d537 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41553 p hg
    simpa only [d8112, d537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38691 p hg
    simpa only [d8112, d537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41565 (p : Pattern) (guard : d8118 p = 1) : d540 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41564 p hg
    simpa only [d8118, d540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38694 p hg
    simpa only [d8118, d540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41566 (p : Pattern) (guard : d8119 p = 1) : d541 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41563 p hg
    simpa only [d8119, d541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41565 p hg
    simpa only [d8119, d541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41567 (p : Pattern) (guard : d8120 p = 1) : d542 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d542, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41383 p hg
    simpa only [d8120, d542, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d542, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41566 p hg
    simpa only [d8120, d542, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41568 (p : Pattern) (guard : d8121 p = 1) : d543 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d543, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41558 p hg
    simpa only [d8121, d543, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d543, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41567 p hg
    simpa only [d8121, d543, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41569 (p : Pattern) (guard : d8126 p = 1) : d412 p ≤ (0 : Int) + d412 p := by
  omega
theorem compare41570 (p : Pattern) (guard : d8127 p = 1) : d544 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d544, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41568 p hg
    simpa only [d8127, d544, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d544, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41569 p hg
    simpa only [d8127, d544, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41571 (p : Pattern) (guard : d8128 p = 1) : d545 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8122 p = 1 := by simpa only [d8128, d545, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41541 p hg
    simpa only [d8128, d545, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8127 p = 1 := by simpa only [d8128, d545, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41570 p hg
    simpa only [d8128, d545, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41572 (p : Pattern) (guard : d8126 p = 1) : d422 p ≤ (0 : Int) + d422 p := by
  omega
theorem compare41573 (p : Pattern) (guard : d8127 p = 1) : d546 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d546, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34695 p hg
    simpa only [d8127, d546, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d546, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41572 p hg
    simpa only [d8127, d546, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41574 (p : Pattern) (guard : d8101 p = 1) : d519 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41544 p hg
    simpa only [d8101, d519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34570 p hg
    simpa only [d8101, d519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41575 (p : Pattern) (guard : d8100 p = 1) : d518 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34637 p hg
    simpa only [d8100, d518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34642 p hg
    simpa only [d8100, d518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41576 (p : Pattern) (guard : d8106 p = 1) : d520 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41575 p hg
    simpa only [d8106, d520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34602 p hg
    simpa only [d8106, d520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41577 (p : Pattern) (guard : d8107 p = 1) : d521 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41574 p hg
    simpa only [d8107, d521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41576 p hg
    simpa only [d8107, d521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41578 (p : Pattern) (guard : d8106 p = 1) : d522 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41575 p hg
    simpa only [d8106, d522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41579 (p : Pattern) (guard : d8105 p = 1) : d523 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34642 p hg
    simpa only [d8105, d523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11750 p hg
    simpa only [d8105, d523, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
