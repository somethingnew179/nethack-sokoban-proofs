/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons031
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare4480 (p : Pattern) (guard : d1 p = 1) : d22 p ≤ (0 : Int) + d175 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d22, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4476 p hg
    simpa only [d22, d175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d22, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4479 p hg
    simpa only [d22, d175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4481 (p : Pattern) (guard : d1 p = 1) : d16 p ≤ (0 : Int) + d66 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d16, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare781 p hg
    simpa only [d16, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d16, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2007 p hg
    simpa only [d16, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4482 (p : Pattern) (guard : d1 p = 1) : d21 p ≤ (0 : Int) + d176 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d21, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d21, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d21, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4478 p hg
    simpa only [d21, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4483 (p : Pattern) (guard : d1 p = 1) : d26 p ≤ (0 : Int) + d72 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d26, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare799 p hg
    simpa only [d26, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d26, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare869 p hg
    simpa only [d26, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4484 (p : Pattern) (guard : d1 p = 1) : d27 p ≤ (0 : Int) + d73 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d27, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4483 p hg
    simpa only [d27, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d27, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d27, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4485 (p : Pattern) (guard : d1 p = 1) : d28 p ≤ (0 : Int) + d177 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d28, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4482 p hg
    simpa only [d28, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d28, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4484 p hg
    simpa only [d28, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4486 (p : Pattern) (guard : d1 p = 1) : d29 p ≤ (0 : Int) + d178 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d29, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4480 p hg
    simpa only [d29, d178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d29, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4485 p hg
    simpa only [d29, d178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4487 (p : Pattern) (guard : d0 p = 1) : d178 p ≤ (0 : Int) + d178 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4488 (p : Pattern) (guard : d4117 p = 1) : d179 p ≤ (0 : Int) + d178 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4486 p hg
    simpa only [d4117, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4487 p hg
    simpa only [d4117, d179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4489 (p : Pattern) (guard : d1 p = 1) : d53 p ≤ (0 : Int) + d43 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d53, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare808 p hg
    simpa only [d53, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d53, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1541 p hg
    simpa only [d53, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4490 (p : Pattern) (guard : d1 p = 1) : d54 p ≤ (0 : Int) + d180 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d54, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4475 p hg
    simpa only [d54, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d54, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4489 p hg
    simpa only [d54, d180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4491 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (0 : Int) + d181 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d55, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4478 p hg
    simpa only [d55, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d55, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4483 p hg
    simpa only [d55, d181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4492 (p : Pattern) (guard : d1 p = 1) : d56 p ≤ (0 : Int) + d182 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d56, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4490 p hg
    simpa only [d56, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d56, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4491 p hg
    simpa only [d56, d182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4493 (p : Pattern) (guard : d1 p = 1) : d61 p ≤ (0 : Int) + d183 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d61, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4478 p hg
    simpa only [d61, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d61, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare851 p hg
    simpa only [d61, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4494 (p : Pattern) (guard : d1 p = 1) : d64 p ≤ (0 : Int) + d184 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d64, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d64, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d64, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare735 p hg
    simpa only [d64, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4495 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (0 : Int) + d185 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d65, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4492 p hg
    simpa only [d65, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d65, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4494 p hg
    simpa only [d65, d185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4496 (p : Pattern) (guard : d0 p = 1) : d185 p ≤ (0 : Int) + d185 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4497 (p : Pattern) (guard : d4117 p = 1) : d186 p ≤ (0 : Int) + d185 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4495 p hg
    simpa only [d4117, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4496 p hg
    simpa only [d4117, d186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4498 (p : Pattern) (guard : d4117 p = 1) : d187 p ≤ (0 : Int) + d4413 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d187, d4413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4488 p hg
    simpa only [d187, d4413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d187, d4413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4497 p hg
    simpa only [d187, d4413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4499 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (0 : Int) + d8 p := by
  change (0 : Int) ≤ (0 : Int) + 8
  decide
theorem compare4500 (p : Pattern) (guard : d1 p = 1) : d13 p ≤ (0 : Int) + d190 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d13, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4499 p hg
    simpa only [d13, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d13, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d13, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4501 (p : Pattern) (guard : d1 p = 1) : d14 p ≤ (0 : Int) + d191 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d14, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4499 p hg
    simpa only [d14, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d14, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4500 p hg
    simpa only [d14, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4502 (p : Pattern) (guard : d1 p = 1) : d15 p ≤ (0 : Int) + d192 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d15, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4501 p hg
    simpa only [d15, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d15, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d15, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4503 (p : Pattern) (guard : d1 p = 1) : d16 p ≤ (0 : Int) + d193 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d16, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4501 p hg
    simpa only [d16, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d16, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4502 p hg
    simpa only [d16, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4504 (p : Pattern) (guard : d1 p = 1) : d16 p ≤ (0 : Int) + d194 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1196 p hg
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4503 p hg
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4505 (p : Pattern) (guard : d1 p = 1) : d79 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1542 p hg
    simpa only [d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare959 p hg
    simpa only [d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4506 (p : Pattern) (guard : d1 p = 1) : d188 p ≤ (0 : Int) + d195 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d188, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4504 p hg
    simpa only [d188, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d188, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4505 p hg
    simpa only [d188, d195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4507 (p : Pattern) (guard : d1 p = 1) : d80 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4505 p hg
    simpa only [d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare735 p hg
    simpa only [d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4508 (p : Pattern) (guard : d1 p = 1) : d189 p ≤ (0 : Int) + d196 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d189, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4506 p hg
    simpa only [d189, d196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d189, d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4507 p hg
    simpa only [d189, d196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4509 (p : Pattern) (guard : d0 p = 1) : d196 p ≤ (0 : Int) + d196 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4510 (p : Pattern) (guard : d4117 p = 1) : d197 p ≤ (0 : Int) + d196 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4508 p hg
    simpa only [d4117, d197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4509 p hg
    simpa only [d4117, d197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4511 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (0 : Int) + d8 p := by
  change (2 : Int) ≤ (0 : Int) + 8
  decide
theorem compare4512 (p : Pattern) (guard : d1 p = 1) : d30 p ≤ (0 : Int) + d190 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d30, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4511 p hg
    simpa only [d30, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d30, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d30, d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4513 (p : Pattern) (guard : d1 p = 1) : d31 p ≤ (0 : Int) + d191 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d31, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4511 p hg
    simpa only [d31, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d31, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4512 p hg
    simpa only [d31, d191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4514 (p : Pattern) (guard : d1 p = 1) : d32 p ≤ (0 : Int) + d192 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d32, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4513 p hg
    simpa only [d32, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d32, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d32, d192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4515 (p : Pattern) (guard : d1 p = 1) : d53 p ≤ (0 : Int) + d193 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d53, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4513 p hg
    simpa only [d53, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d53, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4514 p hg
    simpa only [d53, d193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4516 (p : Pattern) (guard : d1 p = 1) : d53 p ≤ (0 : Int) + d201 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4515 p hg
    simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1542 p hg
    simpa only [d201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4517 (p : Pattern) (guard : d1 p = 1) : d199 p ≤ (0 : Int) + d202 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d199, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d199, d202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d199, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1648 p hg
    simpa only [d199, d202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4518 (p : Pattern) (guard : d1 p = 1) : d200 p ≤ (0 : Int) + d203 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d200, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4517 p hg
    simpa only [d200, d203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d200, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1550 p hg
    simpa only [d200, d203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4519 (p : Pattern) (guard : d0 p = 1) : d203 p ≤ (0 : Int) + d203 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4520 (p : Pattern) (guard : d4117 p = 1) : d204 p ≤ (0 : Int) + d203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4518 p hg
    simpa only [d4117, d204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4519 p hg
    simpa only [d4117, d204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4521 (p : Pattern) (guard : d4117 p = 1) : d205 p ≤ (0 : Int) + d4414 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d205, d4414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4510 p hg
    simpa only [d205, d4414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d205, d4414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4520 p hg
    simpa only [d205, d4414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4522 (p : Pattern) (guard : d4117 p = 1) : d206 p ≤ (0 : Int) + d4415 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d206, d4415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4498 p hg
    simpa only [d206, d4415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d206, d4415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4521 p hg
    simpa only [d206, d4415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4523 (p : Pattern) (guard : d4117 p = 1) : d207 p ≤ (0 : Int) + d4416 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d207, d4416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4521 p hg
    simpa only [d207, d4416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d207, d4416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4444 p hg
    simpa only [d207, d4416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4524 (p : Pattern) (guard : d4117 p = 1) : d208 p ≤ (0 : Int) + d4417 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d208, d4417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4522 p hg
    simpa only [d208, d4417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d208, d4417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d208, d4417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4525 (p : Pattern) (guard : d4117 p = 1) : d209 p ≤ (0 : Int) + d4418 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d209, d4418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4443 p hg
    simpa only [d209, d4418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d209, d4418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4524 p hg
    simpa only [d209, d4418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4526 (p : Pattern) (guard : d4117 p = 1) : d210 p ≤ (0 : Int) + d4419 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d210, d4419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4447 p hg
    simpa only [d210, d4419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d210, d4419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4525 p hg
    simpa only [d210, d4419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4527 (p : Pattern) (guard : d0 p = 1) : d218 p ≤ (0 : Int) + d218 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4528 (p : Pattern) (guard : d4117 p = 1) : d219 p ≤ (0 : Int) + d218 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2087 p hg
    simpa only [d4117, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4527 p hg
    simpa only [d4117, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4529 (p : Pattern) (guard : d4117 p = 1) : d220 p ≤ (0 : Int) + d4132 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d220, d4132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4449 p hg
    simpa only [d220, d4132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d220, d4132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4528 p hg
    simpa only [d220, d4132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4530 (p : Pattern) (guard : d1 p = 1) : d212 p ≤ (0 : Int) + d154 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d212, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4459 p hg
    simpa only [d212, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d212, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1682 p hg
    simpa only [d212, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4531 (p : Pattern) (guard : d1 p = 1) : d213 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1682 p hg
    simpa only [d213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4532 (p : Pattern) (guard : d1 p = 1) : d214 p ≤ (0 : Int) + d155 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d214, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4530 p hg
    simpa only [d214, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d214, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4531 p hg
    simpa only [d214, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4533 (p : Pattern) (guard : d4117 p = 1) : d221 p ≤ (0 : Int) + d155 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4532 p hg
    simpa only [d4117, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4462 p hg
    simpa only [d4117, d221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4534 (p : Pattern) (guard : d4117 p = 1) : d222 p ≤ (0 : Int) + d4407 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d222, d4407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4458 p hg
    simpa only [d222, d4407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d222, d4407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4533 p hg
    simpa only [d222, d4407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4535 (p : Pattern) (guard : d4117 p = 1) : d223 p ≤ (0 : Int) + d4420 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d223, d4420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4529 p hg
    simpa only [d223, d4420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d223, d4420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4534 p hg
    simpa only [d223, d4420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4536 (p : Pattern) (guard : d4117 p = 1) : d224 p ≤ (0 : Int) + d4409 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d224, d4409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4534 p hg
    simpa only [d224, d4409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d224, d4409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4467 p hg
    simpa only [d224, d4409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4537 (p : Pattern) (guard : d4117 p = 1) : d225 p ≤ (0 : Int) + d4421 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d225, d4421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4535 p hg
    simpa only [d225, d4421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d225, d4421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4536 p hg
    simpa only [d225, d4421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4538 (p : Pattern) (guard : d1 p = 1) : d105 p ≤ (0 : Int) + d226 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d105, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1249 p hg
    simpa only [d105, d226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d105, d226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2047 p hg
    simpa only [d105, d226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4539 (p : Pattern) (guard : d1 p = 1) : d105 p ≤ (0 : Int) + d227 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1251 p hg
    simpa only [d227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4538 p hg
    simpa only [d227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4540 (p : Pattern) (guard : d1 p = 1) : d105 p ≤ (0 : Int) + d125 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d105, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1255 p hg
    simpa only [d105, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d105, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1588 p hg
    simpa only [d105, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4541 (p : Pattern) (guard : d1 p = 1) : d110 p ≤ (0 : Int) + d215 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d110, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4540 p hg
    simpa only [d110, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d110, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1323 p hg
    simpa only [d110, d215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4542 (p : Pattern) (guard : d1 p = 1) : d111 p ≤ (0 : Int) + d228 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d111, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4539 p hg
    simpa only [d111, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d111, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d111, d228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4543 (p : Pattern) (guard : d1 p = 1) : d105 p ≤ (0 : Int) + d229 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d105, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1405 p hg
    simpa only [d105, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d105, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1588 p hg
    simpa only [d105, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4544 (p : Pattern) (guard : d1 p = 1) : d110 p ≤ (0 : Int) + d230 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d110, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4543 p hg
    simpa only [d110, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d110, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1323 p hg
    simpa only [d110, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4545 (p : Pattern) (guard : d1 p = 1) : d113 p ≤ (0 : Int) + d231 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d113, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4544 p hg
    simpa only [d113, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d113, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1271 p hg
    simpa only [d113, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4546 (p : Pattern) (guard : d1 p = 1) : d114 p ≤ (0 : Int) + d232 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d114, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4542 p hg
    simpa only [d114, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d114, d232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4545 p hg
    simpa only [d114, d232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4547 (p : Pattern) (guard : d0 p = 1) : d232 p ≤ (0 : Int) + d232 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4548 (p : Pattern) (guard : d4117 p = 1) : d233 p ≤ (0 : Int) + d232 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4546 p hg
    simpa only [d4117, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4547 p hg
    simpa only [d4117, d233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4549 (p : Pattern) (guard : d1 p = 1) : d105 p ≤ (0 : Int) + d234 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d105, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1255 p hg
    simpa only [d105, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d105, d234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2047 p hg
    simpa only [d105, d234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4550 (p : Pattern) (guard : d1 p = 1) : d132 p ≤ (0 : Int) + d125 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d132, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1346 p hg
    simpa only [d132, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d132, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1595 p hg
    simpa only [d132, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4551 (p : Pattern) (guard : d1 p = 1) : d133 p ≤ (0 : Int) + d235 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d133, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4549 p hg
    simpa only [d133, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d133, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4550 p hg
    simpa only [d133, d235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4552 (p : Pattern) (guard : d1 p = 1) : d109 p ≤ (0 : Int) + d229 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d109, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1417 p hg
    simpa only [d109, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d109, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1322 p hg
    simpa only [d109, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4553 (p : Pattern) (guard : d1 p = 1) : d211 p ≤ (0 : Int) + d230 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d211, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4552 p hg
    simpa only [d211, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d211, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d211, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4554 (p : Pattern) (guard : d1 p = 1) : d212 p ≤ (0 : Int) + d236 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d212, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4551 p hg
    simpa only [d212, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d212, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4553 p hg
    simpa only [d212, d236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4555 (p : Pattern) (guard : d1 p = 1) : d109 p ≤ (0 : Int) + d48 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d109, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1423 p hg
    simpa only [d109, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d109, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1322 p hg
    simpa only [d109, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4556 (p : Pattern) (guard : d1 p = 1) : d211 p ≤ (0 : Int) + d49 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d211, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4555 p hg
    simpa only [d211, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d211, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d211, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4557 (p : Pattern) (guard : d1 p = 1) : d213 p ≤ (0 : Int) + d237 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d213, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4556 p hg
    simpa only [d213, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d213, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d213, d237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4558 (p : Pattern) (guard : d1 p = 1) : d214 p ≤ (0 : Int) + d238 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d214, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4554 p hg
    simpa only [d214, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d214, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4557 p hg
    simpa only [d214, d238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4559 (p : Pattern) (guard : d0 p = 1) : d238 p ≤ (0 : Int) + d238 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4560 (p : Pattern) (guard : d4117 p = 1) : d239 p ≤ (0 : Int) + d238 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4558 p hg
    simpa only [d4117, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4559 p hg
    simpa only [d4117, d239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4561 (p : Pattern) (guard : d4117 p = 1) : d240 p ≤ (0 : Int) + d4422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d240, d4422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4548 p hg
    simpa only [d240, d4422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d240, d4422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4560 p hg
    simpa only [d240, d4422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4562 (p : Pattern) (guard : d1 p = 1) : d105 p ≤ (0 : Int) + d153 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4453 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1589 p hg
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4563 (p : Pattern) (guard : d1 p = 1) : d242 p ≤ (0 : Int) + d154 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d242, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4562 p hg
    simpa only [d242, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d242, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1678 p hg
    simpa only [d242, d154, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4564 (p : Pattern) (guard : d1 p = 1) : d243 p ≤ (0 : Int) + d155 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d243, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4563 p hg
    simpa only [d243, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d243, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1605 p hg
    simpa only [d243, d155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4565 (p : Pattern) (guard : d4117 p = 1) : d244 p ≤ (0 : Int) + d155 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d4117, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4462 p hg
    simpa only [d4117, d244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4566 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (0 : Int) + d9 p := by
  change (3 : Int) ≤ (0 : Int) + 9
  decide
theorem compare4567 (p : Pattern) (guard : d1 p = 1) : d115 p ≤ (0 : Int) + d23 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d115, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4566 p hg
    simpa only [d115, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d115, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d115, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4568 (p : Pattern) (guard : d1 p = 1) : d116 p ≤ (0 : Int) + d24 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d116, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4566 p hg
    simpa only [d116, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d116, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4567 p hg
    simpa only [d116, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4569 (p : Pattern) (guard : d1 p = 1) : d117 p ≤ (0 : Int) + d25 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d117, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4568 p hg
    simpa only [d117, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d117, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d117, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4570 (p : Pattern) (guard : d1 p = 1) : d132 p ≤ (0 : Int) + d26 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d132, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4568 p hg
    simpa only [d132, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d132, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4569 p hg
    simpa only [d132, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4571 (p : Pattern) (guard : d1 p = 1) : d132 p ≤ (0 : Int) + d27 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4570 p hg
    simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1596 p hg
    simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4572 (p : Pattern) (guard : d1 p = 1) : d245 p ≤ (0 : Int) + d247 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d245, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4571 p hg
    simpa only [d245, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d245, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1682 p hg
    simpa only [d245, d247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4573 (p : Pattern) (guard : d1 p = 1) : d246 p ≤ (0 : Int) + d248 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d246, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4572 p hg
    simpa only [d246, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d246, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1608 p hg
    simpa only [d246, d248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4574 (p : Pattern) (guard : d0 p = 1) : d248 p ≤ (0 : Int) + d248 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4575 (p : Pattern) (guard : d4117 p = 1) : d249 p ≤ (0 : Int) + d248 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4573 p hg
    simpa only [d4117, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4574 p hg
    simpa only [d4117, d249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4576 (p : Pattern) (guard : d4117 p = 1) : d250 p ≤ (0 : Int) + d4423 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d250, d4423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4565 p hg
    simpa only [d250, d4423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d250, d4423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4575 p hg
    simpa only [d250, d4423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4577 (p : Pattern) (guard : d4117 p = 1) : d251 p ≤ (0 : Int) + d4424 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d251, d4424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4561 p hg
    simpa only [d251, d4424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d251, d4424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4576 p hg
    simpa only [d251, d4424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4578 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (0 : Int) + d11 p := by
  change (1 : Int) ≤ (0 : Int) + 11
  decide
theorem compare4579 (p : Pattern) (guard : d1 p = 1) : d102 p ≤ (0 : Int) + d39 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d102, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4578 p hg
    simpa only [d102, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d102, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d102, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4580 (p : Pattern) (guard : d1 p = 1) : d103 p ≤ (0 : Int) + d40 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d103, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4578 p hg
    simpa only [d103, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d103, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4579 p hg
    simpa only [d103, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4581 (p : Pattern) (guard : d1 p = 1) : d104 p ≤ (0 : Int) + d41 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d104, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4580 p hg
    simpa only [d104, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d104, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d104, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4582 (p : Pattern) (guard : d1 p = 1) : d105 p ≤ (0 : Int) + d62 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d105, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4580 p hg
    simpa only [d105, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d105, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4581 p hg
    simpa only [d105, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4583 (p : Pattern) (guard : d1 p = 1) : d105 p ≤ (0 : Int) + d257 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4453 p hg
    simpa only [d257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4582 p hg
    simpa only [d257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4584 (p : Pattern) (guard : d1 p = 1) : d252 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1596 p hg
    simpa only [d252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare870 p hg
    simpa only [d252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4585 (p : Pattern) (guard : d1 p = 1) : d253 p ≤ (0 : Int) + d258 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d253, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4583 p hg
    simpa only [d253, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d253, d258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4584 p hg
    simpa only [d253, d258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4586 (p : Pattern) (guard : d1 p = 1) : d254 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1323 p hg
    simpa only [d254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare870 p hg
    simpa only [d254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4587 (p : Pattern) (guard : d1 p = 1) : d255 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4586 p hg
    simpa only [d255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare678 p hg
    simpa only [d255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4588 (p : Pattern) (guard : d1 p = 1) : d256 p ≤ (0 : Int) + d259 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d256, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4585 p hg
    simpa only [d256, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d256, d259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4587 p hg
    simpa only [d256, d259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4589 (p : Pattern) (guard : d0 p = 1) : d259 p ≤ (0 : Int) + d259 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4590 (p : Pattern) (guard : d4117 p = 1) : d260 p ≤ (0 : Int) + d259 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4588 p hg
    simpa only [d4117, d260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4589 p hg
    simpa only [d4117, d260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4591 (p : Pattern) (guard : d4117 p = 1) : d261 p ≤ (0 : Int) + d4425 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d261, d4425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4590 p hg
    simpa only [d261, d4425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d261, d4425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4575 p hg
    simpa only [d261, d4425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4592 (p : Pattern) (guard : d4117 p = 1) : d262 p ≤ (0 : Int) + d4426 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d262, d4426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4591 p hg
    simpa only [d262, d4426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d262, d4426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4444 p hg
    simpa only [d262, d4426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4593 (p : Pattern) (guard : d4117 p = 1) : d263 p ≤ (0 : Int) + d4427 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d263, d4427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4577 p hg
    simpa only [d263, d4427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d263, d4427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4592 p hg
    simpa only [d263, d4427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4594 (p : Pattern) (guard : d4117 p = 1) : d264 p ≤ (0 : Int) + d4428 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d264, d4428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4537 p hg
    simpa only [d264, d4428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d264, d4428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4593 p hg
    simpa only [d264, d4428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4595 (p : Pattern) (guard : d4117 p = 1) : d265 p ≤ (0 : Int) + d4429 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d265, d4429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4447 p hg
    simpa only [d265, d4429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d265, d4429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4594 p hg
    simpa only [d265, d4429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4596 (p : Pattern) (guard : d4117 p = 1) : d266 p ≤ (0 : Int) + d4430 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d266, d4430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4526 p hg
    simpa only [d266, d4430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d266, d4430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4595 p hg
    simpa only [d266, d4430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4597 (p : Pattern) (guard : d4117 p = 1) : d267 p ≤ (0 : Int) + d4431 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d267, d4431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4474 p hg
    simpa only [d267, d4431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d267, d4431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4596 p hg
    simpa only [d267, d4431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4598 (p : Pattern) (guard : d0 p = 1) : d81 p ≤ (0 : Int) + d396 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4599 (p : Pattern) (guard : d4117 p = 1) : d82 p ≤ (0 : Int) + d713 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d82, d713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare778 p hg
    simpa only [d4117, d82, d713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d82, d713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4598 p hg
    simpa only [d4117, d82, d713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4600 (p : Pattern) (guard : d0 p = 1) : d85 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4601 (p : Pattern) (guard : d4117 p = 1) : d86 p ≤ (0 : Int) + d714 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d86, d714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare805 p hg
    simpa only [d4117, d86, d714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d86, d714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4600 p hg
    simpa only [d4117, d86, d714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4602 (p : Pattern) (guard : d4117 p = 1) : d87 p ≤ (0 : Int) + d715 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d87, d715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4599 p hg
    simpa only [d87, d715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d87, d715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4601 p hg
    simpa only [d87, d715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4603 (p : Pattern) (guard : d4117 p = 1) : d88 p ≤ (0 : Int) + d716 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d88, d716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2787 p hg
    simpa only [d88, d716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d88, d716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4602 p hg
    simpa only [d88, d716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4604 (p : Pattern) (guard : d0 p = 1) : d81 p ≤ (0 : Int) + d405 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4605 (p : Pattern) (guard : d4117 p = 1) : d82 p ≤ (0 : Int) + d717 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d82, d717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare778 p hg
    simpa only [d4117, d82, d717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d82, d717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4604 p hg
    simpa only [d4117, d82, d717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4606 (p : Pattern) (guard : d4117 p = 1) : d87 p ≤ (0 : Int) + d718 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d87, d718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4605 p hg
    simpa only [d87, d718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d87, d718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4601 p hg
    simpa only [d87, d718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4607 (p : Pattern) (guard : d1 p = 1) : d92 p ≤ (0 : Int) + d92 p := by
  omega
theorem compare4608 (p : Pattern) (guard : d0 p = 1) : d93 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4609 (p : Pattern) (guard : d4117 p = 1) : d94 p ≤ (0 : Int) + d719 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d94, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4607 p hg
    simpa only [d4117, d94, d719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d94, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4608 p hg
    simpa only [d4117, d94, d719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4610 (p : Pattern) (guard : d4117 p = 1) : d95 p ≤ (0 : Int) + d95 p := by
  omega
theorem compare4611 (p : Pattern) (guard : d4117 p = 1) : d96 p ≤ (0 : Int) + d720 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d96, d720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4609 p hg
    simpa only [d96, d720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d96, d720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4610 p hg
    simpa only [d96, d720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4612 (p : Pattern) (guard : d4117 p = 1) : d97 p ≤ (0 : Int) + d721 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d97, d721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4606 p hg
    simpa only [d97, d721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d97, d721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4611 p hg
    simpa only [d97, d721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4613 (p : Pattern) (guard : d4117 p = 1) : d98 p ≤ (0 : Int) + d722 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d98, d722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4603 p hg
    simpa only [d98, d722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d98, d722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4612 p hg
    simpa only [d98, d722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4614 (p : Pattern) (guard : d0 p = 1) : d81 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4615 (p : Pattern) (guard : d4117 p = 1) : d82 p ≤ (0 : Int) + d726 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d82, d726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare778 p hg
    simpa only [d4117, d82, d726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d82, d726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4614 p hg
    simpa only [d4117, d82, d726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4616 (p : Pattern) (guard : d4117 p = 1) : d87 p ≤ (0 : Int) + d727 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d87, d727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4615 p hg
    simpa only [d87, d727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d87, d727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4601 p hg
    simpa only [d87, d727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4617 (p : Pattern) (guard : d4117 p = 1) : d88 p ≤ (0 : Int) + d728 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d88, d728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2802 p hg
    simpa only [d88, d728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d88, d728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4616 p hg
    simpa only [d88, d728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4618 (p : Pattern) (guard : d4117 p = 1) : d99 p ≤ (0 : Int) + d729 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d99, d729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4616 p hg
    simpa only [d99, d729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d99, d729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4444 p hg
    simpa only [d99, d729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4619 (p : Pattern) (guard : d4117 p = 1) : d100 p ≤ (0 : Int) + d730 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d100, d730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4617 p hg
    simpa only [d100, d730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d100, d730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4618 p hg
    simpa only [d100, d730, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
