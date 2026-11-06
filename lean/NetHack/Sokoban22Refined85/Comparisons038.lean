/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons037
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare5320 (p : Pattern) (guard : d4206 p = 1) : d259 p ≤ (0 : Int) + d1673 p := by
  cases selected : p 161 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d259, d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5319 p hg
    simpa only [d259, d1673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d259, d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d259, d1673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5321 (p : Pattern) (guard : d4206 p = 1) : d260 p ≤ (0 : Int) + d1674 p := by
  cases selected : p 160 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d260, d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5317 p hg
    simpa only [d260, d1674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d260, d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5320 p hg
    simpa only [d260, d1674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5322 (p : Pattern) (guard : d4206 p = 1) : d261 p ≤ (0 : Int) + d1675 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d261, d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5321 p hg
    simpa only [d261, d1675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d261, d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5310 p hg
    simpa only [d261, d1675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5323 (p : Pattern) (guard : d4206 p = 1) : d262 p ≤ (0 : Int) + d1676 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d262, d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5322 p hg
    simpa only [d262, d1676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d262, d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2927 p hg
    simpa only [d262, d1676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5324 (p : Pattern) (guard : d4206 p = 1) : d263 p ≤ (0 : Int) + d1677 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d263, d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5312 p hg
    simpa only [d263, d1677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d263, d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5323 p hg
    simpa only [d263, d1677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5325 (p : Pattern) (guard : d4206 p = 1) : d264 p ≤ (0 : Int) + d1678 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d264, d1678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5286 p hg
    simpa only [d264, d1678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d264, d1678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5324 p hg
    simpa only [d264, d1678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5326 (p : Pattern) (guard : d4206 p = 1) : d265 p ≤ (0 : Int) + d1679 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d265, d1679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5136 p hg
    simpa only [d265, d1679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d265, d1679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5325 p hg
    simpa only [d265, d1679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5327 (p : Pattern) (guard : d4206 p = 1) : d266 p ≤ (0 : Int) + d1680 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d266, d1680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5269 p hg
    simpa only [d266, d1680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d266, d1680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5326 p hg
    simpa only [d266, d1680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5328 (p : Pattern) (guard : d4206 p = 1) : d267 p ≤ (0 : Int) + d1681 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4206 p = 1 := by simpa only [d267, d1681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5231 p hg
    simpa only [d267, d1681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4206 p = 1 := by simpa only [d267, d1681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5327 p hg
    simpa only [d267, d1681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5329 (p : Pattern) (guard : d0 p = 1) : d376 p ≤ (0 : Int) + d51 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5330 (p : Pattern) (guard : d4117 p = 1) : d710 p ≤ (0 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d710, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare778 p hg
    simpa only [d4117, d710, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d710, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5329 p hg
    simpa only [d4117, d710, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5331 (p : Pattern) (guard : d0 p = 1) : d391 p ≤ (0 : Int) + d75 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5332 (p : Pattern) (guard : d4117 p = 1) : d711 p ≤ (0 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d711, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare805 p hg
    simpa only [d4117, d711, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d711, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5331 p hg
    simpa only [d4117, d711, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5333 (p : Pattern) (guard : d4117 p = 1) : d712 p ≤ (0 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d712, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5330 p hg
    simpa only [d712, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d712, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5332 p hg
    simpa only [d712, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5334 (p : Pattern) (guard : d0 p = 1) : d715 p ≤ (0 : Int) + d400 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5335 (p : Pattern) (guard : d4203 p = 1) : d716 p ≤ (0 : Int) + d517 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d716, d517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5333 p hg
    simpa only [d4203, d716, d517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d716, d517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5334 p hg
    simpa only [d4203, d716, d517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5336 (p : Pattern) (guard : d0 p = 1) : d405 p ≤ (0 : Int) + d530 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5337 (p : Pattern) (guard : d4117 p = 1) : d717 p ≤ (0 : Int) + d531 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d717, d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare778 p hg
    simpa only [d4117, d717, d531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d717, d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5336 p hg
    simpa only [d4117, d717, d531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5338 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d541 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5339 (p : Pattern) (guard : d4117 p = 1) : d714 p ≤ (0 : Int) + d542 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d714, d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare805 p hg
    simpa only [d4117, d714, d542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d714, d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5338 p hg
    simpa only [d4117, d714, d542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5340 (p : Pattern) (guard : d4117 p = 1) : d718 p ≤ (0 : Int) + d543 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d718, d543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5337 p hg
    simpa only [d718, d543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d718, d543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5339 p hg
    simpa only [d718, d543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5341 (p : Pattern) (guard : d0 p = 1) : d720 p ≤ (0 : Int) + d412 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5342 (p : Pattern) (guard : d4203 p = 1) : d721 p ≤ (0 : Int) + d544 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d721, d544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5340 p hg
    simpa only [d4203, d721, d544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d721, d544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5341 p hg
    simpa only [d4203, d721, d544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5343 (p : Pattern) (guard : d4203 p = 1) : d722 p ≤ (0 : Int) + d545 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d722, d545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5335 p hg
    simpa only [d722, d545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d722, d545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5342 p hg
    simpa only [d722, d545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5344 (p : Pattern) (guard : d0 p = 1) : d409 p ≤ (0 : Int) + d51 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5345 (p : Pattern) (guard : d4117 p = 1) : d723 p ≤ (0 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d723, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare778 p hg
    simpa only [d4117, d723, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d723, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5344 p hg
    simpa only [d4117, d723, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5346 (p : Pattern) (guard : d0 p = 1) : d396 p ≤ (0 : Int) + d75 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5347 (p : Pattern) (guard : d4117 p = 1) : d724 p ≤ (0 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d724, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare805 p hg
    simpa only [d4117, d724, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d724, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5346 p hg
    simpa only [d4117, d724, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5348 (p : Pattern) (guard : d4117 p = 1) : d725 p ≤ (0 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d725, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5345 p hg
    simpa only [d725, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d725, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5347 p hg
    simpa only [d725, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5349 (p : Pattern) (guard : d0 p = 1) : d727 p ≤ (0 : Int) + d422 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5350 (p : Pattern) (guard : d4203 p = 1) : d728 p ≤ (0 : Int) + d546 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d728, d546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5348 p hg
    simpa only [d4203, d728, d546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d728, d546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5349 p hg
    simpa only [d4203, d728, d546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5351 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d530 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5352 (p : Pattern) (guard : d4117 p = 1) : d726 p ≤ (0 : Int) + d531 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d726, d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare778 p hg
    simpa only [d4117, d726, d531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d726, d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5351 p hg
    simpa only [d4117, d726, d531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5353 (p : Pattern) (guard : d4117 p = 1) : d727 p ≤ (0 : Int) + d543 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d727, d543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5352 p hg
    simpa only [d727, d543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d727, d543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5339 p hg
    simpa only [d727, d543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5354 (p : Pattern) (guard : d4203 p = 1) : d729 p ≤ (0 : Int) + d547 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d729, d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5353 p hg
    simpa only [d4203, d729, d547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d729, d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4203, d729, d547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5355 (p : Pattern) (guard : d4203 p = 1) : d730 p ≤ (0 : Int) + d548 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d730, d548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5350 p hg
    simpa only [d730, d548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d730, d548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5354 p hg
    simpa only [d730, d548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5356 (p : Pattern) (guard : d4203 p = 1) : d731 p ≤ (0 : Int) + d549 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d731, d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5343 p hg
    simpa only [d731, d549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d731, d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5355 p hg
    simpa only [d731, d549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5357 (p : Pattern) (guard : d0 p = 1) : d398 p ≤ (0 : Int) + d51 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5358 (p : Pattern) (guard : d4117 p = 1) : d732 p ≤ (0 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d732, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare778 p hg
    simpa only [d4117, d732, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d732, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5357 p hg
    simpa only [d4117, d732, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5359 (p : Pattern) (guard : d0 p = 1) : d409 p ≤ (0 : Int) + d75 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5360 (p : Pattern) (guard : d4117 p = 1) : d733 p ≤ (0 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d733, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare805 p hg
    simpa only [d4117, d733, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d733, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5359 p hg
    simpa only [d4117, d733, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5361 (p : Pattern) (guard : d4117 p = 1) : d734 p ≤ (0 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d734, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5358 p hg
    simpa only [d734, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d734, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5360 p hg
    simpa only [d734, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5362 (p : Pattern) (guard : d0 p = 1) : d727 p ≤ (0 : Int) + d439 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5363 (p : Pattern) (guard : d4203 p = 1) : d735 p ≤ (0 : Int) + d550 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d735, d550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5361 p hg
    simpa only [d4203, d735, d550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d735, d550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5362 p hg
    simpa only [d4203, d735, d550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5364 (p : Pattern) (guard : d0 p = 1) : d396 p ≤ (0 : Int) + d530 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5365 (p : Pattern) (guard : d4117 p = 1) : d713 p ≤ (0 : Int) + d531 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d713, d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare778 p hg
    simpa only [d4117, d713, d531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d713, d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5364 p hg
    simpa only [d4117, d713, d531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5366 (p : Pattern) (guard : d4117 p = 1) : d715 p ≤ (0 : Int) + d543 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d715, d543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5365 p hg
    simpa only [d715, d543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d715, d543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5339 p hg
    simpa only [d715, d543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5367 (p : Pattern) (guard : d0 p = 1) : d720 p ≤ (0 : Int) + d441 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5368 (p : Pattern) (guard : d4203 p = 1) : d736 p ≤ (0 : Int) + d551 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d736, d551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5366 p hg
    simpa only [d4203, d736, d551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d736, d551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5367 p hg
    simpa only [d4203, d736, d551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5369 (p : Pattern) (guard : d4203 p = 1) : d737 p ≤ (0 : Int) + d552 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d737, d552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5363 p hg
    simpa only [d737, d552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d737, d552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5368 p hg
    simpa only [d737, d552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5370 (p : Pattern) (guard : d0 p = 1) : d405 p ≤ (0 : Int) + d51 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5371 (p : Pattern) (guard : d4117 p = 1) : d717 p ≤ (0 : Int) + d52 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d717, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare778 p hg
    simpa only [d4117, d717, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d717, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5370 p hg
    simpa only [d4117, d717, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5372 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d75 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5373 (p : Pattern) (guard : d4117 p = 1) : d714 p ≤ (0 : Int) + d76 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d714, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare805 p hg
    simpa only [d4117, d714, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d714, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5372 p hg
    simpa only [d4117, d714, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5374 (p : Pattern) (guard : d4117 p = 1) : d718 p ≤ (0 : Int) + d77 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d718, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5371 p hg
    simpa only [d718, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d718, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5373 p hg
    simpa only [d718, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5375 (p : Pattern) (guard : d0 p = 1) : d727 p ≤ (0 : Int) + d412 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5376 (p : Pattern) (guard : d4203 p = 1) : d738 p ≤ (0 : Int) + d553 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d738, d553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5374 p hg
    simpa only [d4203, d738, d553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d738, d553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5375 p hg
    simpa only [d4203, d738, d553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5377 (p : Pattern) (guard : d4203 p = 1) : d739 p ≤ (0 : Int) + d554 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d739, d554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5376 p hg
    simpa only [d739, d554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d739, d554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5354 p hg
    simpa only [d739, d554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5378 (p : Pattern) (guard : d4203 p = 1) : d740 p ≤ (0 : Int) + d555 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d740, d555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5369 p hg
    simpa only [d740, d555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d740, d555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5377 p hg
    simpa only [d740, d555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5379 (p : Pattern) (guard : d4203 p = 1) : d741 p ≤ (0 : Int) + d556 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d741, d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5356 p hg
    simpa only [d741, d556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d741, d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5378 p hg
    simpa only [d741, d556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5380 (p : Pattern) (guard : d0 p = 1) : d398 p ≤ (0 : Int) + d130 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5381 (p : Pattern) (guard : d4117 p = 1) : d742 p ≤ (0 : Int) + d131 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d742, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1396 p hg
    simpa only [d4117, d742, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d742, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5380 p hg
    simpa only [d4117, d742, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5382 (p : Pattern) (guard : d0 p = 1) : d409 p ≤ (0 : Int) + d145 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5383 (p : Pattern) (guard : d4117 p = 1) : d743 p ≤ (0 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d743, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1570 p hg
    simpa only [d4117, d743, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d743, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5382 p hg
    simpa only [d4117, d743, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5384 (p : Pattern) (guard : d4117 p = 1) : d744 p ≤ (0 : Int) + d147 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d744, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5381 p hg
    simpa only [d744, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d744, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5383 p hg
    simpa only [d744, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5385 (p : Pattern) (guard : d0 p = 1) : d747 p ≤ (0 : Int) + d439 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5386 (p : Pattern) (guard : d4203 p = 1) : d748 p ≤ (0 : Int) + d557 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d748, d557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5384 p hg
    simpa only [d4203, d748, d557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d748, d557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5385 p hg
    simpa only [d4203, d748, d557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5387 (p : Pattern) (guard : d0 p = 1) : d396 p ≤ (0 : Int) + d568 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5388 (p : Pattern) (guard : d4117 p = 1) : d749 p ≤ (0 : Int) + d569 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d749, d569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1396 p hg
    simpa only [d4117, d749, d569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d749, d569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5387 p hg
    simpa only [d4117, d749, d569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5389 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d577 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5390 (p : Pattern) (guard : d4117 p = 1) : d746 p ≤ (0 : Int) + d578 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d746, d578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1570 p hg
    simpa only [d4117, d746, d578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d746, d578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5389 p hg
    simpa only [d4117, d746, d578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5391 (p : Pattern) (guard : d4117 p = 1) : d750 p ≤ (0 : Int) + d579 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d750, d579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5388 p hg
    simpa only [d750, d579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d750, d579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5390 p hg
    simpa only [d750, d579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5392 (p : Pattern) (guard : d4203 p = 1) : d751 p ≤ (0 : Int) + d580 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d751, d580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5391 p hg
    simpa only [d4203, d751, d580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d751, d580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4994 p hg
    simpa only [d4203, d751, d580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5393 (p : Pattern) (guard : d4203 p = 1) : d752 p ≤ (0 : Int) + d581 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d752, d581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5386 p hg
    simpa only [d752, d581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d752, d581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5392 p hg
    simpa only [d752, d581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5394 (p : Pattern) (guard : d0 p = 1) : d405 p ≤ (0 : Int) + d130 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5395 (p : Pattern) (guard : d4117 p = 1) : d753 p ≤ (0 : Int) + d131 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d753, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1396 p hg
    simpa only [d4117, d753, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d753, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5394 p hg
    simpa only [d4117, d753, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5396 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d145 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5397 (p : Pattern) (guard : d4117 p = 1) : d746 p ≤ (0 : Int) + d146 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d746, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1570 p hg
    simpa only [d4117, d746, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d746, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5396 p hg
    simpa only [d4117, d746, d146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5398 (p : Pattern) (guard : d4117 p = 1) : d754 p ≤ (0 : Int) + d147 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d754, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5395 p hg
    simpa only [d754, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d754, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5397 p hg
    simpa only [d754, d147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5399 (p : Pattern) (guard : d0 p = 1) : d747 p ≤ (0 : Int) + d412 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5400 (p : Pattern) (guard : d4203 p = 1) : d755 p ≤ (0 : Int) + d582 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d755, d582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5398 p hg
    simpa only [d4203, d755, d582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d755, d582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5399 p hg
    simpa only [d4203, d755, d582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5401 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d568 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5402 (p : Pattern) (guard : d4117 p = 1) : d745 p ≤ (0 : Int) + d569 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d745, d569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1396 p hg
    simpa only [d4117, d745, d569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d745, d569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5401 p hg
    simpa only [d4117, d745, d569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5403 (p : Pattern) (guard : d4117 p = 1) : d747 p ≤ (0 : Int) + d579 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d747, d579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5402 p hg
    simpa only [d747, d579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d747, d579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5390 p hg
    simpa only [d747, d579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5404 (p : Pattern) (guard : d4203 p = 1) : d756 p ≤ (0 : Int) + d583 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d756, d583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5403 p hg
    simpa only [d4203, d756, d583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d756, d583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4203, d756, d583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5405 (p : Pattern) (guard : d4203 p = 1) : d757 p ≤ (0 : Int) + d584 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d757, d584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5400 p hg
    simpa only [d757, d584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d757, d584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5404 p hg
    simpa only [d757, d584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5406 (p : Pattern) (guard : d4203 p = 1) : d758 p ≤ (0 : Int) + d585 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d758, d585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5393 p hg
    simpa only [d758, d585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d758, d585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5405 p hg
    simpa only [d758, d585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5407 (p : Pattern) (guard : d4203 p = 1) : d759 p ≤ (0 : Int) + d586 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d759, d586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5356 p hg
    simpa only [d759, d586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d759, d586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5406 p hg
    simpa only [d759, d586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5408 (p : Pattern) (guard : d4203 p = 1) : d760 p ≤ (0 : Int) + d587 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d760, d587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5379 p hg
    simpa only [d760, d587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d760, d587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5407 p hg
    simpa only [d760, d587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5409 (p : Pattern) (guard : d0 p = 1) : d763 p ≤ (0 : Int) + d412 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5410 (p : Pattern) (guard : d4203 p = 1) : d764 p ≤ (0 : Int) + d553 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d764, d553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5374 p hg
    simpa only [d4203, d764, d553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d764, d553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5409 p hg
    simpa only [d4203, d764, d553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5411 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d595 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5412 (p : Pattern) (guard : d4117 p = 1) : d761 p ≤ (0 : Int) + d596 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d761, d596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2866 p hg
    simpa only [d4117, d761, d596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d761, d596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5411 p hg
    simpa only [d4117, d761, d596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5413 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d603 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5414 (p : Pattern) (guard : d4117 p = 1) : d762 p ≤ (0 : Int) + d604 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d762, d604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2869 p hg
    simpa only [d4117, d762, d604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d762, d604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5413 p hg
    simpa only [d4117, d762, d604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5415 (p : Pattern) (guard : d4117 p = 1) : d763 p ≤ (0 : Int) + d605 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d763, d605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5412 p hg
    simpa only [d763, d605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d763, d605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5414 p hg
    simpa only [d763, d605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5416 (p : Pattern) (guard : d4203 p = 1) : d765 p ≤ (0 : Int) + d606 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d765, d606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5415 p hg
    simpa only [d4203, d765, d606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d765, d606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4203, d765, d606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5417 (p : Pattern) (guard : d4203 p = 1) : d766 p ≤ (0 : Int) + d607 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d766, d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5410 p hg
    simpa only [d766, d607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d766, d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5416 p hg
    simpa only [d766, d607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5418 (p : Pattern) (guard : d4203 p = 1) : d767 p ≤ (0 : Int) + d608 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d767, d608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5369 p hg
    simpa only [d767, d608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d767, d608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5417 p hg
    simpa only [d767, d608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5419 (p : Pattern) (guard : d4203 p = 1) : d768 p ≤ (0 : Int) + d609 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d768, d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5356 p hg
    simpa only [d768, d609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d768, d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5418 p hg
    simpa only [d768, d609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5420 (p : Pattern) (guard : d0 p = 1) : d409 p ≤ (0 : Int) + d218 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5421 (p : Pattern) (guard : d4117 p = 1) : d769 p ≤ (0 : Int) + d219 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d769, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1411 p hg
    simpa only [d4117, d769, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d769, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5420 p hg
    simpa only [d4117, d769, d219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5422 (p : Pattern) (guard : d4117 p = 1) : d770 p ≤ (0 : Int) + d220 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d770, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5381 p hg
    simpa only [d770, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d770, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5421 p hg
    simpa only [d770, d220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5423 (p : Pattern) (guard : d0 p = 1) : d772 p ≤ (0 : Int) + d457 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5424 (p : Pattern) (guard : d4203 p = 1) : d773 p ≤ (0 : Int) + d610 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d773, d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5422 p hg
    simpa only [d4203, d773, d610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d773, d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5423 p hg
    simpa only [d4203, d773, d610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5425 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d614 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5426 (p : Pattern) (guard : d4117 p = 1) : d771 p ≤ (0 : Int) + d615 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d771, d615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1411 p hg
    simpa only [d4117, d771, d615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d771, d615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5425 p hg
    simpa only [d4117, d771, d615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5427 (p : Pattern) (guard : d4117 p = 1) : d774 p ≤ (0 : Int) + d616 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d774, d616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5388 p hg
    simpa only [d774, d616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d774, d616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5426 p hg
    simpa only [d774, d616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5428 (p : Pattern) (guard : d4203 p = 1) : d775 p ≤ (0 : Int) + d617 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d775, d617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5427 p hg
    simpa only [d4203, d775, d617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d775, d617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4994 p hg
    simpa only [d4203, d775, d617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5429 (p : Pattern) (guard : d4203 p = 1) : d776 p ≤ (0 : Int) + d618 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d776, d618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5424 p hg
    simpa only [d776, d618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d776, d618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5428 p hg
    simpa only [d776, d618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5430 (p : Pattern) (guard : d0 p = 1) : d405 p ≤ (0 : Int) + d280 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5431 (p : Pattern) (guard : d4117 p = 1) : d753 p ≤ (0 : Int) + d281 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d753, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1396 p hg
    simpa only [d4117, d753, d281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d753, d281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5430 p hg
    simpa only [d4117, d753, d281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5432 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d288 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5433 (p : Pattern) (guard : d4117 p = 1) : d771 p ≤ (0 : Int) + d289 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d771, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1411 p hg
    simpa only [d4117, d771, d289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d771, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5432 p hg
    simpa only [d4117, d771, d289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5434 (p : Pattern) (guard : d4117 p = 1) : d777 p ≤ (0 : Int) + d290 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d777, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5431 p hg
    simpa only [d777, d290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d777, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5433 p hg
    simpa only [d777, d290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5435 (p : Pattern) (guard : d0 p = 1) : d780 p ≤ (0 : Int) + d473 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5436 (p : Pattern) (guard : d4203 p = 1) : d781 p ≤ (0 : Int) + d619 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d781, d619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5434 p hg
    simpa only [d4203, d781, d619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d781, d619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5435 p hg
    simpa only [d4203, d781, d619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5437 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d630 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5438 (p : Pattern) (guard : d4117 p = 1) : d782 p ≤ (0 : Int) + d631 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d782, d631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2894 p hg
    simpa only [d4117, d782, d631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d782, d631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5437 p hg
    simpa only [d4117, d782, d631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5439 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d644 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5440 (p : Pattern) (guard : d4117 p = 1) : d779 p ≤ (0 : Int) + d645 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d779, d645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2897 p hg
    simpa only [d4117, d779, d645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d779, d645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5439 p hg
    simpa only [d4117, d779, d645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5441 (p : Pattern) (guard : d4117 p = 1) : d783 p ≤ (0 : Int) + d646 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d783, d646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5438 p hg
    simpa only [d783, d646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d783, d646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5440 p hg
    simpa only [d783, d646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5442 (p : Pattern) (guard : d4203 p = 1) : d784 p ≤ (0 : Int) + d647 p := by
  cases selected : p 138 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d4203, d784, d647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5441 p hg
    simpa only [d4203, d784, d647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4203, d784, d647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d4203, d784, d647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5443 (p : Pattern) (guard : d4203 p = 1) : d785 p ≤ (0 : Int) + d648 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d785, d648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5436 p hg
    simpa only [d785, d648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d785, d648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5442 p hg
    simpa only [d785, d648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5444 (p : Pattern) (guard : d4203 p = 1) : d786 p ≤ (0 : Int) + d649 p := by
  cases selected : p 115 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d786, d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5429 p hg
    simpa only [d786, d649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d786, d649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5443 p hg
    simpa only [d786, d649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5445 (p : Pattern) (guard : d4203 p = 1) : d787 p ≤ (0 : Int) + d650 p := by
  cases selected : p 71 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d787, d650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5356 p hg
    simpa only [d787, d650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d787, d650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5444 p hg
    simpa only [d787, d650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5446 (p : Pattern) (guard : d4203 p = 1) : d788 p ≤ (0 : Int) + d651 p := by
  cases selected : p 49 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d788, d651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5419 p hg
    simpa only [d788, d651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d788, d651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5445 p hg
    simpa only [d788, d651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5447 (p : Pattern) (guard : d4203 p = 1) : d789 p ≤ (0 : Int) + d652 p := by
  cases selected : p 48 with
  | false =>
    have hg : d4203 p = 1 := by simpa only [d789, d652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5408 p hg
    simpa only [d789, d652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4203 p = 1 := by simpa only [d789, d652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5446 p hg
    simpa only [d789, d652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5448 (p : Pattern) (guard : d0 p = 1) : d712 p ≤ (2 : Int) + d543 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5449 (p : Pattern) (guard : d1 p = 1) : d29 p ≤ (2 : Int) + d29 p := by
  omega
theorem compare5450 (p : Pattern) (guard : d0 p = 1) : d396 p ≤ (2 : Int) + d530 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5451 (p : Pattern) (guard : d4117 p = 1) : d713 p ≤ (2 : Int) + d531 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d713, d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5449 p hg
    simpa only [d4117, d713, d531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d713, d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5450 p hg
    simpa only [d4117, d713, d531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5452 (p : Pattern) (guard : d1 p = 1) : d65 p ≤ (2 : Int) + d65 p := by
  omega
theorem compare5453 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (2 : Int) + d541 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5454 (p : Pattern) (guard : d4117 p = 1) : d714 p ≤ (2 : Int) + d542 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4117, d714, d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5452 p hg
    simpa only [d4117, d714, d542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4117, d714, d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5453 p hg
    simpa only [d4117, d714, d542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5455 (p : Pattern) (guard : d4117 p = 1) : d715 p ≤ (2 : Int) + d543 p := by
  cases selected : p 141 with
  | false =>
    have hg : d4117 p = 1 := by simpa only [d715, d543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5451 p hg
    simpa only [d715, d543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d715, d543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5454 p hg
    simpa only [d715, d543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5456 (p : Pattern) (guard : d4118 p = 1) : d716 p ≤ (2 : Int) + d543 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4118, d716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5448 p hg
    simpa only [d4118, d716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4117 p = 1 := by simpa only [d4118, d716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5455 p hg
    simpa only [d4118, d716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5457 (p : Pattern) (guard : d0 p = 1) : d721 p ≤ (2 : Int) + d543 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5458 (p : Pattern) (guard : d4119 p = 1) : d722 p ≤ (2 : Int) + d543 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4118 p = 1 := by simpa only [d4119, d722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5456 p hg
    simpa only [d4119, d722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4119, d722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5457 p hg
    simpa only [d4119, d722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5459 (p : Pattern) (guard : d0 p = 1) : d725 p ≤ (2 : Int) + d543 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban22Refined85
