import NetHack.Soko22Hazard87.Compare019
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare5000 (p : Pattern) (guard : d5377 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d5376 p = 1 := by simpa only [d5377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4999 p hg
    simpa only [d5377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d5377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5001 (p : Pattern) (guard : d5378 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d5377 p = 1 := by simpa only [d5378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5000 p hg
    simpa only [d5378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d5378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5002 (p : Pattern) (guard : d5379 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d5378 p = 1 := by simpa only [d5379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5001 p hg
    simpa only [d5379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d5379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5003 (p : Pattern) (guard : d82051 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d82050 p = 1 := by simpa only [d82051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4996 p hg
    simpa only [d82051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5379 p = 1 := by simpa only [d82051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5002 p hg
    simpa only [d82051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5004 (p : Pattern) (guard : d82052 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d82052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82051 p = 1 := by simpa only [d82052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5003 p hg
    simpa only [d82052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5005 (p : Pattern) (guard : d82053 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d82053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82052 p = 1 := by simpa only [d82053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5004 p hg
    simpa only [d82053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5006 (p : Pattern) (guard : d82054 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82054, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d82054, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82053 p = 1 := by simpa only [d82054, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5005 p hg
    simpa only [d82054, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5007 (p : Pattern) (guard : d82055 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4515 p hg
    simpa only [d82055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82054 p = 1 := by simpa only [d82055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5006 p hg
    simpa only [d82055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5008 (p : Pattern) (guard : d458 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d84 p = 1 := by simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4575 p hg
    simpa only [d458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5009 (p : Pattern) (guard : d459 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d458 p = 1 := by simpa only [d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5008 p hg
    simpa only [d459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5010 (p : Pattern) (guard : d460 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d459 p = 1 := by simpa only [d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5009 p hg
    simpa only [d460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5011 (p : Pattern) (guard : d461 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d460 p = 1 := by simpa only [d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5010 p hg
    simpa only [d461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5012 (p : Pattern) (guard : d462 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d462, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d462, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d461 p = 1 := by simpa only [d462, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5011 p hg
    simpa only [d462, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5013 (p : Pattern) (guard : d463 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4515 p hg
    simpa only [d463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d462 p = 1 := by simpa only [d463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5012 p hg
    simpa only [d463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5014 (p : Pattern) (guard : d82056 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 69 with
  | false =>
    have hg : d82055 p = 1 := by simpa only [d82056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5007 p hg
    simpa only [d82056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d463 p = 1 := by simpa only [d82056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5013 p hg
    simpa only [d82056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5015 (p : Pattern) (guard : d82057 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 51 with
  | false =>
    have hg : d82056 p = 1 := by simpa only [d82057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5014 p hg
    simpa only [d82057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4515 p hg
    simpa only [d82057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5016 (p : Pattern) (guard : d82058 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 50 with
  | false =>
    have hg : d82057 p = 1 := by simpa only [d82058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5015 p hg
    simpa only [d82058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4515 p hg
    simpa only [d82058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5017 (p : Pattern) (guard : d82059 p = 1) : d47865 p ≤ (-1 : Int) + d98795 p := by
  cases selected : p 49 with
  | false =>
    have hg : d82058 p = 1 := by simpa only [d82059, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5016 p hg
    simpa only [d82059, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82059, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4585 p hg
    simpa only [d82059, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5018 (p : Pattern) (guard : d82060 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 48 with
  | false =>
    have hg : d82049 p = 1 := by simpa only [d82060, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4942 p hg
    simpa only [d82060, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82059 p = 1 := by simpa only [d82060, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5017 p hg
    simpa only [d82060, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5019 (p : Pattern) (guard : d82061 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82060 p = 1 := by simpa only [d82061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5018 p hg
    simpa only [d82061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5020 (p : Pattern) (guard : d82062 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82061 p = 1 := by simpa only [d82062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5019 p hg
    simpa only [d82062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5021 (p : Pattern) (guard : d82063 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82062 p = 1 := by simpa only [d82063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5020 p hg
    simpa only [d82063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5022 (p : Pattern) (guard : d82064 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82063 p = 1 := by simpa only [d82064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5021 p hg
    simpa only [d82064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5023 (p : Pattern) (guard : d82065 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82064 p = 1 := by simpa only [d82065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5022 p hg
    simpa only [d82065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5024 (p : Pattern) (guard : d82066 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d51657 p = 1 := by simpa only [d82066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4783 p hg
    simpa only [d82066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82065 p = 1 := by simpa only [d82066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5023 p hg
    simpa only [d82066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5025 (p : Pattern) (guard : d476 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d328 p = 1 := by simpa only [d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4833 p hg
    simpa only [d476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d475 p = 1 := by simpa only [d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4838 p hg
    simpa only [d476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5026 (p : Pattern) (guard : d477 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d476 p = 1 := by simpa only [d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5025 p hg
    simpa only [d477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5027 (p : Pattern) (guard : d478 p = 1) : d47699 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d477 p = 1 := by simpa only [d478, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5026 p hg
    simpa only [d478, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d478, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4436 p hg
    simpa only [d478, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5028 (p : Pattern) (guard : d479 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d479, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d479, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d478 p = 1 := by simpa only [d479, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5027 p hg
    simpa only [d479, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5029 (p : Pattern) (guard : d480 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d475 p = 1 := by simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4838 p hg
    simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5030 (p : Pattern) (guard : d481 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d480 p = 1 := by simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5029 p hg
    simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5031 (p : Pattern) (guard : d482 p = 1) : d47699 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d481 p = 1 := by simpa only [d482, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5030 p hg
    simpa only [d482, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d482, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4436 p hg
    simpa only [d482, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5032 (p : Pattern) (guard : d483 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d483, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d483, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d482 p = 1 := by simpa only [d483, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5031 p hg
    simpa only [d483, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5033 (p : Pattern) (guard : d484 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d479 p = 1 := by simpa only [d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5028 p hg
    simpa only [d484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d483 p = 1 := by simpa only [d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5032 p hg
    simpa only [d484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5034 (p : Pattern) (guard : d485 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d484 p = 1 := by simpa only [d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5033 p hg
    simpa only [d485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5035 (p : Pattern) (guard : d486 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d485 p = 1 := by simpa only [d486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5034 p hg
    simpa only [d486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5036 (p : Pattern) (guard : d487 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d486 p = 1 := by simpa only [d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5035 p hg
    simpa only [d487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5037 (p : Pattern) (guard : d488 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d483 p = 1 := by simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5032 p hg
    simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5038 (p : Pattern) (guard : d489 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d488 p = 1 := by simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5037 p hg
    simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5039 (p : Pattern) (guard : d490 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d489 p = 1 := by simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5038 p hg
    simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5040 (p : Pattern) (guard : d491 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d490 p = 1 := by simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5039 p hg
    simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5041 (p : Pattern) (guard : d492 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d487 p = 1 := by simpa only [d492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5036 p hg
    simpa only [d492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d491 p = 1 := by simpa only [d492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5040 p hg
    simpa only [d492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5042 (p : Pattern) (guard : d493 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d492 p = 1 := by simpa only [d493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5041 p hg
    simpa only [d493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5043 (p : Pattern) (guard : d494 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d493 p = 1 := by simpa only [d494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5042 p hg
    simpa only [d494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5044 (p : Pattern) (guard : d495 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d494 p = 1 := by simpa only [d495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5043 p hg
    simpa only [d495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5045 (p : Pattern) (guard : d496 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d495 p = 1 := by simpa only [d496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5044 p hg
    simpa only [d496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5046 (p : Pattern) (guard : d497 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d496 p = 1 := by simpa only [d497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5045 p hg
    simpa only [d497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5047 (p : Pattern) (guard : d498 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d497 p = 1 := by simpa only [d498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5046 p hg
    simpa only [d498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5048 (p : Pattern) (guard : d499 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 69 with
  | false =>
    have hg : d498 p = 1 := by simpa only [d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5047 p hg
    simpa only [d499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5049 (p : Pattern) (guard : d500 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d486 p = 1 := by simpa only [d500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5035 p hg
    simpa only [d500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5050 (p : Pattern) (guard : d501 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d490 p = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5039 p hg
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5051 (p : Pattern) (guard : d502 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d500 p = 1 := by simpa only [d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5049 p hg
    simpa only [d502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d501 p = 1 := by simpa only [d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5050 p hg
    simpa only [d502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5052 (p : Pattern) (guard : d503 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d502 p = 1 := by simpa only [d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5051 p hg
    simpa only [d503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5053 (p : Pattern) (guard : d504 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d503 p = 1 := by simpa only [d504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5052 p hg
    simpa only [d504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5054 (p : Pattern) (guard : d505 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d504 p = 1 := by simpa only [d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5053 p hg
    simpa only [d505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5055 (p : Pattern) (guard : d506 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d505 p = 1 := by simpa only [d506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5054 p hg
    simpa only [d506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5056 (p : Pattern) (guard : d507 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d496 p = 1 := by simpa only [d507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5045 p hg
    simpa only [d507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d506 p = 1 := by simpa only [d507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5055 p hg
    simpa only [d507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5057 (p : Pattern) (guard : d508 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d497 p = 1 := by simpa only [d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5046 p hg
    simpa only [d508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d507 p = 1 := by simpa only [d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5056 p hg
    simpa only [d508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5058 (p : Pattern) (guard : d509 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 69 with
  | false =>
    have hg : d508 p = 1 := by simpa only [d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5057 p hg
    simpa only [d509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5059 (p : Pattern) (guard : d510 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 51 with
  | false =>
    have hg : d499 p = 1 := by simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5048 p hg
    simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d509 p = 1 := by simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5058 p hg
    simpa only [d510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5060 (p : Pattern) (guard : d511 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d485 p = 1 := by simpa only [d511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5034 p hg
    simpa only [d511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5061 (p : Pattern) (guard : d512 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d511 p = 1 := by simpa only [d512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5060 p hg
    simpa only [d512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5062 (p : Pattern) (guard : d513 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d489 p = 1 := by simpa only [d513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5038 p hg
    simpa only [d513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5063 (p : Pattern) (guard : d514 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d513 p = 1 := by simpa only [d514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5062 p hg
    simpa only [d514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5064 (p : Pattern) (guard : d515 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d512 p = 1 := by simpa only [d515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5061 p hg
    simpa only [d515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d514 p = 1 := by simpa only [d515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5063 p hg
    simpa only [d515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5065 (p : Pattern) (guard : d516 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d515 p = 1 := by simpa only [d516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5064 p hg
    simpa only [d516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5066 (p : Pattern) (guard : d517 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d516 p = 1 := by simpa only [d517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5065 p hg
    simpa only [d517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5067 (p : Pattern) (guard : d518 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d517 p = 1 := by simpa only [d518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5066 p hg
    simpa only [d518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5068 (p : Pattern) (guard : d519 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d484 p = 1 := by simpa only [d519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5033 p hg
    simpa only [d519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5069 (p : Pattern) (guard : d520 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d519 p = 1 := by simpa only [d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5068 p hg
    simpa only [d520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5070 (p : Pattern) (guard : d521 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d520 p = 1 := by simpa only [d521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5069 p hg
    simpa only [d521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5071 (p : Pattern) (guard : d522 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d488 p = 1 := by simpa only [d522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5037 p hg
    simpa only [d522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5072 (p : Pattern) (guard : d523 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d522 p = 1 := by simpa only [d523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5071 p hg
    simpa only [d523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5073 (p : Pattern) (guard : d524 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d523 p = 1 := by simpa only [d524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5072 p hg
    simpa only [d524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5074 (p : Pattern) (guard : d525 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d521 p = 1 := by simpa only [d525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5070 p hg
    simpa only [d525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d524 p = 1 := by simpa only [d525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5073 p hg
    simpa only [d525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5075 (p : Pattern) (guard : d526 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d525 p = 1 := by simpa only [d526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5074 p hg
    simpa only [d526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5076 (p : Pattern) (guard : d527 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d526 p = 1 := by simpa only [d527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5075 p hg
    simpa only [d527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5077 (p : Pattern) (guard : d528 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d309 p = 1 := by simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4814 p hg
    simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5078 (p : Pattern) (guard : d529 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5077 p hg
    simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d310 p = 1 := by simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4815 p hg
    simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5079 (p : Pattern) (guard : d530 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d529 p = 1 := by simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5078 p hg
    simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d311 p = 1 := by simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4816 p hg
    simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5080 (p : Pattern) (guard : d531 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d530 p = 1 := by simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5079 p hg
    simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5081 (p : Pattern) (guard : d532 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d531 p = 1 := by simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5080 p hg
    simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5082 (p : Pattern) (guard : d533 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d532 p = 1 := by simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5081 p hg
    simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d314 p = 1 := by simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4819 p hg
    simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5083 (p : Pattern) (guard : d534 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d129 p = 1 := by simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4622 p hg
    simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5084 (p : Pattern) (guard : d535 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d310 p = 1 := by simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4815 p hg
    simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d534 p = 1 := by simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5083 p hg
    simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5085 (p : Pattern) (guard : d536 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d535 p = 1 := by simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5084 p hg
    simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d131 p = 1 := by simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4624 p hg
    simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5086 (p : Pattern) (guard : d537 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d536 p = 1 := by simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5085 p hg
    simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5087 (p : Pattern) (guard : d538 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d537 p = 1 := by simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5086 p hg
    simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5088 (p : Pattern) (guard : d539 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d538 p = 1 := by simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5087 p hg
    simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d134 p = 1 := by simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4627 p hg
    simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5089 (p : Pattern) (guard : d540 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d533 p = 1 := by simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5082 p hg
    simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d539 p = 1 := by simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5088 p hg
    simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5090 (p : Pattern) (guard : d541 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d540 p = 1 := by simpa only [d541, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5089 p hg
    simpa only [d541, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d541, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4416 p hg
    simpa only [d541, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5091 (p : Pattern) (guard : d542 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d541 p = 1 := by simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5090 p hg
    simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317 p = 1 := by simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4822 p hg
    simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5092 (p : Pattern) (guard : d543 p = 1) : d47660 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d542 p = 1 := by simpa only [d543, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5091 p hg
    simpa only [d543, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d543, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4420 p hg
    simpa only [d543, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5093 (p : Pattern) (guard : d544 p = 1) : d47663 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d543 p = 1 := by simpa only [d544, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5092 p hg
    simpa only [d544, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d544, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d544, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5094 (p : Pattern) (guard : d545 p = 1) : d47664 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d545, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4404 p hg
    simpa only [d545, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d544 p = 1 := by simpa only [d545, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5093 p hg
    simpa only [d545, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5095 (p : Pattern) (guard : d546 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d545 p = 1 := by simpa only [d546, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5094 p hg
    simpa only [d546, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d546, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4424 p hg
    simpa only [d546, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5096 (p : Pattern) (guard : d547 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d546 p = 1 := by simpa only [d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5095 p hg
    simpa only [d547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d322 p = 1 := by simpa only [d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4827 p hg
    simpa only [d547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5097 (p : Pattern) (guard : d548 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d547 p = 1 := by simpa only [d548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5096 p hg
    simpa only [d548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d323 p = 1 := by simpa only [d548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4828 p hg
    simpa only [d548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5098 (p : Pattern) (guard : d549 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d548 p = 1 := by simpa only [d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5097 p hg
    simpa only [d549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324 p = 1 := by simpa only [d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4829 p hg
    simpa only [d549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5099 (p : Pattern) (guard : d550 p = 1) : d47686 p ≤ (-1 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d550, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4403 p hg
    simpa only [d550, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d549 p = 1 := by simpa only [d550, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5098 p hg
    simpa only [d550, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5100 (p : Pattern) (guard : d551 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d551, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4402 p hg
    simpa only [d551, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d550 p = 1 := by simpa only [d551, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5099 p hg
    simpa only [d551, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5101 (p : Pattern) (guard : d552 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d551 p = 1 := by simpa only [d552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5100 p hg
    simpa only [d552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d327 p = 1 := by simpa only [d552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4832 p hg
    simpa only [d552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5102 (p : Pattern) (guard : d553 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d552 p = 1 := by simpa only [d553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5101 p hg
    simpa only [d553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d328 p = 1 := by simpa only [d553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4833 p hg
    simpa only [d553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5103 (p : Pattern) (guard : d554 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d553 p = 1 := by simpa only [d554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5102 p hg
    simpa only [d554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5104 (p : Pattern) (guard : d555 p = 1) : d47699 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d554 p = 1 := by simpa only [d555, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5103 p hg
    simpa only [d555, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d555, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4436 p hg
    simpa only [d555, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5105 (p : Pattern) (guard : d556 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d556, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d556, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d555 p = 1 := by simpa only [d556, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5104 p hg
    simpa only [d556, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5106 (p : Pattern) (guard : d6797 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d327 p = 1 := by simpa only [d6797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4832 p hg
    simpa only [d6797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d6797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5107 (p : Pattern) (guard : d4818 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d143 p = 1 := by simpa only [d4818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4636 p hg
    simpa only [d4818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4426 p hg
    simpa only [d4818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5108 (p : Pattern) (guard : d4819 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d4818 p = 1 := by simpa only [d4819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5107 p hg
    simpa only [d4819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d30 p = 1 := by simpa only [d4819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4428 p hg
    simpa only [d4819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5109 (p : Pattern) (guard : d4820 p = 1) : d47686 p ≤ (-1 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4820, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4403 p hg
    simpa only [d4820, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4819 p = 1 := by simpa only [d4820, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5108 p hg
    simpa only [d4820, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5110 (p : Pattern) (guard : d4821 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4821, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4402 p hg
    simpa only [d4821, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4820 p = 1 := by simpa only [d4821, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5109 p hg
    simpa only [d4821, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5111 (p : Pattern) (guard : d4822 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d4821 p = 1 := by simpa only [d4822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5110 p hg
    simpa only [d4822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d4822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5112 (p : Pattern) (guard : d6798 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d6797 p = 1 := by simpa only [d6798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5106 p hg
    simpa only [d6798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4822 p = 1 := by simpa only [d6798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5111 p hg
    simpa only [d6798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5113 (p : Pattern) (guard : d6799 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d6798 p = 1 := by simpa only [d6799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5112 p hg
    simpa only [d6799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d6799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5114 (p : Pattern) (guard : d6800 p = 1) : d47699 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6799 p = 1 := by simpa only [d6800, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5113 p hg
    simpa only [d6800, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6800, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4436 p hg
    simpa only [d6800, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5115 (p : Pattern) (guard : d6801 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6801, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d6801, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6800 p = 1 := by simpa only [d6801, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5114 p hg
    simpa only [d6801, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5116 (p : Pattern) (guard : d6802 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d556 p = 1 := by simpa only [d6802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5105 p hg
    simpa only [d6802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6801 p = 1 := by simpa only [d6802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5115 p hg
    simpa only [d6802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5117 (p : Pattern) (guard : d6803 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d6802 p = 1 := by simpa only [d6803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5116 p hg
    simpa only [d6803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5118 (p : Pattern) (guard : d6804 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d6803 p = 1 := by simpa only [d6804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5117 p hg
    simpa only [d6804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5119 (p : Pattern) (guard : d6805 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6804 p = 1 := by simpa only [d6805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5118 p hg
    simpa only [d6805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5120 (p : Pattern) (guard : d4823 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d328 p = 1 := by simpa only [d4823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4833 p hg
    simpa only [d4823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4822 p = 1 := by simpa only [d4823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5111 p hg
    simpa only [d4823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5121 (p : Pattern) (guard : d4824 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d4823 p = 1 := by simpa only [d4824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5120 p hg
    simpa only [d4824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d4824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5122 (p : Pattern) (guard : d4825 p = 1) : d47699 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4824 p = 1 := by simpa only [d4825, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5121 p hg
    simpa only [d4825, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4825, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4436 p hg
    simpa only [d4825, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5123 (p : Pattern) (guard : d4826 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4826, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d4826, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4825 p = 1 := by simpa only [d4826, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5122 p hg
    simpa only [d4826, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5124 (p : Pattern) (guard : d6806 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d4826 p = 1 := by simpa only [d6806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5123 p hg
    simpa only [d6806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d483 p = 1 := by simpa only [d6806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5032 p hg
    simpa only [d6806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5125 (p : Pattern) (guard : d6807 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d6806 p = 1 := by simpa only [d6807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5124 p hg
    simpa only [d6807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5126 (p : Pattern) (guard : d6808 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d6807 p = 1 := by simpa only [d6808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5125 p hg
    simpa only [d6808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5127 (p : Pattern) (guard : d6809 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6808 p = 1 := by simpa only [d6809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5126 p hg
    simpa only [d6809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5128 (p : Pattern) (guard : d6810 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d6805 p = 1 := by simpa only [d6810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5119 p hg
    simpa only [d6810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6809 p = 1 := by simpa only [d6810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5127 p hg
    simpa only [d6810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5129 (p : Pattern) (guard : d82067 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d6810 p = 1 := by simpa only [d82067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5128 p hg
    simpa only [d82067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d82067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5130 (p : Pattern) (guard : d5396 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d479 p = 1 := by simpa only [d5396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5028 p hg
    simpa only [d5396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d5396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5131 (p : Pattern) (guard : d5397 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d5396 p = 1 := by simpa only [d5397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5130 p hg
    simpa only [d5397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d5397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5132 (p : Pattern) (guard : d5398 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d5397 p = 1 := by simpa only [d5398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5131 p hg
    simpa only [d5398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d5398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5133 (p : Pattern) (guard : d5399 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d5399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5398 p = 1 := by simpa only [d5399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5132 p hg
    simpa only [d5399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5134 (p : Pattern) (guard : d5400 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d5399 p = 1 := by simpa only [d5400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5133 p hg
    simpa only [d5400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d5400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5135 (p : Pattern) (guard : d5401 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d5400 p = 1 := by simpa only [d5401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5134 p hg
    simpa only [d5401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d5401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5136 (p : Pattern) (guard : d82068 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d82067 p = 1 := by simpa only [d82068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5129 p hg
    simpa only [d82068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5401 p = 1 := by simpa only [d82068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5135 p hg
    simpa only [d82068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5137 (p : Pattern) (guard : d82069 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d527 p = 1 := by simpa only [d82069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5076 p hg
    simpa only [d82069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82068 p = 1 := by simpa only [d82069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5136 p hg
    simpa only [d82069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5138 (p : Pattern) (guard : d82070 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d518 p = 1 := by simpa only [d82070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5067 p hg
    simpa only [d82070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82069 p = 1 := by simpa only [d82070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5137 p hg
    simpa only [d82070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5139 (p : Pattern) (guard : d82071 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d82071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82070 p = 1 := by simpa only [d82071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5138 p hg
    simpa only [d82071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5140 (p : Pattern) (guard : d609 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d511 p = 1 := by simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5060 p hg
    simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5141 (p : Pattern) (guard : d610 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d513 p = 1 := by simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5062 p hg
    simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5142 (p : Pattern) (guard : d611 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d609 p = 1 := by simpa only [d611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5140 p hg
    simpa only [d611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d610 p = 1 := by simpa only [d611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5141 p hg
    simpa only [d611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5143 (p : Pattern) (guard : d612 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d611 p = 1 := by simpa only [d612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5142 p hg
    simpa only [d612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5144 (p : Pattern) (guard : d613 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d612 p = 1 := by simpa only [d613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5143 p hg
    simpa only [d613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5145 (p : Pattern) (guard : d614 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d613 p = 1 := by simpa only [d614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5144 p hg
    simpa only [d614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5146 (p : Pattern) (guard : d615 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d520 p = 1 := by simpa only [d615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5069 p hg
    simpa only [d615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5147 (p : Pattern) (guard : d616 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d523 p = 1 := by simpa only [d616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5072 p hg
    simpa only [d616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5148 (p : Pattern) (guard : d617 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d615 p = 1 := by simpa only [d617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5146 p hg
    simpa only [d617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d616 p = 1 := by simpa only [d617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5147 p hg
    simpa only [d617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5149 (p : Pattern) (guard : d618 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d617 p = 1 := by simpa only [d618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5148 p hg
    simpa only [d618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5150 (p : Pattern) (guard : d619 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d618 p = 1 := by simpa only [d619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5149 p hg
    simpa only [d619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5151 (p : Pattern) (guard : d6816 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d6804 p = 1 := by simpa only [d6816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5118 p hg
    simpa only [d6816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5152 (p : Pattern) (guard : d6817 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d6808 p = 1 := by simpa only [d6817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5126 p hg
    simpa only [d6817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5153 (p : Pattern) (guard : d6818 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d6816 p = 1 := by simpa only [d6818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5151 p hg
    simpa only [d6818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6817 p = 1 := by simpa only [d6818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5152 p hg
    simpa only [d6818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5154 (p : Pattern) (guard : d82072 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d6818 p = 1 := by simpa only [d82072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5153 p hg
    simpa only [d82072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d82072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5155 (p : Pattern) (guard : d5406 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d5398 p = 1 := by simpa only [d5406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5132 p hg
    simpa only [d5406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d5406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5156 (p : Pattern) (guard : d5407 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d5406 p = 1 := by simpa only [d5407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5155 p hg
    simpa only [d5407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d5407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5157 (p : Pattern) (guard : d5408 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d5407 p = 1 := by simpa only [d5408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5156 p hg
    simpa only [d5408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d5408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5158 (p : Pattern) (guard : d82073 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d82072 p = 1 := by simpa only [d82073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5154 p hg
    simpa only [d82073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5408 p = 1 := by simpa only [d82073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5157 p hg
    simpa only [d82073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5159 (p : Pattern) (guard : d82074 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d619 p = 1 := by simpa only [d82074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5150 p hg
    simpa only [d82074, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82073 p = 1 := by simpa only [d82074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5158 p hg
    simpa only [d82074, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5160 (p : Pattern) (guard : d82075 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d614 p = 1 := by simpa only [d82075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5145 p hg
    simpa only [d82075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82074 p = 1 := by simpa only [d82075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5159 p hg
    simpa only [d82075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5161 (p : Pattern) (guard : d82076 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d82070 p = 1 := by simpa only [d82076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5138 p hg
    simpa only [d82076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82075 p = 1 := by simpa only [d82076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5160 p hg
    simpa only [d82076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5162 (p : Pattern) (guard : d82077 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d82071 p = 1 := by simpa only [d82077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5139 p hg
    simpa only [d82077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82076 p = 1 := by simpa only [d82077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5161 p hg
    simpa only [d82077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5163 (p : Pattern) (guard : d6825 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d6809 p = 1 := by simpa only [d6825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5127 p hg
    simpa only [d6825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d491 p = 1 := by simpa only [d6825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5040 p hg
    simpa only [d6825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5164 (p : Pattern) (guard : d6826 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6825 p = 1 := by simpa only [d6826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5163 p hg
    simpa only [d6826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5165 (p : Pattern) (guard : d6827 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d6826 p = 1 := by simpa only [d6827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5164 p hg
    simpa only [d6827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5166 (p : Pattern) (guard : d6828 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6827 p = 1 := by simpa only [d6828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5165 p hg
    simpa only [d6828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5167 (p : Pattern) (guard : d6829 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6828 p = 1 := by simpa only [d6829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5166 p hg
    simpa only [d6829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5168 (p : Pattern) (guard : d633 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d491 p = 1 := by simpa only [d633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5040 p hg
    simpa only [d633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5169 (p : Pattern) (guard : d634 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d633 p = 1 := by simpa only [d634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5168 p hg
    simpa only [d634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5170 (p : Pattern) (guard : d635 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d634 p = 1 := by simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5169 p hg
    simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5171 (p : Pattern) (guard : d636 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d635 p = 1 := by simpa only [d636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5170 p hg
    simpa only [d636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5172 (p : Pattern) (guard : d637 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d636 p = 1 := by simpa only [d637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5171 p hg
    simpa only [d637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5173 (p : Pattern) (guard : d6830 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d6829 p = 1 := by simpa only [d6830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5167 p hg
    simpa only [d6830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d637 p = 1 := by simpa only [d6830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5172 p hg
    simpa only [d6830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5174 (p : Pattern) (guard : d639 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d501 p = 1 := by simpa only [d639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5050 p hg
    simpa only [d639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5175 (p : Pattern) (guard : d640 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d639 p = 1 := by simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5174 p hg
    simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5176 (p : Pattern) (guard : d641 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d640 p = 1 := by simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5175 p hg
    simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5177 (p : Pattern) (guard : d642 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d641 p = 1 := by simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5176 p hg
    simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5178 (p : Pattern) (guard : d643 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d642 p = 1 := by simpa only [d643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5177 p hg
    simpa only [d643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5179 (p : Pattern) (guard : d644 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d637 p = 1 := by simpa only [d644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5172 p hg
    simpa only [d644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d643 p = 1 := by simpa only [d644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5178 p hg
    simpa only [d644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5180 (p : Pattern) (guard : d6831 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d6830 p = 1 := by simpa only [d6831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5173 p hg
    simpa only [d6831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d644 p = 1 := by simpa only [d6831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5179 p hg
    simpa only [d6831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5181 (p : Pattern) (guard : d82078 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 69 with
  | false =>
    have hg : d82077 p = 1 := by simpa only [d82078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5162 p hg
    simpa only [d82078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6831 p = 1 := by simpa only [d82078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5180 p hg
    simpa only [d82078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5182 (p : Pattern) (guard : d82079 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 51 with
  | false =>
    have hg : d82078 p = 1 := by simpa only [d82079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5181 p hg
    simpa only [d82079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d82079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5183 (p : Pattern) (guard : d82080 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 50 with
  | false =>
    have hg : d510 p = 1 := by simpa only [d82080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5059 p hg
    simpa only [d82080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82079 p = 1 := by simpa only [d82080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5182 p hg
    simpa only [d82080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5184 (p : Pattern) (guard : d528 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d309 p = 1 := by simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4887 p hg
    simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5185 (p : Pattern) (guard : d529 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5184 p hg
    simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d310 p = 1 := by simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4888 p hg
    simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5186 (p : Pattern) (guard : d530 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d529 p = 1 := by simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5185 p hg
    simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d311 p = 1 := by simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4889 p hg
    simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5187 (p : Pattern) (guard : d531 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d530 p = 1 := by simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5186 p hg
    simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5188 (p : Pattern) (guard : d532 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d531 p = 1 := by simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5187 p hg
    simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5189 (p : Pattern) (guard : d533 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d532 p = 1 := by simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5188 p hg
    simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d314 p = 1 := by simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4892 p hg
    simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5190 (p : Pattern) (guard : d534 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d129 p = 1 := by simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4681 p hg
    simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5191 (p : Pattern) (guard : d535 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d310 p = 1 := by simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4888 p hg
    simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d534 p = 1 := by simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5190 p hg
    simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5192 (p : Pattern) (guard : d536 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d535 p = 1 := by simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5191 p hg
    simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d131 p = 1 := by simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4683 p hg
    simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5193 (p : Pattern) (guard : d537 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d536 p = 1 := by simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5192 p hg
    simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5194 (p : Pattern) (guard : d538 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d537 p = 1 := by simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5193 p hg
    simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5195 (p : Pattern) (guard : d539 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d538 p = 1 := by simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5194 p hg
    simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d134 p = 1 := by simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4686 p hg
    simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5196 (p : Pattern) (guard : d540 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d533 p = 1 := by simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5189 p hg
    simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d539 p = 1 := by simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5195 p hg
    simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5197 (p : Pattern) (guard : d541 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d540 p = 1 := by simpa only [d541, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5196 p hg
    simpa only [d541, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d541, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4477 p hg
    simpa only [d541, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5198 (p : Pattern) (guard : d542 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d541 p = 1 := by simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5197 p hg
    simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317 p = 1 := by simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4895 p hg
    simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5199 (p : Pattern) (guard : d543 p = 1) : d47735 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d542 p = 1 := by simpa only [d543, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5198 p hg
    simpa only [d543, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d543, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d543, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5200 (p : Pattern) (guard : d544 p = 1) : d47736 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d543 p = 1 := by simpa only [d544, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5199 p hg
    simpa only [d544, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d544, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d544, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5201 (p : Pattern) (guard : d545 p = 1) : d47737 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d545, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4465 p hg
    simpa only [d545, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d544 p = 1 := by simpa only [d545, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5200 p hg
    simpa only [d545, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5202 (p : Pattern) (guard : d546 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d545 p = 1 := by simpa only [d546, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5201 p hg
    simpa only [d546, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d546, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4485 p hg
    simpa only [d546, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5203 (p : Pattern) (guard : d547 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d546 p = 1 := by simpa only [d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5202 p hg
    simpa only [d547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d322 p = 1 := by simpa only [d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4900 p hg
    simpa only [d547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5204 (p : Pattern) (guard : d548 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 158 with
  | false =>
    have hg : d547 p = 1 := by simpa only [d548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5203 p hg
    simpa only [d548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d323 p = 1 := by simpa only [d548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4901 p hg
    simpa only [d548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5205 (p : Pattern) (guard : d549 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 157 with
  | false =>
    have hg : d548 p = 1 := by simpa only [d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5204 p hg
    simpa only [d549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324 p = 1 := by simpa only [d549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4902 p hg
    simpa only [d549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5206 (p : Pattern) (guard : d550 p = 1) : d47756 p ≤ (-1 : Int) + d47761 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d550, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4464 p hg
    simpa only [d550, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d549 p = 1 := by simpa only [d550, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5205 p hg
    simpa only [d550, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5207 (p : Pattern) (guard : d551 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d551, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4463 p hg
    simpa only [d551, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d550 p = 1 := by simpa only [d551, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5206 p hg
    simpa only [d551, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5208 (p : Pattern) (guard : d552 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 136 with
  | false =>
    have hg : d551 p = 1 := by simpa only [d552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5207 p hg
    simpa only [d552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d327 p = 1 := by simpa only [d552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4905 p hg
    simpa only [d552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5209 (p : Pattern) (guard : d553 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 135 with
  | false =>
    have hg : d552 p = 1 := by simpa only [d553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5208 p hg
    simpa only [d553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d328 p = 1 := by simpa only [d553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4906 p hg
    simpa only [d553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5210 (p : Pattern) (guard : d554 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 119 with
  | false =>
    have hg : d553 p = 1 := by simpa only [d554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5209 p hg
    simpa only [d554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5211 (p : Pattern) (guard : d555 p = 1) : d47765 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 116 with
  | false =>
    have hg : d554 p = 1 := by simpa only [d555, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5210 p hg
    simpa only [d555, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d555, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4497 p hg
    simpa only [d555, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5212 (p : Pattern) (guard : d556 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d556, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4462 p hg
    simpa only [d556, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d555 p = 1 := by simpa only [d556, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5211 p hg
    simpa only [d556, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5213 (p : Pattern) (guard : d6797 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 136 with
  | false =>
    have hg : d327 p = 1 := by simpa only [d6797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4905 p hg
    simpa only [d6797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d6797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5214 (p : Pattern) (guard : d4818 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 158 with
  | false =>
    have hg : d143 p = 1 := by simpa only [d4818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4695 p hg
    simpa only [d4818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4487 p hg
    simpa only [d4818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5215 (p : Pattern) (guard : d4819 p = 1) : d47755 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 157 with
  | false =>
    have hg : d4818 p = 1 := by simpa only [d4819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5214 p hg
    simpa only [d4819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d30 p = 1 := by simpa only [d4819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4489 p hg
    simpa only [d4819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5216 (p : Pattern) (guard : d4820 p = 1) : d47756 p ≤ (-1 : Int) + d47761 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4820, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4464 p hg
    simpa only [d4820, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4819 p = 1 := by simpa only [d4820, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5215 p hg
    simpa only [d4820, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5217 (p : Pattern) (guard : d4821 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4821, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4463 p hg
    simpa only [d4821, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4820 p = 1 := by simpa only [d4821, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5216 p hg
    simpa only [d4821, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5218 (p : Pattern) (guard : d4822 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 136 with
  | false =>
    have hg : d4821 p = 1 := by simpa only [d4822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5217 p hg
    simpa only [d4822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d4822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5219 (p : Pattern) (guard : d6798 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 135 with
  | false =>
    have hg : d6797 p = 1 := by simpa only [d6798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5213 p hg
    simpa only [d6798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4822 p = 1 := by simpa only [d6798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5218 p hg
    simpa only [d6798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5220 (p : Pattern) (guard : d6799 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 119 with
  | false =>
    have hg : d6798 p = 1 := by simpa only [d6799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5219 p hg
    simpa only [d6799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d6799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5221 (p : Pattern) (guard : d6800 p = 1) : d47765 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6799 p = 1 := by simpa only [d6800, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5220 p hg
    simpa only [d6800, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6800, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4497 p hg
    simpa only [d6800, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5222 (p : Pattern) (guard : d6801 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6801, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4462 p hg
    simpa only [d6801, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6800 p = 1 := by simpa only [d6801, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5221 p hg
    simpa only [d6801, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5223 (p : Pattern) (guard : d6802 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 113 with
  | false =>
    have hg : d556 p = 1 := by simpa only [d6802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5212 p hg
    simpa only [d6802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6801 p = 1 := by simpa only [d6802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5222 p hg
    simpa only [d6802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5224 (p : Pattern) (guard : d6803 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 96 with
  | false =>
    have hg : d6802 p = 1 := by simpa only [d6803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5223 p hg
    simpa only [d6803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d6803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5225 (p : Pattern) (guard : d6804 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 95 with
  | false =>
    have hg : d6803 p = 1 := by simpa only [d6804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5224 p hg
    simpa only [d6804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d6804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5226 (p : Pattern) (guard : d6816 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 93 with
  | false =>
    have hg : d6804 p = 1 := by simpa only [d6816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5225 p hg
    simpa only [d6816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d6816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5227 (p : Pattern) (guard : d4823 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 135 with
  | false =>
    have hg : d328 p = 1 := by simpa only [d4823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4906 p hg
    simpa only [d4823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4822 p = 1 := by simpa only [d4823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5218 p hg
    simpa only [d4823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5228 (p : Pattern) (guard : d4824 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 119 with
  | false =>
    have hg : d4823 p = 1 := by simpa only [d4824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5227 p hg
    simpa only [d4824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d4824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5229 (p : Pattern) (guard : d4825 p = 1) : d47765 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4824 p = 1 := by simpa only [d4825, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5228 p hg
    simpa only [d4825, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4825, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4497 p hg
    simpa only [d4825, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5230 (p : Pattern) (guard : d4826 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4826, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4462 p hg
    simpa only [d4826, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4825 p = 1 := by simpa only [d4826, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5229 p hg
    simpa only [d4826, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5231 (p : Pattern) (guard : d480 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 135 with
  | false =>
    have hg : d475 p = 1 := by simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4911 p hg
    simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5232 (p : Pattern) (guard : d481 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 119 with
  | false =>
    have hg : d480 p = 1 := by simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5231 p hg
    simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5233 (p : Pattern) (guard : d482 p = 1) : d47765 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 116 with
  | false =>
    have hg : d481 p = 1 := by simpa only [d482, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5232 p hg
    simpa only [d482, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d482, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4497 p hg
    simpa only [d482, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5234 (p : Pattern) (guard : d483 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d483, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4462 p hg
    simpa only [d483, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d482 p = 1 := by simpa only [d483, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5233 p hg
    simpa only [d483, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5235 (p : Pattern) (guard : d6806 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 113 with
  | false =>
    have hg : d4826 p = 1 := by simpa only [d6806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5230 p hg
    simpa only [d6806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d483 p = 1 := by simpa only [d6806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5234 p hg
    simpa only [d6806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5236 (p : Pattern) (guard : d6807 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 96 with
  | false =>
    have hg : d6806 p = 1 := by simpa only [d6807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5235 p hg
    simpa only [d6807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d6807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5237 (p : Pattern) (guard : d6808 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 95 with
  | false =>
    have hg : d6807 p = 1 := by simpa only [d6808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5236 p hg
    simpa only [d6808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d6808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5238 (p : Pattern) (guard : d6817 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 93 with
  | false =>
    have hg : d6808 p = 1 := by simpa only [d6817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5237 p hg
    simpa only [d6817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d6817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5239 (p : Pattern) (guard : d6818 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 91 with
  | false =>
    have hg : d6816 p = 1 := by simpa only [d6818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5226 p hg
    simpa only [d6818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6817 p = 1 := by simpa only [d6818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5238 p hg
    simpa only [d6818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5240 (p : Pattern) (guard : d82072 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 90 with
  | false =>
    have hg : d6818 p = 1 := by simpa only [d82072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5239 p hg
    simpa only [d82072, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d82072, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5241 (p : Pattern) (guard : d476 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 135 with
  | false =>
    have hg : d328 p = 1 := by simpa only [d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4906 p hg
    simpa only [d476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d475 p = 1 := by simpa only [d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4911 p hg
    simpa only [d476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5242 (p : Pattern) (guard : d477 p = 1) : d47757 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 119 with
  | false =>
    have hg : d476 p = 1 := by simpa only [d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5241 p hg
    simpa only [d477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4493 p hg
    simpa only [d477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5243 (p : Pattern) (guard : d478 p = 1) : d47765 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 116 with
  | false =>
    have hg : d477 p = 1 := by simpa only [d478, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5242 p hg
    simpa only [d478, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d478, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4497 p hg
    simpa only [d478, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5244 (p : Pattern) (guard : d479 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d479, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4462 p hg
    simpa only [d479, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d478 p = 1 := by simpa only [d479, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5243 p hg
    simpa only [d479, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5245 (p : Pattern) (guard : d5396 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 113 with
  | false =>
    have hg : d479 p = 1 := by simpa only [d5396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5244 p hg
    simpa only [d5396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d5396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5246 (p : Pattern) (guard : d5397 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 96 with
  | false =>
    have hg : d5396 p = 1 := by simpa only [d5397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5245 p hg
    simpa only [d5397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d5397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5247 (p : Pattern) (guard : d5398 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 95 with
  | false =>
    have hg : d5397 p = 1 := by simpa only [d5398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5246 p hg
    simpa only [d5398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d5398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5248 (p : Pattern) (guard : d5406 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 93 with
  | false =>
    have hg : d5398 p = 1 := by simpa only [d5406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5247 p hg
    simpa only [d5406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d5406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5249 (p : Pattern) (guard : d5407 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 91 with
  | false =>
    have hg : d5406 p = 1 := by simpa only [d5407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5248 p hg
    simpa only [d5407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d5407, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
