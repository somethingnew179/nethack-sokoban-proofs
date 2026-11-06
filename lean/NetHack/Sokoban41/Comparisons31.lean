/- Staged soko4-1 certificate. No result until all kernel checks pass. -/
import NetHack.Sokoban41.Comparisons30
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem c4960 (pattern : Ten) (guard : d0 pattern = 1) : d32 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4961 (pattern : Ten) (guard : d610 pattern = 1) : d34 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4959 pattern childGuard
    simpa only [d610, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4960 pattern childGuard
    simpa only [d610, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4962 (pattern : Ten) (guard : d707 pattern = 1) : d35 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d707, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4952 pattern childGuard
    simpa only [d707, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d610 pattern = 1 := by simpa only [d707, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4961 pattern childGuard
    simpa only [d707, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4963 (pattern : Ten) (guard : d0 pattern = 1) : d36 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4964 (pattern : Ten) (guard : d708 pattern = 1) : d37 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d707 pattern = 1 := by simpa only [d708, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4962 pattern childGuard
    simpa only [d708, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d708, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4963 pattern childGuard
    simpa only [d708, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4965 (pattern : Ten) (guard : d0 pattern = 1) : d54 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4966 (pattern : Ten) (guard : d0 pattern = 1) : d2 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4967 (pattern : Ten) (guard : d606 pattern = 1) : d15 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4953 pattern childGuard
    simpa only [d606, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4966 pattern childGuard
    simpa only [d606, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4968 (pattern : Ten) (guard : d0 pattern = 1) : d42 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4969 (pattern : Ten) (guard : d607 pattern = 1) : d48 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4967 pattern childGuard
    simpa only [d607, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4968 pattern childGuard
    simpa only [d607, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4970 (pattern : Ten) (guard : d0 pattern = 1) : d49 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4971 (pattern : Ten) (guard : d608 pattern = 1) : d54 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4969 pattern childGuard
    simpa only [d608, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4970 pattern childGuard
    simpa only [d608, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4972 (pattern : Ten) (guard : d609 pattern = 1) : d58 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4971 pattern childGuard
    simpa only [d609, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4958 pattern childGuard
    simpa only [d609, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4973 (pattern : Ten) (guard : d0 pattern = 1) : d59 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4974 (pattern : Ten) (guard : d610 pattern = 1) : d62 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4972 pattern childGuard
    simpa only [d610, d62, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4973 pattern childGuard
    simpa only [d610, d62, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4975 (pattern : Ten) (guard : d707 pattern = 1) : d64 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d707, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4965 pattern childGuard
    simpa only [d707, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d610 pattern = 1 := by simpa only [d707, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4974 pattern childGuard
    simpa only [d707, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4976 (pattern : Ten) (guard : d0 pattern = 1) : d65 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4977 (pattern : Ten) (guard : d708 pattern = 1) : d66 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d707 pattern = 1 := by simpa only [d708, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4975 pattern childGuard
    simpa only [d708, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d708, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4976 pattern childGuard
    simpa only [d708, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4978 (pattern : Ten) (guard : d0 pattern = 1) : d77 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4979 (pattern : Ten) (guard : d0 pattern = 1) : d72 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4980 (pattern : Ten) (guard : d609 pattern = 1) : d75 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4957 pattern childGuard
    simpa only [d609, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4979 pattern childGuard
    simpa only [d609, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4981 (pattern : Ten) (guard : d0 pattern = 1) : d76 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4982 (pattern : Ten) (guard : d610 pattern = 1) : d78 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4980 pattern childGuard
    simpa only [d610, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4981 pattern childGuard
    simpa only [d610, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4983 (pattern : Ten) (guard : d707 pattern = 1) : d79 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d707, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4978 pattern childGuard
    simpa only [d707, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d610 pattern = 1 := by simpa only [d707, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4982 pattern childGuard
    simpa only [d707, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4984 (pattern : Ten) (guard : d0 pattern = 1) : d80 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4985 (pattern : Ten) (guard : d708 pattern = 1) : d81 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d707 pattern = 1 := by simpa only [d708, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4983 pattern childGuard
    simpa only [d708, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d708, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4984 pattern childGuard
    simpa only [d708, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4986 (pattern : Ten) (guard : d0 pattern = 1) : d82 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4987 (pattern : Ten) (guard : d610 pattern = 1) : d58 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4972 pattern childGuard
    simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c280 pattern childGuard
    simpa only [d610, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4988 (pattern : Ten) (guard : d707 pattern = 1) : d83 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d707, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4986 pattern childGuard
    simpa only [d707, d83, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d610 pattern = 1 := by simpa only [d707, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4987 pattern childGuard
    simpa only [d707, d83, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4989 (pattern : Ten) (guard : d0 pattern = 1) : d84 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4990 (pattern : Ten) (guard : d708 pattern = 1) : d85 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d707 pattern = 1 := by simpa only [d708, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4988 pattern childGuard
    simpa only [d708, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d708, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4989 pattern childGuard
    simpa only [d708, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4991 (pattern : Ten) (guard : d0 pattern = 1) : d103 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4992 (pattern : Ten) (guard : d606 pattern = 1) : d0 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) ≤ (0 : Int) + 8
  decide
theorem c4993 (pattern : Ten) (guard : d607 pattern = 1) : d88 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4992 pattern childGuard
    simpa only [d607, d88, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4954 pattern childGuard
    simpa only [d607, d88, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4994 (pattern : Ten) (guard : d608 pattern = 1) : d96 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4993 pattern childGuard
    simpa only [d608, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4954 pattern childGuard
    simpa only [d608, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4995 (pattern : Ten) (guard : d0 pattern = 1) : d97 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4996 (pattern : Ten) (guard : d609 pattern = 1) : d101 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4994 pattern childGuard
    simpa only [d609, d101, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4995 pattern childGuard
    simpa only [d609, d101, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4997 (pattern : Ten) (guard : d0 pattern = 1) : d102 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4998 (pattern : Ten) (guard : d610 pattern = 1) : d104 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4996 pattern childGuard
    simpa only [d610, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4997 pattern childGuard
    simpa only [d610, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4999 (pattern : Ten) (guard : d707 pattern = 1) : d105 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d707, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4991 pattern childGuard
    simpa only [d707, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d610 pattern = 1 := by simpa only [d707, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4998 pattern childGuard
    simpa only [d707, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5000 (pattern : Ten) (guard : d0 pattern = 1) : d106 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5001 (pattern : Ten) (guard : d708 pattern = 1) : d107 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d707 pattern = 1 := by simpa only [d708, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4999 pattern childGuard
    simpa only [d708, d107, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d708, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5000 pattern childGuard
    simpa only [d708, d107, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5002 (pattern : Ten) (guard : d0 pattern = 1) : d119 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5003 (pattern : Ten) (guard : d0 pattern = 1) : d15 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5004 (pattern : Ten) (guard : d607 pattern = 1) : d15 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4967 pattern childGuard
    simpa only [d607, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5003 pattern childGuard
    simpa only [d607, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5005 (pattern : Ten) (guard : d608 pattern = 1) : d112 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5004 pattern childGuard
    simpa only [d608, d112, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4954 pattern childGuard
    simpa only [d608, d112, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5006 (pattern : Ten) (guard : d0 pattern = 1) : d113 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5007 (pattern : Ten) (guard : d609 pattern = 1) : d117 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5005 pattern childGuard
    simpa only [d609, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5006 pattern childGuard
    simpa only [d609, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5008 (pattern : Ten) (guard : d0 pattern = 1) : d118 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5009 (pattern : Ten) (guard : d610 pattern = 1) : d120 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5007 pattern childGuard
    simpa only [d610, d120, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5008 pattern childGuard
    simpa only [d610, d120, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5010 (pattern : Ten) (guard : d707 pattern = 1) : d121 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d707, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5002 pattern childGuard
    simpa only [d707, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d610 pattern = 1 := by simpa only [d707, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5009 pattern childGuard
    simpa only [d707, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5011 (pattern : Ten) (guard : d0 pattern = 1) : d122 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5012 (pattern : Ten) (guard : d708 pattern = 1) : d123 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d707 pattern = 1 := by simpa only [d708, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5010 pattern childGuard
    simpa only [d708, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d708, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5011 pattern childGuard
    simpa only [d708, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5013 (pattern : Ten) (guard : d0 pattern = 1) : d128 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5014 (pattern : Ten) (guard : d0 pattern = 1) : d48 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5015 (pattern : Ten) (guard : d608 pattern = 1) : d48 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4969 pattern childGuard
    simpa only [d608, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5014 pattern childGuard
    simpa only [d608, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5016 (pattern : Ten) (guard : d0 pattern = 1) : d20 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5017 (pattern : Ten) (guard : d609 pattern = 1) : d126 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5015 pattern childGuard
    simpa only [d609, d126, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5016 pattern childGuard
    simpa only [d609, d126, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5018 (pattern : Ten) (guard : d0 pattern = 1) : d127 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5019 (pattern : Ten) (guard : d610 pattern = 1) : d129 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5017 pattern childGuard
    simpa only [d610, d129, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5018 pattern childGuard
    simpa only [d610, d129, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5020 (pattern : Ten) (guard : d707 pattern = 1) : d130 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d707, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5013 pattern childGuard
    simpa only [d707, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d610 pattern = 1 := by simpa only [d707, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5019 pattern childGuard
    simpa only [d707, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5021 (pattern : Ten) (guard : d0 pattern = 1) : d131 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5022 (pattern : Ten) (guard : d708 pattern = 1) : d132 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d707 pattern = 1 := by simpa only [d708, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5020 pattern childGuard
    simpa only [d708, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d708, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5021 pattern childGuard
    simpa only [d708, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5023 (pattern : Ten) (guard : d0 pattern = 1) : d7 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5024 (pattern : Ten) (guard : d708 pattern = 1) : d133 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d707 pattern = 1 := by simpa only [d708, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4975 pattern childGuard
    simpa only [d708, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d708, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5023 pattern childGuard
    simpa only [d708, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5025 (pattern : Ten) (guard : d610 pattern = 1) : d8 pattern ≤ (0 : Int) + d8 pattern := by
  omega
theorem c5026 (pattern : Ten) (guard : d707 pattern = 1) : d134 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d707, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4965 pattern childGuard
    simpa only [d707, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d610 pattern = 1 := by simpa only [d707, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5025 pattern childGuard
    simpa only [d707, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5027 (pattern : Ten) (guard : d0 pattern = 1) : d56 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5028 (pattern : Ten) (guard : d708 pattern = 1) : d135 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d707 pattern = 1 := by simpa only [d708, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5026 pattern childGuard
    simpa only [d708, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d708, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5027 pattern childGuard
    simpa only [d708, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5029 (pattern : Ten) (guard : d0 pattern = 1) : d147 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5030 (pattern : Ten) (guard : d707 pattern = 1) : d148 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d707, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5029 pattern childGuard
    simpa only [d707, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d610 pattern = 1 := by simpa only [d707, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4961 pattern childGuard
    simpa only [d707, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5031 (pattern : Ten) (guard : d708 pattern = 1) : d149 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d707 pattern = 1 := by simpa only [d708, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5030 pattern childGuard
    simpa only [d708, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d708, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4963 pattern childGuard
    simpa only [d708, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5032 (pattern : Ten) (guard : d0 pattern = 1) : d151 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5033 (pattern : Ten) (guard : d609 pattern = 1) : d54 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4971 pattern childGuard
    simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4965 pattern childGuard
    simpa only [d609, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5034 (pattern : Ten) (guard : d0 pattern = 1) : d55 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5035 (pattern : Ten) (guard : d610 pattern = 1) : d152 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5033 pattern childGuard
    simpa only [d610, d152, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5034 pattern childGuard
    simpa only [d610, d152, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5036 (pattern : Ten) (guard : d707 pattern = 1) : d154 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d707, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5032 pattern childGuard
    simpa only [d707, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d610 pattern = 1 := by simpa only [d707, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5035 pattern childGuard
    simpa only [d707, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5037 (pattern : Ten) (guard : d0 pattern = 1) : d155 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5038 (pattern : Ten) (guard : d708 pattern = 1) : d156 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d707 pattern = 1 := by simpa only [d708, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5036 pattern childGuard
    simpa only [d708, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d708, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5037 pattern childGuard
    simpa only [d708, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5039 (pattern : Ten) (guard : d0 pattern = 1) : d165 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5040 (pattern : Ten) (guard : d609 pattern = 1) : d162 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d608 pattern = 1 := by simpa only [d609, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4971 pattern childGuard
    simpa only [d609, d162, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d609, d162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4954 pattern childGuard
    simpa only [d609, d162, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5041 (pattern : Ten) (guard : d0 pattern = 1) : d163 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5042 (pattern : Ten) (guard : d610 pattern = 1) : d166 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d609 pattern = 1 := by simpa only [d610, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5040 pattern childGuard
    simpa only [d610, d166, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d610, d166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5041 pattern childGuard
    simpa only [d610, d166, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5043 (pattern : Ten) (guard : d707 pattern = 1) : d168 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d707, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5039 pattern childGuard
    simpa only [d707, d168, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d610 pattern = 1 := by simpa only [d707, d168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5042 pattern childGuard
    simpa only [d707, d168, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5044 (pattern : Ten) (guard : d0 pattern = 1) : d169 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5045 (pattern : Ten) (guard : d708 pattern = 1) : d170 pattern ≤ (0 : Int) + d8 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d707 pattern = 1 := by simpa only [d708, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5043 pattern childGuard
    simpa only [d708, d170, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d708, d170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5044 pattern childGuard
    simpa only [d708, d170, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5046 (pattern : Ten) (guard : d0 pattern = 1) : d23 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5047 (pattern : Ten) (guard : d359 pattern = 1) : d0 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) ≤ (0 : Int) + 9
  decide
theorem c5048 (pattern : Ten) (guard : d606 pattern = 1) : d13 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5047 pattern childGuard
    simpa only [d606, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7 pattern childGuard
    simpa only [d606, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5049 (pattern : Ten) (guard : d0 pattern = 1) : d14 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5050 (pattern : Ten) (guard : d607 pattern = 1) : d19 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5048 pattern childGuard
    simpa only [d607, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5049 pattern childGuard
    simpa only [d607, d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5051 (pattern : Ten) (guard : d0 pattern = 1) : d20 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5052 (pattern : Ten) (guard : d608 pattern = 1) : d24 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5050 pattern childGuard
    simpa only [d608, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5051 pattern childGuard
    simpa only [d608, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5053 (pattern : Ten) (guard : d721 pattern = 1) : d29 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d721, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5046 pattern childGuard
    simpa only [d721, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d608 pattern = 1 := by simpa only [d721, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5052 pattern childGuard
    simpa only [d721, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5054 (pattern : Ten) (guard : d0 pattern = 1) : d30 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5055 (pattern : Ten) (guard : d722 pattern = 1) : d33 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d721 pattern = 1 := by simpa only [d722, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5053 pattern childGuard
    simpa only [d722, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d722, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5054 pattern childGuard
    simpa only [d722, d33, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5056 (pattern : Ten) (guard : d0 pattern = 1) : d34 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5057 (pattern : Ten) (guard : d723 pattern = 1) : d35 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d722 pattern = 1 := by simpa only [d723, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5055 pattern childGuard
    simpa only [d723, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d723, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5056 pattern childGuard
    simpa only [d723, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5058 (pattern : Ten) (guard : d0 pattern = 1) : d36 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5059 (pattern : Ten) (guard : d724 pattern = 1) : d37 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d723 pattern = 1 := by simpa only [d724, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5057 pattern childGuard
    simpa only [d724, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d724, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5058 pattern childGuard
    simpa only [d724, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5060 (pattern : Ten) (guard : d0 pattern = 1) : d2 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5061 (pattern : Ten) (guard : d606 pattern = 1) : d15 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5047 pattern childGuard
    simpa only [d606, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5060 pattern childGuard
    simpa only [d606, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5062 (pattern : Ten) (guard : d0 pattern = 1) : d42 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5063 (pattern : Ten) (guard : d607 pattern = 1) : d48 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5061 pattern childGuard
    simpa only [d607, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5062 pattern childGuard
    simpa only [d607, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5064 (pattern : Ten) (guard : d0 pattern = 1) : d49 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5065 (pattern : Ten) (guard : d608 pattern = 1) : d54 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5063 pattern childGuard
    simpa only [d608, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5064 pattern childGuard
    simpa only [d608, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5066 (pattern : Ten) (guard : d721 pattern = 1) : d54 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c882 pattern childGuard
    simpa only [d721, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d608 pattern = 1 := by simpa only [d721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5065 pattern childGuard
    simpa only [d721, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5067 (pattern : Ten) (guard : d722 pattern = 1) : d54 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d721 pattern = 1 := by simpa only [d722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5066 pattern childGuard
    simpa only [d722, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c882 pattern childGuard
    simpa only [d722, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5068 (pattern : Ten) (guard : d0 pattern = 1) : d62 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5069 (pattern : Ten) (guard : d723 pattern = 1) : d64 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d722 pattern = 1 := by simpa only [d723, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5067 pattern childGuard
    simpa only [d723, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d723, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5068 pattern childGuard
    simpa only [d723, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5070 (pattern : Ten) (guard : d0 pattern = 1) : d65 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5071 (pattern : Ten) (guard : d724 pattern = 1) : d66 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d723 pattern = 1 := by simpa only [d724, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5069 pattern childGuard
    simpa only [d724, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d724, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5070 pattern childGuard
    simpa only [d724, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5072 (pattern : Ten) (guard : d0 pattern = 1) : d9 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5073 (pattern : Ten) (guard : d606 pattern = 1) : d67 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d359 pattern = 1 := by simpa only [d606, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5047 pattern childGuard
    simpa only [d606, d67, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d606, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5072 pattern childGuard
    simpa only [d606, d67, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5074 (pattern : Ten) (guard : d0 pattern = 1) : d68 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5075 (pattern : Ten) (guard : d607 pattern = 1) : d69 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5073 pattern childGuard
    simpa only [d607, d69, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5074 pattern childGuard
    simpa only [d607, d69, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5076 (pattern : Ten) (guard : d0 pattern = 1) : d70 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5077 (pattern : Ten) (guard : d608 pattern = 1) : d71 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5075 pattern childGuard
    simpa only [d608, d71, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5076 pattern childGuard
    simpa only [d608, d71, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5078 (pattern : Ten) (guard : d721 pattern = 1) : d73 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d721, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5046 pattern childGuard
    simpa only [d721, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d608 pattern = 1 := by simpa only [d721, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5077 pattern childGuard
    simpa only [d721, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5079 (pattern : Ten) (guard : d0 pattern = 1) : d74 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5080 (pattern : Ten) (guard : d722 pattern = 1) : d77 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d721 pattern = 1 := by simpa only [d722, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5078 pattern childGuard
    simpa only [d722, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d722, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5079 pattern childGuard
    simpa only [d722, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5081 (pattern : Ten) (guard : d0 pattern = 1) : d78 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5082 (pattern : Ten) (guard : d723 pattern = 1) : d79 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d722 pattern = 1 := by simpa only [d723, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5080 pattern childGuard
    simpa only [d723, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d723, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5081 pattern childGuard
    simpa only [d723, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5083 (pattern : Ten) (guard : d0 pattern = 1) : d80 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5084 (pattern : Ten) (guard : d724 pattern = 1) : d81 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d723 pattern = 1 := by simpa only [d724, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5082 pattern childGuard
    simpa only [d724, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d724, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5083 pattern childGuard
    simpa only [d724, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5085 (pattern : Ten) (guard : d0 pattern = 1) : d7 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5086 (pattern : Ten) (guard : d722 pattern = 1) : d82 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d721 pattern = 1 := by simpa only [d722, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5066 pattern childGuard
    simpa only [d722, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d722, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5085 pattern childGuard
    simpa only [d722, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5087 (pattern : Ten) (guard : d0 pattern = 1) : d58 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5088 (pattern : Ten) (guard : d723 pattern = 1) : d83 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d722 pattern = 1 := by simpa only [d723, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5086 pattern childGuard
    simpa only [d723, d83, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d723, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5087 pattern childGuard
    simpa only [d723, d83, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5089 (pattern : Ten) (guard : d0 pattern = 1) : d84 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5090 (pattern : Ten) (guard : d724 pattern = 1) : d85 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d723 pattern = 1 := by simpa only [d724, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5088 pattern childGuard
    simpa only [d724, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d724, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5089 pattern childGuard
    simpa only [d724, d85, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5091 (pattern : Ten) (guard : d0 pattern = 1) : d93 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5092 (pattern : Ten) (guard : d606 pattern = 1) : d0 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) ≤ (0 : Int) + 9
  decide
theorem c5093 (pattern : Ten) (guard : d607 pattern = 1) : d89 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5092 pattern childGuard
    simpa only [d607, d89, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7 pattern childGuard
    simpa only [d607, d89, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5094 (pattern : Ten) (guard : d0 pattern = 1) : d90 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5095 (pattern : Ten) (guard : d608 pattern = 1) : d94 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5093 pattern childGuard
    simpa only [d608, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5094 pattern childGuard
    simpa only [d608, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5096 (pattern : Ten) (guard : d721 pattern = 1) : d99 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d721, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5091 pattern childGuard
    simpa only [d721, d99, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d608 pattern = 1 := by simpa only [d721, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5095 pattern childGuard
    simpa only [d721, d99, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5097 (pattern : Ten) (guard : d0 pattern = 1) : d100 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5098 (pattern : Ten) (guard : d722 pattern = 1) : d103 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d721 pattern = 1 := by simpa only [d722, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5096 pattern childGuard
    simpa only [d722, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d722, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5097 pattern childGuard
    simpa only [d722, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5099 (pattern : Ten) (guard : d0 pattern = 1) : d104 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5100 (pattern : Ten) (guard : d723 pattern = 1) : d105 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d722 pattern = 1 := by simpa only [d723, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5098 pattern childGuard
    simpa only [d723, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d723, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5099 pattern childGuard
    simpa only [d723, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5101 (pattern : Ten) (guard : d0 pattern = 1) : d106 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5102 (pattern : Ten) (guard : d724 pattern = 1) : d107 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d723 pattern = 1 := by simpa only [d724, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5100 pattern childGuard
    simpa only [d724, d107, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d724, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5101 pattern childGuard
    simpa only [d724, d107, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5103 (pattern : Ten) (guard : d0 pattern = 1) : d109 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5104 (pattern : Ten) (guard : d0 pattern = 1) : d15 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5105 (pattern : Ten) (guard : d607 pattern = 1) : d15 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d606 pattern = 1 := by simpa only [d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5061 pattern childGuard
    simpa only [d607, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5104 pattern childGuard
    simpa only [d607, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5106 (pattern : Ten) (guard : d608 pattern = 1) : d110 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5105 pattern childGuard
    simpa only [d608, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5049 pattern childGuard
    simpa only [d608, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5107 (pattern : Ten) (guard : d721 pattern = 1) : d115 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d721, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5103 pattern childGuard
    simpa only [d721, d115, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d608 pattern = 1 := by simpa only [d721, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5106 pattern childGuard
    simpa only [d721, d115, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5108 (pattern : Ten) (guard : d0 pattern = 1) : d116 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5109 (pattern : Ten) (guard : d722 pattern = 1) : d119 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d721 pattern = 1 := by simpa only [d722, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5107 pattern childGuard
    simpa only [d722, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d722, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5108 pattern childGuard
    simpa only [d722, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5110 (pattern : Ten) (guard : d0 pattern = 1) : d120 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5111 (pattern : Ten) (guard : d723 pattern = 1) : d121 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d722 pattern = 1 := by simpa only [d723, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5109 pattern childGuard
    simpa only [d723, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d723, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5110 pattern childGuard
    simpa only [d723, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5112 (pattern : Ten) (guard : d0 pattern = 1) : d122 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5113 (pattern : Ten) (guard : d724 pattern = 1) : d123 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d723 pattern = 1 := by simpa only [d724, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5111 pattern childGuard
    simpa only [d724, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d724, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5112 pattern childGuard
    simpa only [d724, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5114 (pattern : Ten) (guard : d0 pattern = 1) : d124 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5115 (pattern : Ten) (guard : d0 pattern = 1) : d48 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5116 (pattern : Ten) (guard : d608 pattern = 1) : d48 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d607 pattern = 1 := by simpa only [d608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5063 pattern childGuard
    simpa only [d608, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5115 pattern childGuard
    simpa only [d608, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5117 (pattern : Ten) (guard : d721 pattern = 1) : d125 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d721, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5114 pattern childGuard
    simpa only [d721, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d608 pattern = 1 := by simpa only [d721, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5116 pattern childGuard
    simpa only [d721, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5118 (pattern : Ten) (guard : d722 pattern = 1) : d128 pattern ≤ (0 : Int) + d9 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d721 pattern = 1 := by simpa only [d722, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5117 pattern childGuard
    simpa only [d722, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d722, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5115 pattern childGuard
    simpa only [d722, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5119 (pattern : Ten) (guard : d0 pattern = 1) : d129 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban41.Diagram
