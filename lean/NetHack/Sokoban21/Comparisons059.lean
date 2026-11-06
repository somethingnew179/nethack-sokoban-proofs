/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons058
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c8260 (pattern : Twelve) (guard : d1867 pattern = 1) : d674 pattern ≤ (0 : Int) + d526 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d674, d526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8135 pattern childGuard
    simpa only [d674, d526, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d674, d526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8216 pattern childGuard
    simpa only [d674, d526, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8261 (pattern : Twelve) (guard : d1867 pattern = 1) : d705 pattern ≤ (0 : Int) + d557 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d705, d557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8260 pattern childGuard
    simpa only [d705, d557, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d705, d557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8142 pattern childGuard
    simpa only [d705, d557, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8262 (pattern : Twelve) (guard : d1867 pattern = 1) : d729 pattern ≤ (0 : Int) + d581 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d729, d581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8135 pattern childGuard
    simpa only [d729, d581, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d729, d581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8261 pattern childGuard
    simpa only [d729, d581, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8263 (pattern : Twelve) (guard : d1867 pattern = 1) : d749 pattern ≤ (0 : Int) + d601 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d749, d601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8231 pattern childGuard
    simpa only [d749, d601, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d749, d601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8262 pattern childGuard
    simpa only [d749, d601, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8264 (pattern : Twelve) (guard : d1867 pattern = 1) : d730 pattern ≤ (0 : Int) + d582 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d730, d582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8237 pattern childGuard
    simpa only [d730, d582, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d730, d582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8186 pattern childGuard
    simpa only [d730, d582, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8265 (pattern : Twelve) (guard : d1867 pattern = 1) : d731 pattern ≤ (0 : Int) + d583 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d731, d583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8186 pattern childGuard
    simpa only [d731, d583, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d731, d583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8261 pattern childGuard
    simpa only [d731, d583, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8266 (pattern : Twelve) (guard : d1867 pattern = 1) : d750 pattern ≤ (0 : Int) + d602 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d750, d602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8264 pattern childGuard
    simpa only [d750, d602, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d750, d602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8265 pattern childGuard
    simpa only [d750, d602, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8267 (pattern : Twelve) (guard : d1867 pattern = 1) : d762 pattern ≤ (0 : Int) + d614 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d762, d614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8263 pattern childGuard
    simpa only [d762, d614, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d762, d614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8266 pattern childGuard
    simpa only [d762, d614, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8268 (pattern : Twelve) (guard : d1867 pattern = 1) : d751 pattern ≤ (0 : Int) + d603 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d751, d603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8186 pattern childGuard
    simpa only [d751, d603, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d751, d603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8265 pattern childGuard
    simpa only [d751, d603, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8269 (pattern : Twelve) (guard : d1867 pattern = 1) : d763 pattern ≤ (0 : Int) + d615 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d763, d615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8263 pattern childGuard
    simpa only [d763, d615, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d763, d615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8268 pattern childGuard
    simpa only [d763, d615, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8270 (pattern : Twelve) (guard : d1867 pattern = 1) : d770 pattern ≤ (0 : Int) + d622 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d770, d622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8267 pattern childGuard
    simpa only [d770, d622, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d770, d622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8269 pattern childGuard
    simpa only [d770, d622, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8271 (pattern : Twelve) (guard : d1867 pattern = 1) : d675 pattern ≤ (0 : Int) + d527 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d675, d527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8135 pattern childGuard
    simpa only [d675, d527, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d675, d527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8209 pattern childGuard
    simpa only [d675, d527, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8272 (pattern : Twelve) (guard : d1867 pattern = 1) : d706 pattern ≤ (0 : Int) + d558 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d706, d558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8164 pattern childGuard
    simpa only [d706, d558, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d706, d558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8271 pattern childGuard
    simpa only [d706, d558, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8273 (pattern : Twelve) (guard : d1867 pattern = 1) : d732 pattern ≤ (0 : Int) + d584 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d732, d584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8164 pattern childGuard
    simpa only [d732, d584, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d732, d584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8272 pattern childGuard
    simpa only [d732, d584, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8274 (pattern : Twelve) (guard : d1867 pattern = 1) : d733 pattern ≤ (0 : Int) + d585 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d733, d585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8249 pattern childGuard
    simpa only [d733, d585, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d733, d585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8261 pattern childGuard
    simpa only [d733, d585, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8275 (pattern : Twelve) (guard : d1867 pattern = 1) : d752 pattern ≤ (0 : Int) + d604 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d752, d604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8273 pattern childGuard
    simpa only [d752, d604, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d752, d604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8274 pattern childGuard
    simpa only [d752, d604, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8276 (pattern : Twelve) (guard : d1867 pattern = 1) : d14 pattern ≤ (0 : Int) + d497 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7908 pattern childGuard
    simpa only [d1867, d497, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2875 pattern childGuard
    simpa only [d1867, d497, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8277 (pattern : Twelve) (guard : d1867 pattern = 1) : d676 pattern ≤ (0 : Int) + d528 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d676, d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8156 pattern childGuard
    simpa only [d676, d528, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d676, d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8276 pattern childGuard
    simpa only [d676, d528, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8278 (pattern : Twelve) (guard : d1867 pattern = 1) : d677 pattern ≤ (0 : Int) + d529 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d677, d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8200 pattern childGuard
    simpa only [d677, d529, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d677, d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d677, d529, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8279 (pattern : Twelve) (guard : d1867 pattern = 1) : d707 pattern ≤ (0 : Int) + d559 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d707, d559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8277 pattern childGuard
    simpa only [d707, d559, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d707, d559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8278 pattern childGuard
    simpa only [d707, d559, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8280 (pattern : Twelve) (guard : d1867 pattern = 1) : d734 pattern ≤ (0 : Int) + d586 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d734, d586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8214 pattern childGuard
    simpa only [d734, d586, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d734, d586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8279 pattern childGuard
    simpa only [d734, d586, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8281 (pattern : Twelve) (guard : d1867 pattern = 1) : d678 pattern ≤ (0 : Int) + d530 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d678, d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8156 pattern childGuard
    simpa only [d678, d530, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d678, d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3302 pattern childGuard
    simpa only [d678, d530, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8282 (pattern : Twelve) (guard : d1867 pattern = 1) : d679 pattern ≤ (0 : Int) + d531 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d679, d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8153 pattern childGuard
    simpa only [d679, d531, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d679, d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d679, d531, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8283 (pattern : Twelve) (guard : d1867 pattern = 1) : d708 pattern ≤ (0 : Int) + d560 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d708, d560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8281 pattern childGuard
    simpa only [d708, d560, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d708, d560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8282 pattern childGuard
    simpa only [d708, d560, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8284 (pattern : Twelve) (guard : d1867 pattern = 1) : d735 pattern ≤ (0 : Int) + d587 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d735, d587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8279 pattern childGuard
    simpa only [d735, d587, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d735, d587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8283 pattern childGuard
    simpa only [d735, d587, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8285 (pattern : Twelve) (guard : d1867 pattern = 1) : d753 pattern ≤ (0 : Int) + d605 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d753, d605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8280 pattern childGuard
    simpa only [d753, d605, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d753, d605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8284 pattern childGuard
    simpa only [d753, d605, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8286 (pattern : Twelve) (guard : d1867 pattern = 1) : d764 pattern ≤ (0 : Int) + d616 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d764, d616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8275 pattern childGuard
    simpa only [d764, d616, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d764, d616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8285 pattern childGuard
    simpa only [d764, d616, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8287 (pattern : Twelve) (guard : d1867 pattern = 1) : d765 pattern ≤ (0 : Int) + d617 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d765, d617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8268 pattern childGuard
    simpa only [d765, d617, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d765, d617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d765, d617, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8288 (pattern : Twelve) (guard : d1867 pattern = 1) : d771 pattern ≤ (0 : Int) + d623 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d771, d623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8286 pattern childGuard
    simpa only [d771, d623, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d771, d623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8287 pattern childGuard
    simpa only [d771, d623, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8289 (pattern : Twelve) (guard : d1867 pattern = 1) : d774 pattern ≤ (0 : Int) + d626 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d774, d626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8270 pattern childGuard
    simpa only [d774, d626, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d774, d626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8288 pattern childGuard
    simpa only [d774, d626, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8290 (pattern : Twelve) (guard : d1867 pattern = 1) : d777 pattern ≤ (0 : Int) + d629 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d777, d629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8259 pattern childGuard
    simpa only [d777, d629, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d777, d629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8289 pattern childGuard
    simpa only [d777, d629, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8291 (pattern : Twelve) (guard : d1867 pattern = 1) : d636 pattern ≤ (0 : Int) + d1105 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d636, d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7739 pattern childGuard
    simpa only [d1867, d636, d1105, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d636, d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8129 pattern childGuard
    simpa only [d1867, d636, d1105, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8292 (pattern : Twelve) (guard : d1867 pattern = 1) : d1183 pattern ≤ (0 : Int) + d1108 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1183, d1108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8291 pattern childGuard
    simpa only [d1183, d1108, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1183, d1108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8130 pattern childGuard
    simpa only [d1183, d1108, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8293 (pattern : Twelve) (guard : d1867 pattern = 1) : d1189 pattern ≤ (0 : Int) + d1118 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1189, d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8131 pattern childGuard
    simpa only [d1189, d1118, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1189, d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8292 pattern childGuard
    simpa only [d1189, d1118, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8294 (pattern : Twelve) (guard : d1867 pattern = 1) : d1199 pattern ≤ (0 : Int) + d1132 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1199, d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8137 pattern childGuard
    simpa only [d1199, d1132, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1199, d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8293 pattern childGuard
    simpa only [d1199, d1132, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8295 (pattern : Twelve) (guard : d1867 pattern = 1) : d1190 pattern ≤ (0 : Int) + d1119 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1190, d1119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8136 pattern childGuard
    simpa only [d1190, d1119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1190, d1119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8135 pattern childGuard
    simpa only [d1190, d1119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8296 (pattern : Twelve) (guard : d1867 pattern = 1) : d1184 pattern ≤ (0 : Int) + d1109 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1184, d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8141 pattern childGuard
    simpa only [d1184, d1109, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1184, d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8216 pattern childGuard
    simpa only [d1184, d1109, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8297 (pattern : Twelve) (guard : d1867 pattern = 1) : d1191 pattern ≤ (0 : Int) + d1120 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1191, d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8296 pattern childGuard
    simpa only [d1191, d1120, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1191, d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8217 pattern childGuard
    simpa only [d1191, d1120, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8298 (pattern : Twelve) (guard : d1867 pattern = 1) : d1200 pattern ≤ (0 : Int) + d1133 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1200, d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8295 pattern childGuard
    simpa only [d1200, d1133, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1200, d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8297 pattern childGuard
    simpa only [d1200, d1133, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8299 (pattern : Twelve) (guard : d1867 pattern = 1) : d1216 pattern ≤ (0 : Int) + d1152 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1216, d1152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8294 pattern childGuard
    simpa only [d1216, d1152, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1216, d1152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8298 pattern childGuard
    simpa only [d1216, d1152, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8300 (pattern : Twelve) (guard : d1867 pattern = 1) : d1192 pattern ≤ (0 : Int) + d1121 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1192, d1121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8157 pattern childGuard
    simpa only [d1192, d1121, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1192, d1121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8184 pattern childGuard
    simpa only [d1192, d1121, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8301 (pattern : Twelve) (guard : d1867 pattern = 1) : d651 pattern ≤ (0 : Int) + d1110 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d651, d1110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8291 pattern childGuard
    simpa only [d651, d1110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d651, d1110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d651, d1110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8302 (pattern : Twelve) (guard : d1867 pattern = 1) : d687 pattern ≤ (0 : Int) + d1122 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d687, d1122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8164 pattern childGuard
    simpa only [d687, d1122, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d687, d1122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8301 pattern childGuard
    simpa only [d687, d1122, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8303 (pattern : Twelve) (guard : d1867 pattern = 1) : d1201 pattern ≤ (0 : Int) + d1134 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1201, d1134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8300 pattern childGuard
    simpa only [d1201, d1134, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1201, d1134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8302 pattern childGuard
    simpa only [d1201, d1134, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8304 (pattern : Twelve) (guard : d1867 pattern = 1) : d1202 pattern ≤ (0 : Int) + d1135 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1202, d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8186 pattern childGuard
    simpa only [d1202, d1135, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1202, d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8297 pattern childGuard
    simpa only [d1202, d1135, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8305 (pattern : Twelve) (guard : d1867 pattern = 1) : d1217 pattern ≤ (0 : Int) + d1153 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1217, d1153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8303 pattern childGuard
    simpa only [d1217, d1153, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1217, d1153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8304 pattern childGuard
    simpa only [d1217, d1153, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8306 (pattern : Twelve) (guard : d1867 pattern = 1) : d1228 pattern ≤ (0 : Int) + d1164 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1228, d1164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8299 pattern childGuard
    simpa only [d1228, d1164, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1228, d1164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8305 pattern childGuard
    simpa only [d1228, d1164, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8307 (pattern : Twelve) (guard : d1867 pattern = 1) : d1193 pattern ≤ (0 : Int) + d1123 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1193, d1123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8175 pattern childGuard
    simpa only [d1193, d1123, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1193, d1123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8292 pattern childGuard
    simpa only [d1193, d1123, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8308 (pattern : Twelve) (guard : d1867 pattern = 1) : d1203 pattern ≤ (0 : Int) + d1136 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1203, d1136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8178 pattern childGuard
    simpa only [d1203, d1136, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1203, d1136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8307 pattern childGuard
    simpa only [d1203, d1136, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8309 (pattern : Twelve) (guard : d1867 pattern = 1) : d1204 pattern ≤ (0 : Int) + d1137 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1204, d1137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8135 pattern childGuard
    simpa only [d1204, d1137, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1204, d1137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8297 pattern childGuard
    simpa only [d1204, d1137, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8310 (pattern : Twelve) (guard : d1867 pattern = 1) : d1218 pattern ≤ (0 : Int) + d1154 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1218, d1154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8308 pattern childGuard
    simpa only [d1218, d1154, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1218, d1154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8309 pattern childGuard
    simpa only [d1218, d1154, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8311 (pattern : Twelve) (guard : d1867 pattern = 1) : d716 pattern ≤ (0 : Int) + d1138 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d716, d1138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8186 pattern childGuard
    simpa only [d716, d1138, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d716, d1138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8302 pattern childGuard
    simpa only [d716, d1138, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8312 (pattern : Twelve) (guard : d1867 pattern = 1) : d1219 pattern ≤ (0 : Int) + d1155 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1219, d1155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8311 pattern childGuard
    simpa only [d1219, d1155, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1219, d1155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8304 pattern childGuard
    simpa only [d1219, d1155, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8313 (pattern : Twelve) (guard : d1867 pattern = 1) : d1229 pattern ≤ (0 : Int) + d1165 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1229, d1165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8310 pattern childGuard
    simpa only [d1229, d1165, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1229, d1165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8312 pattern childGuard
    simpa only [d1229, d1165, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8314 (pattern : Twelve) (guard : d1867 pattern = 1) : d1237 pattern ≤ (0 : Int) + d1173 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1237, d1173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8306 pattern childGuard
    simpa only [d1237, d1173, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1237, d1173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8313 pattern childGuard
    simpa only [d1237, d1173, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8315 (pattern : Twelve) (guard : d1867 pattern = 1) : d1185 pattern ≤ (0 : Int) + d1111 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1185, d1111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8291 pattern childGuard
    simpa only [d1185, d1111, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1185, d1111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8200 pattern childGuard
    simpa only [d1185, d1111, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8316 (pattern : Twelve) (guard : d1867 pattern = 1) : d1194 pattern ≤ (0 : Int) + d1124 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1194, d1124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8164 pattern childGuard
    simpa only [d1194, d1124, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1194, d1124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8315 pattern childGuard
    simpa only [d1194, d1124, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8317 (pattern : Twelve) (guard : d1867 pattern = 1) : d1205 pattern ≤ (0 : Int) + d1139 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1205, d1139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8204 pattern childGuard
    simpa only [d1205, d1139, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1205, d1139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8316 pattern childGuard
    simpa only [d1205, d1139, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8318 (pattern : Twelve) (guard : d1867 pattern = 1) : d1206 pattern ≤ (0 : Int) + d1140 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1206, d1140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8164 pattern childGuard
    simpa only [d1206, d1140, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1206, d1140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8297 pattern childGuard
    simpa only [d1206, d1140, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8319 (pattern : Twelve) (guard : d1867 pattern = 1) : d1220 pattern ≤ (0 : Int) + d1156 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1220, d1156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8317 pattern childGuard
    simpa only [d1220, d1156, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1220, d1156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8318 pattern childGuard
    simpa only [d1220, d1156, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8320 (pattern : Twelve) (guard : d1867 pattern = 1) : d644 pattern ≤ (0 : Int) + d1106 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d644, d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7748 pattern childGuard
    simpa only [d1867, d644, d1106, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d644, d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8199 pattern childGuard
    simpa only [d1867, d644, d1106, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8321 (pattern : Twelve) (guard : d1867 pattern = 1) : d670 pattern ≤ (0 : Int) + d1112 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d670, d1112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8320 pattern childGuard
    simpa only [d670, d1112, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d670, d1112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d670, d1112, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8322 (pattern : Twelve) (guard : d1867 pattern = 1) : d698 pattern ≤ (0 : Int) + d1125 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d698, d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8213 pattern childGuard
    simpa only [d698, d1125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d698, d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8321 pattern childGuard
    simpa only [d698, d1125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8323 (pattern : Twelve) (guard : d1867 pattern = 1) : d720 pattern ≤ (0 : Int) + d1141 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d720, d1141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8214 pattern childGuard
    simpa only [d720, d1141, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d720, d1141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8322 pattern childGuard
    simpa only [d720, d1141, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8324 (pattern : Twelve) (guard : d1867 pattern = 1) : d1186 pattern ≤ (0 : Int) + d1113 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1186, d1113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8216 pattern childGuard
    simpa only [d1186, d1113, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1186, d1113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8158 pattern childGuard
    simpa only [d1186, d1113, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8325 (pattern : Twelve) (guard : d1867 pattern = 1) : d822 pattern ≤ (0 : Int) + d178 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d822, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8158 pattern childGuard
    simpa only [d822, d178, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d822, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d822, d178, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8326 (pattern : Twelve) (guard : d1867 pattern = 1) : d1195 pattern ≤ (0 : Int) + d1126 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1195, d1126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8324 pattern childGuard
    simpa only [d1195, d1126, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1195, d1126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8325 pattern childGuard
    simpa only [d1195, d1126, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8327 (pattern : Twelve) (guard : d1867 pattern = 1) : d1207 pattern ≤ (0 : Int) + d1142 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1207, d1142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8214 pattern childGuard
    simpa only [d1207, d1142, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1207, d1142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8326 pattern childGuard
    simpa only [d1207, d1142, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8328 (pattern : Twelve) (guard : d1867 pattern = 1) : d1221 pattern ≤ (0 : Int) + d1157 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1221, d1157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8323 pattern childGuard
    simpa only [d1221, d1157, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1221, d1157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8327 pattern childGuard
    simpa only [d1221, d1157, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8329 (pattern : Twelve) (guard : d1867 pattern = 1) : d1230 pattern ≤ (0 : Int) + d1166 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1230, d1166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8319 pattern childGuard
    simpa only [d1230, d1166, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1230, d1166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8328 pattern childGuard
    simpa only [d1230, d1166, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8330 (pattern : Twelve) (guard : d1867 pattern = 1) : d1231 pattern ≤ (0 : Int) + d1167 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1231, d1167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8312 pattern childGuard
    simpa only [d1231, d1167, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1231, d1167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1231, d1167, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8331 (pattern : Twelve) (guard : d1867 pattern = 1) : d1238 pattern ≤ (0 : Int) + d1174 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1238, d1174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8329 pattern childGuard
    simpa only [d1238, d1174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1238, d1174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8330 pattern childGuard
    simpa only [d1238, d1174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8332 (pattern : Twelve) (guard : d1867 pattern = 1) : d1241 pattern ≤ (0 : Int) + d1177 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1241, d1177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8314 pattern childGuard
    simpa only [d1241, d1177, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1241, d1177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8331 pattern childGuard
    simpa only [d1241, d1177, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8333 (pattern : Twelve) (guard : d1867 pattern = 1) : d1208 pattern ≤ (0 : Int) + d1143 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1208, d1143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8135 pattern childGuard
    simpa only [d1208, d1143, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1208, d1143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8307 pattern childGuard
    simpa only [d1208, d1143, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8334 (pattern : Twelve) (guard : d1867 pattern = 1) : d1222 pattern ≤ (0 : Int) + d1158 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1222, d1158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8333 pattern childGuard
    simpa only [d1222, d1158, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1222, d1158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8309 pattern childGuard
    simpa only [d1222, d1158, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8335 (pattern : Twelve) (guard : d1867 pattern = 1) : d1232 pattern ≤ (0 : Int) + d1168 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1232, d1168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8334 pattern childGuard
    simpa only [d1232, d1168, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1232, d1168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8312 pattern childGuard
    simpa only [d1232, d1168, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8336 (pattern : Twelve) (guard : d1867 pattern = 1) : d1209 pattern ≤ (0 : Int) + d1144 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1209, d1144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8164 pattern childGuard
    simpa only [d1209, d1144, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1209, d1144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8316 pattern childGuard
    simpa only [d1209, d1144, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8337 (pattern : Twelve) (guard : d1867 pattern = 1) : d1223 pattern ≤ (0 : Int) + d1159 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1223, d1159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8336 pattern childGuard
    simpa only [d1223, d1159, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1223, d1159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8318 pattern childGuard
    simpa only [d1223, d1159, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8338 (pattern : Twelve) (guard : d1867 pattern = 1) : d1233 pattern ≤ (0 : Int) + d1169 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1233, d1169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8337 pattern childGuard
    simpa only [d1233, d1169, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1233, d1169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8328 pattern childGuard
    simpa only [d1233, d1169, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8339 (pattern : Twelve) (guard : d1867 pattern = 1) : d1239 pattern ≤ (0 : Int) + d1175 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1239, d1175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8338 pattern childGuard
    simpa only [d1239, d1175, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1239, d1175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8330 pattern childGuard
    simpa only [d1239, d1175, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8340 (pattern : Twelve) (guard : d1867 pattern = 1) : d1242 pattern ≤ (0 : Int) + d1178 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1242, d1178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8335 pattern childGuard
    simpa only [d1242, d1178, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1242, d1178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8339 pattern childGuard
    simpa only [d1242, d1178, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8341 (pattern : Twelve) (guard : d1867 pattern = 1) : d1244 pattern ≤ (0 : Int) + d1180 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1244, d1180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8332 pattern childGuard
    simpa only [d1244, d1180, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1244, d1180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8340 pattern childGuard
    simpa only [d1244, d1180, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8342 (pattern : Twelve) (guard : d1867 pattern = 1) : d1245 pattern ≤ (0 : Int) + d1181 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1245, d1181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8341 pattern childGuard
    simpa only [d1245, d1181, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1245, d1181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8340 pattern childGuard
    simpa only [d1245, d1181, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8343 (pattern : Twelve) (guard : d1867 pattern = 1) : d1187 pattern ≤ (0 : Int) + d1114 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1187, d1114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8141 pattern childGuard
    simpa only [d1187, d1114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1187, d1114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8158 pattern childGuard
    simpa only [d1187, d1114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8344 (pattern : Twelve) (guard : d1867 pattern = 1) : d1196 pattern ≤ (0 : Int) + d1127 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1196, d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8343 pattern childGuard
    simpa only [d1196, d1127, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1196, d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8217 pattern childGuard
    simpa only [d1196, d1127, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8345 (pattern : Twelve) (guard : d1867 pattern = 1) : d1210 pattern ≤ (0 : Int) + d1145 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1210, d1145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8135 pattern childGuard
    simpa only [d1210, d1145, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1210, d1145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8344 pattern childGuard
    simpa only [d1210, d1145, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8346 (pattern : Twelve) (guard : d1867 pattern = 1) : d1224 pattern ≤ (0 : Int) + d1160 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1224, d1160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8333 pattern childGuard
    simpa only [d1224, d1160, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1224, d1160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8345 pattern childGuard
    simpa only [d1224, d1160, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8347 (pattern : Twelve) (guard : d1867 pattern = 1) : d674 pattern ≤ (0 : Int) + d1115 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d674, d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8135 pattern childGuard
    simpa only [d674, d1115, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d674, d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8320 pattern childGuard
    simpa only [d674, d1115, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8348 (pattern : Twelve) (guard : d1867 pattern = 1) : d705 pattern ≤ (0 : Int) + d1128 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d705, d1128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8347 pattern childGuard
    simpa only [d705, d1128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d705, d1128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8301 pattern childGuard
    simpa only [d705, d1128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8349 (pattern : Twelve) (guard : d1867 pattern = 1) : d731 pattern ≤ (0 : Int) + d1146 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d731, d1146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8186 pattern childGuard
    simpa only [d731, d1146, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d731, d1146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8348 pattern childGuard
    simpa only [d731, d1146, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8350 (pattern : Twelve) (guard : d1867 pattern = 1) : d1211 pattern ≤ (0 : Int) + d1147 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1211, d1147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8186 pattern childGuard
    simpa only [d1211, d1147, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1211, d1147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8344 pattern childGuard
    simpa only [d1211, d1147, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8351 (pattern : Twelve) (guard : d1867 pattern = 1) : d1225 pattern ≤ (0 : Int) + d1161 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1225, d1161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8349 pattern childGuard
    simpa only [d1225, d1161, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1225, d1161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8350 pattern childGuard
    simpa only [d1225, d1161, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8352 (pattern : Twelve) (guard : d1867 pattern = 1) : d1234 pattern ≤ (0 : Int) + d1170 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1234, d1170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8346 pattern childGuard
    simpa only [d1234, d1170, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1234, d1170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8351 pattern childGuard
    simpa only [d1234, d1170, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8353 (pattern : Twelve) (guard : d1867 pattern = 1) : d1188 pattern ≤ (0 : Int) + d1116 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1188, d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8291 pattern childGuard
    simpa only [d1188, d1116, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1188, d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8209 pattern childGuard
    simpa only [d1188, d1116, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8354 (pattern : Twelve) (guard : d1867 pattern = 1) : d1197 pattern ≤ (0 : Int) + d1129 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1197, d1129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8347 pattern childGuard
    simpa only [d1197, d1129, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1197, d1129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8353 pattern childGuard
    simpa only [d1197, d1129, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8355 (pattern : Twelve) (guard : d1867 pattern = 1) : d1212 pattern ≤ (0 : Int) + d1148 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1212, d1148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8164 pattern childGuard
    simpa only [d1212, d1148, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1212, d1148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8354 pattern childGuard
    simpa only [d1212, d1148, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8356 (pattern : Twelve) (guard : d1867 pattern = 1) : d1213 pattern ≤ (0 : Int) + d1149 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1213, d1149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8249 pattern childGuard
    simpa only [d1213, d1149, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1213, d1149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8344 pattern childGuard
    simpa only [d1213, d1149, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8357 (pattern : Twelve) (guard : d1867 pattern = 1) : d1226 pattern ≤ (0 : Int) + d1162 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1226, d1162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8355 pattern childGuard
    simpa only [d1226, d1162, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1226, d1162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8356 pattern childGuard
    simpa only [d1226, d1162, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8358 (pattern : Twelve) (guard : d1867 pattern = 1) : d639 pattern ≤ (0 : Int) + d1107 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d639, d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7911 pattern childGuard
    simpa only [d1867, d639, d1107, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d639, d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2866 pattern childGuard
    simpa only [d1867, d639, d1107, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8359 (pattern : Twelve) (guard : d1867 pattern = 1) : d679 pattern ≤ (0 : Int) + d1117 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d679, d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8358 pattern childGuard
    simpa only [d679, d1117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d679, d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d679, d1117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8360 (pattern : Twelve) (guard : d1867 pattern = 1) : d708 pattern ≤ (0 : Int) + d1130 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d708, d1130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8281 pattern childGuard
    simpa only [d708, d1130, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d708, d1130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8359 pattern childGuard
    simpa only [d708, d1130, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8361 (pattern : Twelve) (guard : d1867 pattern = 1) : d1214 pattern ≤ (0 : Int) + d1150 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1214, d1150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8214 pattern childGuard
    simpa only [d1214, d1150, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1214, d1150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8360 pattern childGuard
    simpa only [d1214, d1150, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8362 (pattern : Twelve) (guard : d1867 pattern = 1) : d1198 pattern ≤ (0 : Int) + d1131 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1198, d1131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8217 pattern childGuard
    simpa only [d1198, d1131, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1198, d1131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1198, d1131, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8363 (pattern : Twelve) (guard : d1867 pattern = 1) : d1215 pattern ≤ (0 : Int) + d1151 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1215, d1151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8279 pattern childGuard
    simpa only [d1215, d1151, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1215, d1151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8362 pattern childGuard
    simpa only [d1215, d1151, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8364 (pattern : Twelve) (guard : d1867 pattern = 1) : d1227 pattern ≤ (0 : Int) + d1163 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1227, d1163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8361 pattern childGuard
    simpa only [d1227, d1163, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1227, d1163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8363 pattern childGuard
    simpa only [d1227, d1163, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8365 (pattern : Twelve) (guard : d1867 pattern = 1) : d1235 pattern ≤ (0 : Int) + d1171 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1235, d1171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8357 pattern childGuard
    simpa only [d1235, d1171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1235, d1171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8364 pattern childGuard
    simpa only [d1235, d1171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8366 (pattern : Twelve) (guard : d1867 pattern = 1) : d1236 pattern ≤ (0 : Int) + d1172 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1236, d1172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8351 pattern childGuard
    simpa only [d1236, d1172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1236, d1172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1236, d1172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8367 (pattern : Twelve) (guard : d1867 pattern = 1) : d1240 pattern ≤ (0 : Int) + d1176 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1240, d1176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8365 pattern childGuard
    simpa only [d1240, d1176, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1240, d1176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8366 pattern childGuard
    simpa only [d1240, d1176, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8368 (pattern : Twelve) (guard : d1867 pattern = 1) : d1243 pattern ≤ (0 : Int) + d1179 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1243, d1179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8352 pattern childGuard
    simpa only [d1243, d1179, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1243, d1179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8367 pattern childGuard
    simpa only [d1243, d1179, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8369 (pattern : Twelve) (guard : d1867 pattern = 1) : d1246 pattern ≤ (0 : Int) + d1182 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1246, d1182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8342 pattern childGuard
    simpa only [d1246, d1182, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1246, d1182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8368 pattern childGuard
    simpa only [d1246, d1182, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8370 (pattern : Twelve) (guard : d1867 pattern = 1) : d1564 pattern ≤ (0 : Int) + d1505 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1564, d1505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8292 pattern childGuard
    simpa only [d1564, d1505, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1564, d1505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8130 pattern childGuard
    simpa only [d1564, d1505, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8371 (pattern : Twelve) (guard : d1867 pattern = 1) : d1576 pattern ≤ (0 : Int) + d1517 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1576, d1517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8295 pattern childGuard
    simpa only [d1576, d1517, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1576, d1517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8370 pattern childGuard
    simpa only [d1576, d1517, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8372 (pattern : Twelve) (guard : d1867 pattern = 1) : d1577 pattern ≤ (0 : Int) + d1518 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1577, d1518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8141 pattern childGuard
    simpa only [d1577, d1518, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1577, d1518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1577, d1518, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8373 (pattern : Twelve) (guard : d1867 pattern = 1) : d1591 pattern ≤ (0 : Int) + d1532 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1591, d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8371 pattern childGuard
    simpa only [d1591, d1532, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1591, d1532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8372 pattern childGuard
    simpa only [d1591, d1532, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8374 (pattern : Twelve) (guard : d1867 pattern = 1) : d1184 pattern ≤ (0 : Int) + d1495 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1184, d1495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8291 pattern childGuard
    simpa only [d1184, d1495, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1184, d1495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8320 pattern childGuard
    simpa only [d1184, d1495, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8375 (pattern : Twelve) (guard : d1867 pattern = 1) : d1557 pattern ≤ (0 : Int) + d1496 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1557, d1496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8130 pattern childGuard
    simpa only [d1557, d1496, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1557, d1496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1557, d1496, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8376 (pattern : Twelve) (guard : d1867 pattern = 1) : d1565 pattern ≤ (0 : Int) + d1506 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1565, d1506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8374 pattern childGuard
    simpa only [d1565, d1506, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1565, d1506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8375 pattern childGuard
    simpa only [d1565, d1506, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8377 (pattern : Twelve) (guard : d1867 pattern = 1) : d1578 pattern ≤ (0 : Int) + d1519 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1578, d1519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8186 pattern childGuard
    simpa only [d1578, d1519, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1578, d1519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8376 pattern childGuard
    simpa only [d1578, d1519, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8378 (pattern : Twelve) (guard : d1867 pattern = 1) : d1566 pattern ≤ (0 : Int) + d1507 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1566, d1507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8296 pattern childGuard
    simpa only [d1566, d1507, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1566, d1507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8142 pattern childGuard
    simpa only [d1566, d1507, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8379 (pattern : Twelve) (guard : d1867 pattern = 1) : d1579 pattern ≤ (0 : Int) + d1520 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1579, d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8378 pattern childGuard
    simpa only [d1579, d1520, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1579, d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1579, d1520, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8380 (pattern : Twelve) (guard : d1867 pattern = 1) : d1592 pattern ≤ (0 : Int) + d1533 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1592, d1533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8377 pattern childGuard
    simpa only [d1592, d1533, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1592, d1533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8379 pattern childGuard
    simpa only [d1592, d1533, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8381 (pattern : Twelve) (guard : d1867 pattern = 1) : d1600 pattern ≤ (0 : Int) + d1541 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1600, d1541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8373 pattern childGuard
    simpa only [d1600, d1541, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1600, d1541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8380 pattern childGuard
    simpa only [d1600, d1541, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8382 (pattern : Twelve) (guard : d1867 pattern = 1) : d1580 pattern ≤ (0 : Int) + d1521 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1580, d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8135 pattern childGuard
    simpa only [d1580, d1521, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1580, d1521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8370 pattern childGuard
    simpa only [d1580, d1521, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8383 (pattern : Twelve) (guard : d1867 pattern = 1) : d1593 pattern ≤ (0 : Int) + d1534 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1593, d1534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8382 pattern childGuard
    simpa only [d1593, d1534, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1593, d1534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8372 pattern childGuard
    simpa only [d1593, d1534, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8384 (pattern : Twelve) (guard : d1867 pattern = 1) : d1601 pattern ≤ (0 : Int) + d1542 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1601, d1542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8383 pattern childGuard
    simpa only [d1601, d1542, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1601, d1542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8380 pattern childGuard
    simpa only [d1601, d1542, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8385 (pattern : Twelve) (guard : d1867 pattern = 1) : d1607 pattern ≤ (0 : Int) + d1548 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1607, d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8381 pattern childGuard
    simpa only [d1607, d1548, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1607, d1548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8384 pattern childGuard
    simpa only [d1607, d1548, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8386 (pattern : Twelve) (guard : d1867 pattern = 1) : d1558 pattern ≤ (0 : Int) + d1497 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1558, d1497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8130 pattern childGuard
    simpa only [d1558, d1497, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1558, d1497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8200 pattern childGuard
    simpa only [d1558, d1497, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8387 (pattern : Twelve) (guard : d1867 pattern = 1) : d1567 pattern ≤ (0 : Int) + d1508 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1567, d1508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8374 pattern childGuard
    simpa only [d1567, d1508, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1567, d1508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8386 pattern childGuard
    simpa only [d1567, d1508, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8388 (pattern : Twelve) (guard : d1867 pattern = 1) : d1581 pattern ≤ (0 : Int) + d1522 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1581, d1522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8164 pattern childGuard
    simpa only [d1581, d1522, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1581, d1522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8387 pattern childGuard
    simpa only [d1581, d1522, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8389 (pattern : Twelve) (guard : d1867 pattern = 1) : d1582 pattern ≤ (0 : Int) + d1523 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1582, d1523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8296 pattern childGuard
    simpa only [d1582, d1523, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1582, d1523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1582, d1523, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8390 (pattern : Twelve) (guard : d1867 pattern = 1) : d1594 pattern ≤ (0 : Int) + d1535 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1594, d1535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8388 pattern childGuard
    simpa only [d1594, d1535, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1594, d1535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8389 pattern childGuard
    simpa only [d1594, d1535, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8391 (pattern : Twelve) (guard : d1867 pattern = 1) : d21 pattern ≤ (0 : Int) + d1493 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d21, d1493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7834 pattern childGuard
    simpa only [d1867, d21, d1493, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d21, d1493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2875 pattern childGuard
    simpa only [d1867, d21, d1493, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8392 (pattern : Twelve) (guard : d1867 pattern = 1) : d1186 pattern ≤ (0 : Int) + d1498 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1186, d1498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8320 pattern childGuard
    simpa only [d1186, d1498, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1186, d1498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8391 pattern childGuard
    simpa only [d1186, d1498, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8393 (pattern : Twelve) (guard : d1867 pattern = 1) : d1568 pattern ≤ (0 : Int) + d1509 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1568, d1509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8392 pattern childGuard
    simpa only [d1568, d1509, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1568, d1509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8278 pattern childGuard
    simpa only [d1568, d1509, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8394 (pattern : Twelve) (guard : d1867 pattern = 1) : d1583 pattern ≤ (0 : Int) + d1524 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1583, d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8214 pattern childGuard
    simpa only [d1583, d1524, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1583, d1524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8393 pattern childGuard
    simpa only [d1583, d1524, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8395 (pattern : Twelve) (guard : d1867 pattern = 1) : d1569 pattern ≤ (0 : Int) + d1510 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1569, d1510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8324 pattern childGuard
    simpa only [d1569, d1510, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1569, d1510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8217 pattern childGuard
    simpa only [d1569, d1510, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8396 (pattern : Twelve) (guard : d1867 pattern = 1) : d1584 pattern ≤ (0 : Int) + d1525 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1584, d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8395 pattern childGuard
    simpa only [d1584, d1525, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1584, d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1584, d1525, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8397 (pattern : Twelve) (guard : d1867 pattern = 1) : d1595 pattern ≤ (0 : Int) + d1536 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1595, d1536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8394 pattern childGuard
    simpa only [d1595, d1536, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1595, d1536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8396 pattern childGuard
    simpa only [d1595, d1536, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8398 (pattern : Twelve) (guard : d1867 pattern = 1) : d1602 pattern ≤ (0 : Int) + d1543 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1602, d1543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8390 pattern childGuard
    simpa only [d1602, d1543, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1602, d1543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8397 pattern childGuard
    simpa only [d1602, d1543, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c8399 (pattern : Twelve) (guard : d1867 pattern = 1) : d1603 pattern ≤ (0 : Int) + d1544 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1603, d1544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c8380 pattern childGuard
    simpa only [d1603, d1544, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1867 pattern = 1 := by simpa only [d1603, d1544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3275 pattern childGuard
    simpa only [d1603, d1544, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
