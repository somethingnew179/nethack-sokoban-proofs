/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons050
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c7140 (pattern : Twelve) (guard : d1865 pattern = 1) : d581 pattern ≤ (0 : Int) + d136 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d581, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6996 pattern childGuard
    simpa only [d581, d136, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d581, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7139 pattern childGuard
    simpa only [d581, d136, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7141 (pattern : Twelve) (guard : d1865 pattern = 1) : d601 pattern ≤ (0 : Int) + d144 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d601, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7107 pattern childGuard
    simpa only [d601, d144, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d601, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7140 pattern childGuard
    simpa only [d601, d144, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7142 (pattern : Twelve) (guard : d1865 pattern = 1) : d509 pattern ≤ (0 : Int) + d121 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d509, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6996 pattern childGuard
    simpa only [d509, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d509, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7029 pattern childGuard
    simpa only [d509, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7143 (pattern : Twelve) (guard : d1865 pattern = 1) : d544 pattern ≤ (0 : Int) + d130 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d544, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7142 pattern childGuard
    simpa only [d544, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d544, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7053 pattern childGuard
    simpa only [d544, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7144 (pattern : Twelve) (guard : d1865 pattern = 1) : d582 pattern ≤ (0 : Int) + d137 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d582, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7113 pattern childGuard
    simpa only [d582, d137, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d582, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7143 pattern childGuard
    simpa only [d582, d137, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7145 (pattern : Twelve) (guard : d1865 pattern = 1) : d583 pattern ≤ (0 : Int) + d138 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d583, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7056 pattern childGuard
    simpa only [d583, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d583, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7139 pattern childGuard
    simpa only [d583, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7146 (pattern : Twelve) (guard : d1865 pattern = 1) : d602 pattern ≤ (0 : Int) + d145 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d602, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7144 pattern childGuard
    simpa only [d602, d145, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d602, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7145 pattern childGuard
    simpa only [d602, d145, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7147 (pattern : Twelve) (guard : d1865 pattern = 1) : d614 pattern ≤ (0 : Int) + d149 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d614, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7141 pattern childGuard
    simpa only [d614, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d614, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7146 pattern childGuard
    simpa only [d614, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7148 (pattern : Twelve) (guard : d1865 pattern = 1) : d544 pattern ≤ (0 : Int) + d139 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7056 pattern childGuard
    simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7143 pattern childGuard
    simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7149 (pattern : Twelve) (guard : d1865 pattern = 1) : d603 pattern ≤ (0 : Int) + d146 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d603, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7148 pattern childGuard
    simpa only [d603, d146, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d603, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7145 pattern childGuard
    simpa only [d603, d146, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7150 (pattern : Twelve) (guard : d1865 pattern = 1) : d615 pattern ≤ (0 : Int) + d150 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d615, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7141 pattern childGuard
    simpa only [d615, d150, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d615, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7149 pattern childGuard
    simpa only [d615, d150, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7151 (pattern : Twelve) (guard : d1865 pattern = 1) : d622 pattern ≤ (0 : Int) + d153 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d622, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7147 pattern childGuard
    simpa only [d622, d153, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d622, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7150 pattern childGuard
    simpa only [d622, d153, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7152 (pattern : Twelve) (guard : d1865 pattern = 1) : d527 pattern ≤ (0 : Int) + d122 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d527, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7021 pattern childGuard
    simpa only [d527, d122, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d527, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7077 pattern childGuard
    simpa only [d527, d122, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7153 (pattern : Twelve) (guard : d1865 pattern = 1) : d558 pattern ≤ (0 : Int) + d131 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d558, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7142 pattern childGuard
    simpa only [d558, d131, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d558, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7152 pattern childGuard
    simpa only [d558, d131, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7154 (pattern : Twelve) (guard : d1865 pattern = 1) : d584 pattern ≤ (0 : Int) + d140 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d584, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7052 pattern childGuard
    simpa only [d584, d140, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d584, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7153 pattern childGuard
    simpa only [d584, d140, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7155 (pattern : Twelve) (guard : d1865 pattern = 1) : d518 pattern ≤ (0 : Int) + d123 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d518, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6996 pattern childGuard
    simpa only [d518, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d518, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7068 pattern childGuard
    simpa only [d518, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7156 (pattern : Twelve) (guard : d1865 pattern = 1) : d556 pattern ≤ (0 : Int) + d132 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d556, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7052 pattern childGuard
    simpa only [d556, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d556, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7155 pattern childGuard
    simpa only [d556, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7157 (pattern : Twelve) (guard : d1865 pattern = 1) : d585 pattern ≤ (0 : Int) + d141 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d585, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7156 pattern childGuard
    simpa only [d585, d141, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d585, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7139 pattern childGuard
    simpa only [d585, d141, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7158 (pattern : Twelve) (guard : d1865 pattern = 1) : d604 pattern ≤ (0 : Int) + d147 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d604, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7154 pattern childGuard
    simpa only [d604, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d604, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7157 pattern childGuard
    simpa only [d604, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7159 (pattern : Twelve) (guard : d1865 pattern = 1) : d497 pattern ≤ (0 : Int) + d118 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d497, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3017 pattern childGuard
    simpa only [d1865, d497, d118, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d497, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7022 pattern childGuard
    simpa only [d1865, d497, d118, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7160 (pattern : Twelve) (guard : d1865 pattern = 1) : d528 pattern ≤ (0 : Int) + d124 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d528, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7018 pattern childGuard
    simpa only [d528, d124, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d528, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7159 pattern childGuard
    simpa only [d528, d124, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7161 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d117 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c7162 (pattern : Twelve) (guard : d1865 pattern = 1) : d492 pattern ≤ (0 : Int) + d119 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d492, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2922 pattern childGuard
    simpa only [d1865, d492, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d492, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7161 pattern childGuard
    simpa only [d1865, d492, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7163 (pattern : Twelve) (guard : d1865 pattern = 1) : d529 pattern ≤ (0 : Int) + d125 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d529, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7162 pattern childGuard
    simpa only [d529, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d529, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d529, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7164 (pattern : Twelve) (guard : d1865 pattern = 1) : d559 pattern ≤ (0 : Int) + d133 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d559, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7160 pattern childGuard
    simpa only [d559, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d559, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7163 pattern childGuard
    simpa only [d559, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7165 (pattern : Twelve) (guard : d1865 pattern = 1) : d586 pattern ≤ (0 : Int) + d142 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d586, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7085 pattern childGuard
    simpa only [d586, d142, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d586, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7164 pattern childGuard
    simpa only [d586, d142, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7166 (pattern : Twelve) (guard : d1865 pattern = 1) : d497 pattern ≤ (0 : Int) + d5 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3017 pattern childGuard
    simpa only [d1865, d497, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5335 pattern childGuard
    simpa only [d1865, d497, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7167 (pattern : Twelve) (guard : d1865 pattern = 1) : d528 pattern ≤ (0 : Int) + d126 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d528, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7018 pattern childGuard
    simpa only [d528, d126, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d528, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7166 pattern childGuard
    simpa only [d528, d126, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7168 (pattern : Twelve) (guard : d1865 pattern = 1) : d529 pattern ≤ (0 : Int) + d47 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d529, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7068 pattern childGuard
    simpa only [d529, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d529, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d529, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7169 (pattern : Twelve) (guard : d1865 pattern = 1) : d559 pattern ≤ (0 : Int) + d134 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d559, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7167 pattern childGuard
    simpa only [d559, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d559, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7168 pattern childGuard
    simpa only [d559, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7170 (pattern : Twelve) (guard : d1865 pattern = 1) : d530 pattern ≤ (0 : Int) + d127 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d530, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7029 pattern childGuard
    simpa only [d530, d127, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d530, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2880 pattern childGuard
    simpa only [d530, d127, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7171 (pattern : Twelve) (guard : d1865 pattern = 1) : d531 pattern ≤ (0 : Int) + d128 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d531, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7015 pattern childGuard
    simpa only [d531, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d531, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d531, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7172 (pattern : Twelve) (guard : d1865 pattern = 1) : d560 pattern ≤ (0 : Int) + d135 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d560, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7170 pattern childGuard
    simpa only [d560, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d560, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7171 pattern childGuard
    simpa only [d560, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7173 (pattern : Twelve) (guard : d1865 pattern = 1) : d587 pattern ≤ (0 : Int) + d143 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d587, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7169 pattern childGuard
    simpa only [d587, d143, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d587, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7172 pattern childGuard
    simpa only [d587, d143, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7174 (pattern : Twelve) (guard : d1865 pattern = 1) : d605 pattern ≤ (0 : Int) + d148 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d605, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7165 pattern childGuard
    simpa only [d605, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d605, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7173 pattern childGuard
    simpa only [d605, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7175 (pattern : Twelve) (guard : d1865 pattern = 1) : d616 pattern ≤ (0 : Int) + d151 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d616, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7158 pattern childGuard
    simpa only [d616, d151, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d616, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7174 pattern childGuard
    simpa only [d616, d151, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7176 (pattern : Twelve) (guard : d1865 pattern = 1) : d617 pattern ≤ (0 : Int) + d152 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d617, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7149 pattern childGuard
    simpa only [d617, d152, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d617, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d617, d152, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7177 (pattern : Twelve) (guard : d1865 pattern = 1) : d623 pattern ≤ (0 : Int) + d154 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d623, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7175 pattern childGuard
    simpa only [d623, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d623, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7176 pattern childGuard
    simpa only [d623, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7178 (pattern : Twelve) (guard : d1865 pattern = 1) : d626 pattern ≤ (0 : Int) + d155 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d626, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7151 pattern childGuard
    simpa only [d626, d155, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d626, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7177 pattern childGuard
    simpa only [d626, d155, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7179 (pattern : Twelve) (guard : d1865 pattern = 1) : d629 pattern ≤ (0 : Int) + d156 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d629, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7137 pattern childGuard
    simpa only [d629, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d629, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7178 pattern childGuard
    simpa only [d629, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7180 (pattern : Twelve) (guard : d1865 pattern = 1) : d1105 pattern ≤ (0 : Int) + d814 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d1105, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3040 pattern childGuard
    simpa only [d1865, d1105, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d1105, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5047 pattern childGuard
    simpa only [d1865, d1105, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7181 (pattern : Twelve) (guard : d1865 pattern = 1) : d1108 pattern ≤ (0 : Int) + d816 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1108, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7180 pattern childGuard
    simpa only [d1108, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1108, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6990 pattern childGuard
    simpa only [d1108, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7182 (pattern : Twelve) (guard : d1865 pattern = 1) : d1118 pattern ≤ (0 : Int) + d824 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1118, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6991 pattern childGuard
    simpa only [d1118, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1118, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7181 pattern childGuard
    simpa only [d1118, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7183 (pattern : Twelve) (guard : d1865 pattern = 1) : d1132 pattern ≤ (0 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1132, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6998 pattern childGuard
    simpa only [d1132, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1132, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7182 pattern childGuard
    simpa only [d1132, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7184 (pattern : Twelve) (guard : d1865 pattern = 1) : d501 pattern ≤ (0 : Int) + d17 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6989 pattern childGuard
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7021 pattern childGuard
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7185 (pattern : Twelve) (guard : d1865 pattern = 1) : d1119 pattern ≤ (0 : Int) + d17 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7184 pattern childGuard
    simpa only [d1119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7021 pattern childGuard
    simpa only [d1119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7186 (pattern : Twelve) (guard : d1865 pattern = 1) : d1109 pattern ≤ (0 : Int) + d817 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1109, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7003 pattern childGuard
    simpa only [d1109, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1109, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7090 pattern childGuard
    simpa only [d1109, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7187 (pattern : Twelve) (guard : d1865 pattern = 1) : d1120 pattern ≤ (0 : Int) + d825 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1120, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7186 pattern childGuard
    simpa only [d1120, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1120, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7091 pattern childGuard
    simpa only [d1120, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7188 (pattern : Twelve) (guard : d1865 pattern = 1) : d1133 pattern ≤ (0 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1133, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7185 pattern childGuard
    simpa only [d1133, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1133, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7187 pattern childGuard
    simpa only [d1133, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7189 (pattern : Twelve) (guard : d1865 pattern = 1) : d1152 pattern ≤ (0 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1152, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7183 pattern childGuard
    simpa only [d1152, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1152, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7188 pattern childGuard
    simpa only [d1152, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7190 (pattern : Twelve) (guard : d1865 pattern = 1) : d1121 pattern ≤ (0 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1121, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7019 pattern childGuard
    simpa only [d1121, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1121, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7050 pattern childGuard
    simpa only [d1121, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7191 (pattern : Twelve) (guard : d1865 pattern = 1) : d1110 pattern ≤ (0 : Int) + d818 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1110, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7180 pattern childGuard
    simpa only [d1110, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1110, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d1110, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7192 (pattern : Twelve) (guard : d1865 pattern = 1) : d1122 pattern ≤ (0 : Int) + d826 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1122, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7030 pattern childGuard
    simpa only [d1122, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1122, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7191 pattern childGuard
    simpa only [d1122, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7193 (pattern : Twelve) (guard : d1865 pattern = 1) : d1134 pattern ≤ (0 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1134, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7190 pattern childGuard
    simpa only [d1134, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1134, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7192 pattern childGuard
    simpa only [d1134, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7194 (pattern : Twelve) (guard : d1865 pattern = 1) : d544 pattern ≤ (0 : Int) + d827 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d544, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7030 pattern childGuard
    simpa only [d544, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d544, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7053 pattern childGuard
    simpa only [d544, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7195 (pattern : Twelve) (guard : d1865 pattern = 1) : d1135 pattern ≤ (0 : Int) + d841 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1135, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7194 pattern childGuard
    simpa only [d1135, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1135, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7187 pattern childGuard
    simpa only [d1135, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7196 (pattern : Twelve) (guard : d1865 pattern = 1) : d1153 pattern ≤ (0 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1153, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7193 pattern childGuard
    simpa only [d1153, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1153, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7195 pattern childGuard
    simpa only [d1153, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7197 (pattern : Twelve) (guard : d1865 pattern = 1) : d1164 pattern ≤ (0 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1164, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7189 pattern childGuard
    simpa only [d1164, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1164, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7196 pattern childGuard
    simpa only [d1164, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7198 (pattern : Twelve) (guard : d1865 pattern = 1) : d1123 pattern ≤ (0 : Int) + d824 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1123, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7041 pattern childGuard
    simpa only [d1123, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1123, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7181 pattern childGuard
    simpa only [d1123, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7199 (pattern : Twelve) (guard : d1865 pattern = 1) : d1136 pattern ≤ (0 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1136, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7044 pattern childGuard
    simpa only [d1136, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1136, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7198 pattern childGuard
    simpa only [d1136, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7200 (pattern : Twelve) (guard : d1865 pattern = 1) : d1137 pattern ≤ (0 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1137, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7021 pattern childGuard
    simpa only [d1137, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1137, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7187 pattern childGuard
    simpa only [d1137, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7201 (pattern : Twelve) (guard : d1865 pattern = 1) : d1154 pattern ≤ (0 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1154, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7199 pattern childGuard
    simpa only [d1154, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1154, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7200 pattern childGuard
    simpa only [d1154, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7202 (pattern : Twelve) (guard : d1865 pattern = 1) : d1138 pattern ≤ (0 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1138, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7056 pattern childGuard
    simpa only [d1138, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1138, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7192 pattern childGuard
    simpa only [d1138, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7203 (pattern : Twelve) (guard : d1865 pattern = 1) : d1155 pattern ≤ (0 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1155, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7202 pattern childGuard
    simpa only [d1155, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1155, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7195 pattern childGuard
    simpa only [d1155, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7204 (pattern : Twelve) (guard : d1865 pattern = 1) : d1165 pattern ≤ (0 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1165, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7201 pattern childGuard
    simpa only [d1165, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1165, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7203 pattern childGuard
    simpa only [d1165, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7205 (pattern : Twelve) (guard : d1865 pattern = 1) : d1173 pattern ≤ (0 : Int) + d861 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7197 pattern childGuard
    simpa only [d1173, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7204 pattern childGuard
    simpa only [d1173, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7206 (pattern : Twelve) (guard : d1865 pattern = 1) : d1111 pattern ≤ (0 : Int) + d819 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1111, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7180 pattern childGuard
    simpa only [d1111, d819, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1111, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7068 pattern childGuard
    simpa only [d1111, d819, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7207 (pattern : Twelve) (guard : d1865 pattern = 1) : d1124 pattern ≤ (0 : Int) + d828 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1124, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7030 pattern childGuard
    simpa only [d1124, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1124, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7206 pattern childGuard
    simpa only [d1124, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7208 (pattern : Twelve) (guard : d1865 pattern = 1) : d1139 pattern ≤ (0 : Int) + d842 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1139, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7072 pattern childGuard
    simpa only [d1139, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1139, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7207 pattern childGuard
    simpa only [d1139, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7209 (pattern : Twelve) (guard : d1865 pattern = 1) : d1140 pattern ≤ (0 : Int) + d843 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1140, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7030 pattern childGuard
    simpa only [d1140, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1140, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7187 pattern childGuard
    simpa only [d1140, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7210 (pattern : Twelve) (guard : d1865 pattern = 1) : d1156 pattern ≤ (0 : Int) + d855 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1156, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7208 pattern childGuard
    simpa only [d1156, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1156, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7209 pattern childGuard
    simpa only [d1156, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7211 (pattern : Twelve) (guard : d1865 pattern = 1) : d1106 pattern ≤ (0 : Int) + d815 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d1106, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3072 pattern childGuard
    simpa only [d1865, d1106, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d1106, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5328 pattern childGuard
    simpa only [d1865, d1106, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7212 (pattern : Twelve) (guard : d1865 pattern = 1) : d1112 pattern ≤ (0 : Int) + d820 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1112, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7211 pattern childGuard
    simpa only [d1112, d820, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1112, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d1112, d820, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7213 (pattern : Twelve) (guard : d1865 pattern = 1) : d1125 pattern ≤ (0 : Int) + d829 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1125, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7088 pattern childGuard
    simpa only [d1125, d829, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1125, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7212 pattern childGuard
    simpa only [d1125, d829, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7214 (pattern : Twelve) (guard : d1865 pattern = 1) : d1141 pattern ≤ (0 : Int) + d844 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1141, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7085 pattern childGuard
    simpa only [d1141, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1141, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7213 pattern childGuard
    simpa only [d1141, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7215 (pattern : Twelve) (guard : d1865 pattern = 1) : d549 pattern ≤ (0 : Int) + d830 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d549, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7088 pattern childGuard
    simpa only [d549, d830, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d549, d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7082 pattern childGuard
    simpa only [d549, d830, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7216 (pattern : Twelve) (guard : d1865 pattern = 1) : d1113 pattern ≤ (0 : Int) + d821 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1113, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7090 pattern childGuard
    simpa only [d1113, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1113, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7023 pattern childGuard
    simpa only [d1113, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7217 (pattern : Twelve) (guard : d1865 pattern = 1) : d178 pattern ≤ (0 : Int) + d822 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d178, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7023 pattern childGuard
    simpa only [d178, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d178, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d178, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7218 (pattern : Twelve) (guard : d1865 pattern = 1) : d1126 pattern ≤ (0 : Int) + d831 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1126, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7216 pattern childGuard
    simpa only [d1126, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1126, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7217 pattern childGuard
    simpa only [d1126, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7219 (pattern : Twelve) (guard : d1865 pattern = 1) : d1142 pattern ≤ (0 : Int) + d845 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1142, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7215 pattern childGuard
    simpa only [d1142, d845, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1142, d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7218 pattern childGuard
    simpa only [d1142, d845, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7220 (pattern : Twelve) (guard : d1865 pattern = 1) : d1157 pattern ≤ (0 : Int) + d856 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1157, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7214 pattern childGuard
    simpa only [d1157, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1157, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7219 pattern childGuard
    simpa only [d1157, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7221 (pattern : Twelve) (guard : d1865 pattern = 1) : d1166 pattern ≤ (0 : Int) + d862 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1166, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7210 pattern childGuard
    simpa only [d1166, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1166, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7220 pattern childGuard
    simpa only [d1166, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7222 (pattern : Twelve) (guard : d1865 pattern = 1) : d1167 pattern ≤ (0 : Int) + d863 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1167, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7203 pattern childGuard
    simpa only [d1167, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1167, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d1167, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7223 (pattern : Twelve) (guard : d1865 pattern = 1) : d1174 pattern ≤ (0 : Int) + d867 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1174, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7221 pattern childGuard
    simpa only [d1174, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1174, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7222 pattern childGuard
    simpa only [d1174, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7224 (pattern : Twelve) (guard : d1865 pattern = 1) : d1177 pattern ≤ (0 : Int) + d869 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1177, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7205 pattern childGuard
    simpa only [d1177, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1177, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7223 pattern childGuard
    simpa only [d1177, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7225 (pattern : Twelve) (guard : d1865 pattern = 1) : d1143 pattern ≤ (0 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1143, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6996 pattern childGuard
    simpa only [d1143, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1143, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7198 pattern childGuard
    simpa only [d1143, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7226 (pattern : Twelve) (guard : d1865 pattern = 1) : d1158 pattern ≤ (0 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1158, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7225 pattern childGuard
    simpa only [d1158, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1158, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7200 pattern childGuard
    simpa only [d1158, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7227 (pattern : Twelve) (guard : d1865 pattern = 1) : d1168 pattern ≤ (0 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1168, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7226 pattern childGuard
    simpa only [d1168, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1168, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7203 pattern childGuard
    simpa only [d1168, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7228 (pattern : Twelve) (guard : d1865 pattern = 1) : d1144 pattern ≤ (0 : Int) + d842 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1144, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7052 pattern childGuard
    simpa only [d1144, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1144, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7207 pattern childGuard
    simpa only [d1144, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7229 (pattern : Twelve) (guard : d1865 pattern = 1) : d1159 pattern ≤ (0 : Int) + d855 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1159, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7228 pattern childGuard
    simpa only [d1159, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1159, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7209 pattern childGuard
    simpa only [d1159, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7230 (pattern : Twelve) (guard : d1865 pattern = 1) : d1169 pattern ≤ (0 : Int) + d862 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1169, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7229 pattern childGuard
    simpa only [d1169, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1169, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7220 pattern childGuard
    simpa only [d1169, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7231 (pattern : Twelve) (guard : d1865 pattern = 1) : d1175 pattern ≤ (0 : Int) + d867 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1175, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7230 pattern childGuard
    simpa only [d1175, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1175, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7222 pattern childGuard
    simpa only [d1175, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7232 (pattern : Twelve) (guard : d1865 pattern = 1) : d1178 pattern ≤ (0 : Int) + d869 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1178, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7227 pattern childGuard
    simpa only [d1178, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1178, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7231 pattern childGuard
    simpa only [d1178, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7233 (pattern : Twelve) (guard : d1865 pattern = 1) : d1180 pattern ≤ (0 : Int) + d869 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7224 pattern childGuard
    simpa only [d1180, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7232 pattern childGuard
    simpa only [d1180, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7234 (pattern : Twelve) (guard : d1865 pattern = 1) : d1181 pattern ≤ (0 : Int) + d869 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7233 pattern childGuard
    simpa only [d1181, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7232 pattern childGuard
    simpa only [d1181, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7235 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c7236 (pattern : Twelve) (guard : d1865 pattern = 1) : d479 pattern ≤ (0 : Int) + d872 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d479, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2831 pattern childGuard
    simpa only [d1865, d479, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d479, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7235 pattern childGuard
    simpa only [d1865, d479, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7237 (pattern : Twelve) (guard : d1865 pattern = 1) : d513 pattern ≤ (0 : Int) + d874 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d513, d874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7021 pattern childGuard
    simpa only [d513, d874, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d513, d874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7236 pattern childGuard
    simpa only [d513, d874, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7238 (pattern : Twelve) (guard : d1865 pattern = 1) : d1108 pattern ≤ (0 : Int) + d875 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1108, d875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7180 pattern childGuard
    simpa only [d1108, d875, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1108, d875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7236 pattern childGuard
    simpa only [d1108, d875, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7239 (pattern : Twelve) (guard : d1865 pattern = 1) : d1123 pattern ≤ (0 : Int) + d882 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1123, d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7237 pattern childGuard
    simpa only [d1123, d882, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1123, d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7238 pattern childGuard
    simpa only [d1123, d882, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7240 (pattern : Twelve) (guard : d1865 pattern = 1) : d1143 pattern ≤ (0 : Int) + d890 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1143, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6996 pattern childGuard
    simpa only [d1143, d890, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1143, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7239 pattern childGuard
    simpa only [d1143, d890, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7241 (pattern : Twelve) (guard : d1865 pattern = 1) : d1114 pattern ≤ (0 : Int) + d876 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1114, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7003 pattern childGuard
    simpa only [d1114, d876, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1114, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7023 pattern childGuard
    simpa only [d1114, d876, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7242 (pattern : Twelve) (guard : d1865 pattern = 1) : d1127 pattern ≤ (0 : Int) + d883 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1127, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7241 pattern childGuard
    simpa only [d1127, d883, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1127, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7091 pattern childGuard
    simpa only [d1127, d883, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7243 (pattern : Twelve) (guard : d1865 pattern = 1) : d1145 pattern ≤ (0 : Int) + d891 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1145, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7021 pattern childGuard
    simpa only [d1145, d891, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1145, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7242 pattern childGuard
    simpa only [d1145, d891, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7244 (pattern : Twelve) (guard : d1865 pattern = 1) : d1160 pattern ≤ (0 : Int) + d898 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1160, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7240 pattern childGuard
    simpa only [d1160, d898, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1160, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7243 pattern childGuard
    simpa only [d1160, d898, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7245 (pattern : Twelve) (guard : d1865 pattern = 1) : d1115 pattern ≤ (0 : Int) + d877 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1115, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7021 pattern childGuard
    simpa only [d1115, d877, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1115, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7211 pattern childGuard
    simpa only [d1115, d877, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7246 (pattern : Twelve) (guard : d1865 pattern = 1) : d1128 pattern ≤ (0 : Int) + d884 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1128, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7245 pattern childGuard
    simpa only [d1128, d884, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1128, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7191 pattern childGuard
    simpa only [d1128, d884, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7247 (pattern : Twelve) (guard : d1865 pattern = 1) : d1146 pattern ≤ (0 : Int) + d892 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1146, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7056 pattern childGuard
    simpa only [d1146, d892, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1146, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7246 pattern childGuard
    simpa only [d1146, d892, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7248 (pattern : Twelve) (guard : d1865 pattern = 1) : d1147 pattern ≤ (0 : Int) + d893 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1147, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7194 pattern childGuard
    simpa only [d1147, d893, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1147, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7242 pattern childGuard
    simpa only [d1147, d893, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7249 (pattern : Twelve) (guard : d1865 pattern = 1) : d1161 pattern ≤ (0 : Int) + d899 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1161, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7247 pattern childGuard
    simpa only [d1161, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1161, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7248 pattern childGuard
    simpa only [d1161, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7250 (pattern : Twelve) (guard : d1865 pattern = 1) : d1170 pattern ≤ (0 : Int) + d902 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1170, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7244 pattern childGuard
    simpa only [d1170, d902, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1170, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7249 pattern childGuard
    simpa only [d1170, d902, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7251 (pattern : Twelve) (guard : d1865 pattern = 1) : d1116 pattern ≤ (0 : Int) + d878 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1116, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7180 pattern childGuard
    simpa only [d1116, d878, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1116, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7087 pattern childGuard
    simpa only [d1116, d878, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7252 (pattern : Twelve) (guard : d1865 pattern = 1) : d1129 pattern ≤ (0 : Int) + d885 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1129, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7245 pattern childGuard
    simpa only [d1129, d885, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1129, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7251 pattern childGuard
    simpa only [d1129, d885, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7253 (pattern : Twelve) (guard : d1865 pattern = 1) : d1148 pattern ≤ (0 : Int) + d894 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1148, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7052 pattern childGuard
    simpa only [d1148, d894, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1148, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7252 pattern childGuard
    simpa only [d1148, d894, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7254 (pattern : Twelve) (guard : d1865 pattern = 1) : d518 pattern ≤ (0 : Int) + d879 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d518, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7021 pattern childGuard
    simpa only [d518, d879, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d518, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7162 pattern childGuard
    simpa only [d518, d879, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7255 (pattern : Twelve) (guard : d1865 pattern = 1) : d556 pattern ≤ (0 : Int) + d886 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d556, d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7030 pattern childGuard
    simpa only [d556, d886, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d556, d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7254 pattern childGuard
    simpa only [d556, d886, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7256 (pattern : Twelve) (guard : d1865 pattern = 1) : d1149 pattern ≤ (0 : Int) + d895 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1149, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7255 pattern childGuard
    simpa only [d1149, d895, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1149, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7242 pattern childGuard
    simpa only [d1149, d895, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7257 (pattern : Twelve) (guard : d1865 pattern = 1) : d1162 pattern ≤ (0 : Int) + d900 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1162, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7253 pattern childGuard
    simpa only [d1162, d900, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1162, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7256 pattern childGuard
    simpa only [d1162, d900, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7258 (pattern : Twelve) (guard : d1865 pattern = 1) : d1107 pattern ≤ (0 : Int) + d873 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d1107, d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3120 pattern childGuard
    simpa only [d1865, d1107, d873, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d1107, d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7086 pattern childGuard
    simpa only [d1865, d1107, d873, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7259 (pattern : Twelve) (guard : d1865 pattern = 1) : d1117 pattern ≤ (0 : Int) + d880 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1117, d880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7258 pattern childGuard
    simpa only [d1117, d880, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1117, d880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d1117, d880, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7260 (pattern : Twelve) (guard : d1865 pattern = 1) : d1130 pattern ≤ (0 : Int) + d887 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1130, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7170 pattern childGuard
    simpa only [d1130, d887, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1130, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7259 pattern childGuard
    simpa only [d1130, d887, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7261 (pattern : Twelve) (guard : d1865 pattern = 1) : d1150 pattern ≤ (0 : Int) + d896 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1150, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7085 pattern childGuard
    simpa only [d1150, d896, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1150, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7260 pattern childGuard
    simpa only [d1150, d896, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7262 (pattern : Twelve) (guard : d1865 pattern = 1) : d528 pattern ≤ (0 : Int) + d881 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d528, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7029 pattern childGuard
    simpa only [d528, d881, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d528, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7159 pattern childGuard
    simpa only [d528, d881, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7263 (pattern : Twelve) (guard : d1865 pattern = 1) : d559 pattern ≤ (0 : Int) + d888 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d559, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7262 pattern childGuard
    simpa only [d559, d888, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d559, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7163 pattern childGuard
    simpa only [d559, d888, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7264 (pattern : Twelve) (guard : d1865 pattern = 1) : d1131 pattern ≤ (0 : Int) + d889 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1131, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7091 pattern childGuard
    simpa only [d1131, d889, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1131, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d1131, d889, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7265 (pattern : Twelve) (guard : d1865 pattern = 1) : d1151 pattern ≤ (0 : Int) + d897 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1151, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7263 pattern childGuard
    simpa only [d1151, d897, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1151, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7264 pattern childGuard
    simpa only [d1151, d897, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7266 (pattern : Twelve) (guard : d1865 pattern = 1) : d1163 pattern ≤ (0 : Int) + d901 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1163, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7261 pattern childGuard
    simpa only [d1163, d901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1163, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7265 pattern childGuard
    simpa only [d1163, d901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7267 (pattern : Twelve) (guard : d1865 pattern = 1) : d1171 pattern ≤ (0 : Int) + d903 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1171, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7257 pattern childGuard
    simpa only [d1171, d903, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1171, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7266 pattern childGuard
    simpa only [d1171, d903, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7268 (pattern : Twelve) (guard : d1865 pattern = 1) : d1172 pattern ≤ (0 : Int) + d904 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1172, d904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7249 pattern childGuard
    simpa only [d1172, d904, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1172, d904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d1172, d904, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7269 (pattern : Twelve) (guard : d1865 pattern = 1) : d1176 pattern ≤ (0 : Int) + d905 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1176, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7267 pattern childGuard
    simpa only [d1176, d905, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1176, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7268 pattern childGuard
    simpa only [d1176, d905, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7270 (pattern : Twelve) (guard : d1865 pattern = 1) : d1179 pattern ≤ (0 : Int) + d906 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1179, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7250 pattern childGuard
    simpa only [d1179, d906, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1179, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7269 pattern childGuard
    simpa only [d1179, d906, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7271 (pattern : Twelve) (guard : d1865 pattern = 1) : d1182 pattern ≤ (0 : Int) + d907 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1182, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7234 pattern childGuard
    simpa only [d1182, d907, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1182, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7270 pattern childGuard
    simpa only [d1182, d907, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7272 (pattern : Twelve) (guard : d1865 pattern = 1) : d1105 pattern ≤ (0 : Int) + d1275 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d1105, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3040 pattern childGuard
    simpa only [d1865, d1105, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d1105, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7235 pattern childGuard
    simpa only [d1865, d1105, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7273 (pattern : Twelve) (guard : d1865 pattern = 1) : d1108 pattern ≤ (0 : Int) + d1278 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1108, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7272 pattern childGuard
    simpa only [d1108, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1108, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7236 pattern childGuard
    simpa only [d1108, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7274 (pattern : Twelve) (guard : d1865 pattern = 1) : d1505 pattern ≤ (0 : Int) + d1284 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1505, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7273 pattern childGuard
    simpa only [d1505, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1505, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7236 pattern childGuard
    simpa only [d1505, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7275 (pattern : Twelve) (guard : d1865 pattern = 1) : d1517 pattern ≤ (0 : Int) + d1293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1517, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7185 pattern childGuard
    simpa only [d1517, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1517, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7274 pattern childGuard
    simpa only [d1517, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7276 (pattern : Twelve) (guard : d1865 pattern = 1) : d1518 pattern ≤ (0 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1518, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7003 pattern childGuard
    simpa only [d1518, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1518, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2853 pattern childGuard
    simpa only [d1518, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7277 (pattern : Twelve) (guard : d1865 pattern = 1) : d1532 pattern ≤ (0 : Int) + d1305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1532, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7275 pattern childGuard
    simpa only [d1532, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1532, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7276 pattern childGuard
    simpa only [d1532, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7278 (pattern : Twelve) (guard : d1865 pattern = 1) : d1106 pattern ≤ (0 : Int) + d1276 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d1106, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3072 pattern childGuard
    simpa only [d1865, d1106, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d1106, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7161 pattern childGuard
    simpa only [d1865, d1106, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c7279 (pattern : Twelve) (guard : d1865 pattern = 1) : d1495 pattern ≤ (0 : Int) + d1279 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1495, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7272 pattern childGuard
    simpa only [d1495, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1495, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7278 pattern childGuard
    simpa only [d1495, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
