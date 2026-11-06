/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons161
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c22680 (pattern : Twelve) (guard : d1 pattern = 1) : d72 pattern ≤ (5 : Int) + d788 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d72, d788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12972 pattern childGuard
    simpa only [d72, d788, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d72, d788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22679 pattern childGuard
    simpa only [d72, d788, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22681 (pattern : Twelve) (guard : d1 pattern = 1) : d30 pattern ≤ (5 : Int) + d38 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12972 pattern childGuard
    simpa only [d30, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12978 pattern childGuard
    simpa only [d30, d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22682 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (5 : Int) + d15 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12978 pattern childGuard
    simpa only [d9, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12981 pattern childGuard
    simpa only [d9, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22683 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (5 : Int) + d24 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12978 pattern childGuard
    simpa only [d23, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22682 pattern childGuard
    simpa only [d23, d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22684 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (5 : Int) + d41 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22677 pattern childGuard
    simpa only [d34, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22683 pattern childGuard
    simpa only [d34, d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22685 (pattern : Twelve) (guard : d1 pattern = 1) : d55 pattern ≤ (5 : Int) + d61 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d55, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22684 pattern childGuard
    simpa only [d55, d61, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d55, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12989 pattern childGuard
    simpa only [d55, d61, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22686 (pattern : Twelve) (guard : d1 pattern = 1) : d80 pattern ≤ (5 : Int) + d789 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22681 pattern childGuard
    simpa only [d80, d789, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d80, d789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22685 pattern childGuard
    simpa only [d80, d789, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22687 (pattern : Twelve) (guard : d1 pattern = 1) : d97 pattern ≤ (5 : Int) + d794 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d97, d794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22680 pattern childGuard
    simpa only [d97, d794, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d97, d794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22686 pattern childGuard
    simpa only [d97, d794, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22688 (pattern : Twelve) (guard : d1 pattern = 1) : d20 pattern ≤ (5 : Int) + d22 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13057 pattern childGuard
    simpa only [d20, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d20, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12998 pattern childGuard
    simpa only [d20, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22689 (pattern : Twelve) (guard : d1 pattern = 1) : d31 pattern ≤ (5 : Int) + d44 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d31, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12972 pattern childGuard
    simpa only [d31, d44, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d31, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22688 pattern childGuard
    simpa only [d31, d44, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22690 (pattern : Twelve) (guard : d1 pattern = 1) : d52 pattern ≤ (5 : Int) + d783 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d52, d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22681 pattern childGuard
    simpa only [d52, d783, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d52, d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22689 pattern childGuard
    simpa only [d52, d783, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22691 (pattern : Twelve) (guard : d1 pattern = 1) : d43 pattern ≤ (5 : Int) + d47 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d43, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12974 pattern childGuard
    simpa only [d43, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d43, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13007 pattern childGuard
    simpa only [d43, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22692 (pattern : Twelve) (guard : d1 pattern = 1) : d62 pattern ≤ (5 : Int) + d69 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d62, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22681 pattern childGuard
    simpa only [d62, d69, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d62, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22691 pattern childGuard
    simpa only [d62, d69, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22693 (pattern : Twelve) (guard : d1 pattern = 1) : d83 pattern ≤ (5 : Int) + d790 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d83, d790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22690 pattern childGuard
    simpa only [d83, d790, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d83, d790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22692 pattern childGuard
    simpa only [d83, d790, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22694 (pattern : Twelve) (guard : d1 pattern = 1) : d44 pattern ≤ (5 : Int) + d48 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d44, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12978 pattern childGuard
    simpa only [d44, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d44, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13011 pattern childGuard
    simpa only [d44, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22695 (pattern : Twelve) (guard : d1 pattern = 1) : d63 pattern ≤ (5 : Int) + d70 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d63, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22681 pattern childGuard
    simpa only [d63, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d63, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22694 pattern childGuard
    simpa only [d63, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22696 (pattern : Twelve) (guard : d1 pattern = 1) : d40 pattern ≤ (5 : Int) + d49 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22683 pattern childGuard
    simpa only [d40, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d40, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22697 (pattern : Twelve) (guard : d1 pattern = 1) : d64 pattern ≤ (5 : Int) + d71 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d64, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22684 pattern childGuard
    simpa only [d64, d71, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d64, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22696 pattern childGuard
    simpa only [d64, d71, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22698 (pattern : Twelve) (guard : d1 pattern = 1) : d84 pattern ≤ (5 : Int) + d90 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d84, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22695 pattern childGuard
    simpa only [d84, d90, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d84, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22697 pattern childGuard
    simpa only [d84, d90, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22699 (pattern : Twelve) (guard : d1 pattern = 1) : d98 pattern ≤ (5 : Int) + d795 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d98, d795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22693 pattern childGuard
    simpa only [d98, d795, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d98, d795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22698 pattern childGuard
    simpa only [d98, d795, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22700 (pattern : Twelve) (guard : d1 pattern = 1) : d106 pattern ≤ (5 : Int) + d798 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d106, d798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22687 pattern childGuard
    simpa only [d106, d798, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d106, d798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22699 pattern childGuard
    simpa only [d106, d798, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22701 (pattern : Twelve) (guard : d1 pattern = 1) : d35 pattern ≤ (5 : Int) + d39 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d35, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12972 pattern childGuard
    simpa only [d35, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d35, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d35, d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22702 (pattern : Twelve) (guard : d1 pattern = 1) : d56 pattern ≤ (5 : Int) + d59 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d56, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22681 pattern childGuard
    simpa only [d56, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d56, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22701 pattern childGuard
    simpa only [d56, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22703 (pattern : Twelve) (guard : d1 pattern = 1) : d45 pattern ≤ (5 : Int) + d47 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d45, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12974 pattern childGuard
    simpa only [d45, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d45, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d45, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22704 (pattern : Twelve) (guard : d1 pattern = 1) : d65 pattern ≤ (5 : Int) + d69 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d65, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22681 pattern childGuard
    simpa only [d65, d69, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d65, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22703 pattern childGuard
    simpa only [d65, d69, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22705 (pattern : Twelve) (guard : d1 pattern = 1) : d85 pattern ≤ (5 : Int) + d89 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d85, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22702 pattern childGuard
    simpa only [d85, d89, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d85, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22704 pattern childGuard
    simpa only [d85, d89, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22706 (pattern : Twelve) (guard : d1 pattern = 1) : d39 pattern ≤ (5 : Int) + d48 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12978 pattern childGuard
    simpa only [d39, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d39, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22707 (pattern : Twelve) (guard : d1 pattern = 1) : d66 pattern ≤ (5 : Int) + d70 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d66, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22681 pattern childGuard
    simpa only [d66, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d66, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22706 pattern childGuard
    simpa only [d66, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22708 (pattern : Twelve) (guard : d1 pattern = 1) : d86 pattern ≤ (5 : Int) + d90 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d86, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22707 pattern childGuard
    simpa only [d86, d90, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d86, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22697 pattern childGuard
    simpa only [d86, d90, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22709 (pattern : Twelve) (guard : d1 pattern = 1) : d99 pattern ≤ (5 : Int) + d101 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d99, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22705 pattern childGuard
    simpa only [d99, d101, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d99, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22708 pattern childGuard
    simpa only [d99, d101, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22710 (pattern : Twelve) (guard : d1 pattern = 1) : d107 pattern ≤ (5 : Int) + d799 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d107, d799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22687 pattern childGuard
    simpa only [d107, d799, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d107, d799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22709 pattern childGuard
    simpa only [d107, d799, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22711 (pattern : Twelve) (guard : d1 pattern = 1) : d112 pattern ≤ (5 : Int) + d802 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d112, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22700 pattern childGuard
    simpa only [d112, d802, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d112, d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22710 pattern childGuard
    simpa only [d112, d802, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22712 (pattern : Twelve) (guard : d1 pattern = 1) : d46 pattern ≤ (5 : Int) + d780 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d46, d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12974 pattern childGuard
    simpa only [d46, d780, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d46, d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12981 pattern childGuard
    simpa only [d46, d780, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22713 (pattern : Twelve) (guard : d1 pattern = 1) : d67 pattern ≤ (5 : Int) + d784 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d67, d784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22681 pattern childGuard
    simpa only [d67, d784, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d67, d784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22712 pattern childGuard
    simpa only [d67, d784, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22714 (pattern : Twelve) (guard : d1 pattern = 1) : d87 pattern ≤ (5 : Int) + d791 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d87, d791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22681 pattern childGuard
    simpa only [d87, d791, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d87, d791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22713 pattern childGuard
    simpa only [d87, d791, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22715 (pattern : Twelve) (guard : d1 pattern = 1) : d38 pattern ≤ (5 : Int) + d48 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12978 pattern childGuard
    simpa only [d38, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12997 pattern childGuard
    simpa only [d38, d48, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22716 (pattern : Twelve) (guard : d1 pattern = 1) : d68 pattern ≤ (5 : Int) + d70 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d68, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22681 pattern childGuard
    simpa only [d68, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d68, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22715 pattern childGuard
    simpa only [d68, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22717 (pattern : Twelve) (guard : d1 pattern = 1) : d88 pattern ≤ (5 : Int) + d90 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d88, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22716 pattern childGuard
    simpa only [d88, d90, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d88, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22697 pattern childGuard
    simpa only [d88, d90, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22718 (pattern : Twelve) (guard : d1 pattern = 1) : d100 pattern ≤ (5 : Int) + d796 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d100, d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22714 pattern childGuard
    simpa only [d100, d796, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d100, d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22717 pattern childGuard
    simpa only [d100, d796, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22719 (pattern : Twelve) (guard : d1 pattern = 1) : d59 pattern ≤ (5 : Int) + d48 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22715 pattern childGuard
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22706 pattern childGuard
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22720 (pattern : Twelve) (guard : d1 pattern = 1) : d47 pattern ≤ (5 : Int) + d781 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d47, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12981 pattern childGuard
    simpa only [d47, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d47, d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d47, d781, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22721 (pattern : Twelve) (guard : d1 pattern = 1) : d69 pattern ≤ (5 : Int) + d785 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d69, d785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22715 pattern childGuard
    simpa only [d69, d785, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d69, d785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22720 pattern childGuard
    simpa only [d69, d785, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22722 (pattern : Twelve) (guard : d1 pattern = 1) : d89 pattern ≤ (5 : Int) + d792 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d89, d792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22719 pattern childGuard
    simpa only [d89, d792, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d89, d792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22721 pattern childGuard
    simpa only [d89, d792, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22723 (pattern : Twelve) (guard : d1 pattern = 1) : d48 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12997 pattern childGuard
    simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d48, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22724 (pattern : Twelve) (guard : d1 pattern = 1) : d70 pattern ≤ (5 : Int) + d786 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d70, d786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22715 pattern childGuard
    simpa only [d70, d786, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d70, d786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22723 pattern childGuard
    simpa only [d70, d786, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22725 (pattern : Twelve) (guard : d1 pattern = 1) : d24 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12997 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22661 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22726 (pattern : Twelve) (guard : d1 pattern = 1) : d41 pattern ≤ (5 : Int) + d49 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22683 pattern childGuard
    simpa only [d41, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22725 pattern childGuard
    simpa only [d41, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22727 (pattern : Twelve) (guard : d1 pattern = 1) : d49 pattern ≤ (5 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22725 pattern childGuard
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22728 (pattern : Twelve) (guard : d1 pattern = 1) : d71 pattern ≤ (5 : Int) + d787 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d71, d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22726 pattern childGuard
    simpa only [d71, d787, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d71, d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22727 pattern childGuard
    simpa only [d71, d787, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22729 (pattern : Twelve) (guard : d1 pattern = 1) : d90 pattern ≤ (5 : Int) + d793 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d90, d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22724 pattern childGuard
    simpa only [d90, d793, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d90, d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22728 pattern childGuard
    simpa only [d90, d793, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22730 (pattern : Twelve) (guard : d1 pattern = 1) : d101 pattern ≤ (5 : Int) + d797 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d101, d797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22722 pattern childGuard
    simpa only [d101, d797, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d101, d797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22729 pattern childGuard
    simpa only [d101, d797, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22731 (pattern : Twelve) (guard : d1 pattern = 1) : d108 pattern ≤ (5 : Int) + d800 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d108, d800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22718 pattern childGuard
    simpa only [d108, d800, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d108, d800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22730 pattern childGuard
    simpa only [d108, d800, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22732 (pattern : Twelve) (guard : d1 pattern = 1) : d109 pattern ≤ (5 : Int) + d801 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d109, d801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22709 pattern childGuard
    simpa only [d109, d801, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d109, d801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d109, d801, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22733 (pattern : Twelve) (guard : d1 pattern = 1) : d113 pattern ≤ (5 : Int) + d803 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d113, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22731 pattern childGuard
    simpa only [d113, d803, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d113, d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22732 pattern childGuard
    simpa only [d113, d803, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22734 (pattern : Twelve) (guard : d1 pattern = 1) : d115 pattern ≤ (5 : Int) + d804 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d115, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22711 pattern childGuard
    simpa only [d115, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d115, d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22733 pattern childGuard
    simpa only [d115, d804, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22735 (pattern : Twelve) (guard : d1 pattern = 1) : d116 pattern ≤ (5 : Int) + d805 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d116, d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22674 pattern childGuard
    simpa only [d116, d805, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d116, d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22734 pattern childGuard
    simpa only [d116, d805, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22736 (pattern : Twelve) (guard : d0 pattern = 1) : d805 pattern ≤ (5 : Int) + d805 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c22737 (pattern : Twelve) (guard : d1878 pattern = 1) : d806 pattern ≤ (5 : Int) + d805 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1878, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22735 pattern childGuard
    simpa only [d1878, d806, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1878, d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22736 pattern childGuard
    simpa only [d1878, d806, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22738 (pattern : Twelve) (guard : d1 pattern = 1) : d27 pattern ≤ (5 : Int) + d874 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22616 pattern childGuard
    simpa only [d27, d874, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13113 pattern childGuard
    simpa only [d27, d874, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22739 (pattern : Twelve) (guard : d1 pattern = 1) : d814 pattern ≤ (5 : Int) + d814 pattern := by
  omega
theorem c22740 (pattern : Twelve) (guard : d1 pattern = 1) : d816 pattern ≤ (5 : Int) + d875 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d816, d875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22739 pattern childGuard
    simpa only [d816, d875, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d816, d875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13113 pattern childGuard
    simpa only [d816, d875, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22741 (pattern : Twelve) (guard : d1 pattern = 1) : d824 pattern ≤ (5 : Int) + d882 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d824, d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22738 pattern childGuard
    simpa only [d824, d882, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d824, d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22740 pattern childGuard
    simpa only [d824, d882, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22742 (pattern : Twelve) (guard : d1 pattern = 1) : d838 pattern ≤ (5 : Int) + d890 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d838, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12961 pattern childGuard
    simpa only [d838, d890, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d838, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22741 pattern childGuard
    simpa only [d838, d890, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22743 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (5 : Int) + d19 pattern := by
  omega
theorem c22744 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (5 : Int) + d876 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22743 pattern childGuard
    simpa only [d817, d876, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13058 pattern childGuard
    simpa only [d817, d876, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22745 (pattern : Twelve) (guard : d1 pattern = 1) : d42 pattern ≤ (5 : Int) + d42 pattern := by
  omega
theorem c22746 (pattern : Twelve) (guard : d1 pattern = 1) : d825 pattern ≤ (5 : Int) + d883 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d825, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22744 pattern childGuard
    simpa only [d825, d883, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d825, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22745 pattern childGuard
    simpa only [d825, d883, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22747 (pattern : Twelve) (guard : d1 pattern = 1) : d839 pattern ≤ (5 : Int) + d891 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d839, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22616 pattern childGuard
    simpa only [d839, d891, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d839, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22746 pattern childGuard
    simpa only [d839, d891, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22748 (pattern : Twelve) (guard : d1 pattern = 1) : d853 pattern ≤ (5 : Int) + d898 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d853, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22742 pattern childGuard
    simpa only [d853, d898, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d853, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22747 pattern childGuard
    simpa only [d853, d898, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22749 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (5 : Int) + d877 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22616 pattern childGuard
    simpa only [d34, d877, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13046 pattern childGuard
    simpa only [d34, d877, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22750 (pattern : Twelve) (guard : d1 pattern = 1) : d818 pattern ≤ (5 : Int) + d818 pattern := by
  omega
theorem c22751 (pattern : Twelve) (guard : d1 pattern = 1) : d826 pattern ≤ (5 : Int) + d884 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d826, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22749 pattern childGuard
    simpa only [d826, d884, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d826, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22750 pattern childGuard
    simpa only [d826, d884, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22752 (pattern : Twelve) (guard : d1 pattern = 1) : d840 pattern ≤ (5 : Int) + d892 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d840, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13023 pattern childGuard
    simpa only [d840, d892, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d840, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22751 pattern childGuard
    simpa only [d840, d892, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22753 (pattern : Twelve) (guard : d1 pattern = 1) : d827 pattern ≤ (5 : Int) + d827 pattern := by
  omega
theorem c22754 (pattern : Twelve) (guard : d1 pattern = 1) : d841 pattern ≤ (5 : Int) + d893 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d841, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22753 pattern childGuard
    simpa only [d841, d893, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d841, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22746 pattern childGuard
    simpa only [d841, d893, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22755 (pattern : Twelve) (guard : d1 pattern = 1) : d854 pattern ≤ (5 : Int) + d899 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d854, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22752 pattern childGuard
    simpa only [d854, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d854, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22754 pattern childGuard
    simpa only [d854, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22756 (pattern : Twelve) (guard : d1 pattern = 1) : d861 pattern ≤ (5 : Int) + d902 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d861, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22748 pattern childGuard
    simpa only [d861, d902, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d861, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22755 pattern childGuard
    simpa only [d861, d902, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22757 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (5 : Int) + d15 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13132 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12981 pattern childGuard
    simpa only [d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22758 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (5 : Int) + d24 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13132 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22757 pattern childGuard
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22759 (pattern : Twelve) (guard : d1 pattern = 1) : d819 pattern ≤ (5 : Int) + d878 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d819, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22739 pattern childGuard
    simpa only [d819, d878, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d819, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22758 pattern childGuard
    simpa only [d819, d878, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22760 (pattern : Twelve) (guard : d1 pattern = 1) : d828 pattern ≤ (5 : Int) + d885 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d828, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22749 pattern childGuard
    simpa only [d828, d885, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d828, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22759 pattern childGuard
    simpa only [d828, d885, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22761 (pattern : Twelve) (guard : d1 pattern = 1) : d842 pattern ≤ (5 : Int) + d894 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d842, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12993 pattern childGuard
    simpa only [d842, d894, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d842, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22760 pattern childGuard
    simpa only [d842, d894, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22762 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (5 : Int) + d34 pattern := by
  omega
theorem c22763 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (5 : Int) + d879 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22616 pattern childGuard
    simpa only [d34, d879, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22653 pattern childGuard
    simpa only [d34, d879, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22764 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (5 : Int) + d886 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22762 pattern childGuard
    simpa only [d886, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22763 pattern childGuard
    simpa only [d886, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22765 (pattern : Twelve) (guard : d1 pattern = 1) : d843 pattern ≤ (5 : Int) + d895 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d843, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22764 pattern childGuard
    simpa only [d843, d895, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d843, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22746 pattern childGuard
    simpa only [d843, d895, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22766 (pattern : Twelve) (guard : d1 pattern = 1) : d855 pattern ≤ (5 : Int) + d900 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d855, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22761 pattern childGuard
    simpa only [d855, d900, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d855, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22765 pattern childGuard
    simpa only [d855, d900, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22767 (pattern : Twelve) (guard : d1 pattern = 1) : d815 pattern ≤ (5 : Int) + d873 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13133 pattern childGuard
    simpa only [d815, d873, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22757 pattern childGuard
    simpa only [d815, d873, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22768 (pattern : Twelve) (guard : d1 pattern = 1) : d820 pattern ≤ (5 : Int) + d880 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d820, d880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22767 pattern childGuard
    simpa only [d820, d880, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d820, d880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d820, d880, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22769 (pattern : Twelve) (guard : d1 pattern = 1) : d829 pattern ≤ (5 : Int) + d887 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d829, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22663 pattern childGuard
    simpa only [d829, d887, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d829, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22768 pattern childGuard
    simpa only [d829, d887, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22770 (pattern : Twelve) (guard : d1 pattern = 1) : d844 pattern ≤ (5 : Int) + d896 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d844, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13039 pattern childGuard
    simpa only [d844, d896, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d844, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22769 pattern childGuard
    simpa only [d844, d896, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22771 (pattern : Twelve) (guard : d1 pattern = 1) : d24 pattern ≤ (5 : Int) + d118 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13041 pattern childGuard
    simpa only [d24, d118, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13053 pattern childGuard
    simpa only [d24, d118, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22772 (pattern : Twelve) (guard : d1 pattern = 1) : d41 pattern ≤ (5 : Int) + d881 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22660 pattern childGuard
    simpa only [d41, d881, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22771 pattern childGuard
    simpa only [d41, d881, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22773 (pattern : Twelve) (guard : d1 pattern = 1) : d830 pattern ≤ (5 : Int) + d888 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22772 pattern childGuard
    simpa only [d830, d888, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22654 pattern childGuard
    simpa only [d830, d888, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22774 (pattern : Twelve) (guard : d1 pattern = 1) : d25 pattern ≤ (5 : Int) + d25 pattern := by
  omega
theorem c22775 (pattern : Twelve) (guard : d1 pattern = 1) : d821 pattern ≤ (5 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22774 pattern childGuard
    simpa only [d821, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13007 pattern childGuard
    simpa only [d821, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22776 (pattern : Twelve) (guard : d1 pattern = 1) : d831 pattern ≤ (5 : Int) + d889 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d831, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22775 pattern childGuard
    simpa only [d831, d889, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d831, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13159 pattern childGuard
    simpa only [d831, d889, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22777 (pattern : Twelve) (guard : d1 pattern = 1) : d845 pattern ≤ (5 : Int) + d897 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d845, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22773 pattern childGuard
    simpa only [d845, d897, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d845, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22776 pattern childGuard
    simpa only [d845, d897, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22778 (pattern : Twelve) (guard : d1 pattern = 1) : d856 pattern ≤ (5 : Int) + d901 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d856, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22770 pattern childGuard
    simpa only [d856, d901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d856, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22777 pattern childGuard
    simpa only [d856, d901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22779 (pattern : Twelve) (guard : d1 pattern = 1) : d862 pattern ≤ (5 : Int) + d903 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d862, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22766 pattern childGuard
    simpa only [d862, d903, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d862, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22778 pattern childGuard
    simpa only [d862, d903, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22780 (pattern : Twelve) (guard : d1 pattern = 1) : d863 pattern ≤ (5 : Int) + d904 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d863, d904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22755 pattern childGuard
    simpa only [d863, d904, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d863, d904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d863, d904, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22781 (pattern : Twelve) (guard : d1 pattern = 1) : d867 pattern ≤ (5 : Int) + d905 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d867, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22779 pattern childGuard
    simpa only [d867, d905, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d867, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22780 pattern childGuard
    simpa only [d867, d905, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22782 (pattern : Twelve) (guard : d1 pattern = 1) : d869 pattern ≤ (5 : Int) + d906 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d869, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22756 pattern childGuard
    simpa only [d869, d906, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d869, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22781 pattern childGuard
    simpa only [d869, d906, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22783 (pattern : Twelve) (guard : d1 pattern = 1) : d814 pattern ≤ (5 : Int) + d815 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22676 pattern childGuard
    simpa only [d814, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12974 pattern childGuard
    simpa only [d814, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22784 (pattern : Twelve) (guard : d1 pattern = 1) : d816 pattern ≤ (5 : Int) + d1247 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d816, d1247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22783 pattern childGuard
    simpa only [d816, d1247, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d816, d1247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12974 pattern childGuard
    simpa only [d816, d1247, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22785 (pattern : Twelve) (guard : d1 pattern = 1) : d824 pattern ≤ (5 : Int) + d1249 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d824, d1249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22678 pattern childGuard
    simpa only [d824, d1249, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d824, d1249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22784 pattern childGuard
    simpa only [d824, d1249, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22786 (pattern : Twelve) (guard : d1 pattern = 1) : d838 pattern ≤ (5 : Int) + d1253 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d838, d1253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12972 pattern childGuard
    simpa only [d838, d1253, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d838, d1253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22785 pattern childGuard
    simpa only [d838, d1253, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22787 (pattern : Twelve) (guard : d1 pattern = 1) : d823 pattern ≤ (5 : Int) + d1248 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d823, d1248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22677 pattern childGuard
    simpa only [d823, d1248, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d823, d1248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12978 pattern childGuard
    simpa only [d823, d1248, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22788 (pattern : Twelve) (guard : d1 pattern = 1) : d825 pattern ≤ (5 : Int) + d831 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d825, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13209 pattern childGuard
    simpa only [d825, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d825, d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13059 pattern childGuard
    simpa only [d825, d831, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22789 (pattern : Twelve) (guard : d1 pattern = 1) : d846 pattern ≤ (5 : Int) + d1254 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d846, d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22787 pattern childGuard
    simpa only [d846, d1254, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d846, d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22788 pattern childGuard
    simpa only [d846, d1254, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22790 (pattern : Twelve) (guard : d1 pattern = 1) : d857 pattern ≤ (5 : Int) + d1258 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d857, d1258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22786 pattern childGuard
    simpa only [d857, d1258, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d857, d1258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22789 pattern childGuard
    simpa only [d857, d1258, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22791 (pattern : Twelve) (guard : d1 pattern = 1) : d832 pattern ≤ (5 : Int) + d836 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d832, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22684 pattern childGuard
    simpa only [d832, d836, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d832, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22703 pattern childGuard
    simpa only [d832, d836, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22792 (pattern : Twelve) (guard : d1 pattern = 1) : d847 pattern ≤ (5 : Int) + d851 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d847, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22702 pattern childGuard
    simpa only [d847, d851, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d847, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22791 pattern childGuard
    simpa only [d847, d851, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22793 (pattern : Twelve) (guard : d1 pattern = 1) : d833 pattern ≤ (5 : Int) + d837 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d833, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22684 pattern childGuard
    simpa only [d833, d837, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d833, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22706 pattern childGuard
    simpa only [d833, d837, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22794 (pattern : Twelve) (guard : d1 pattern = 1) : d848 pattern ≤ (5 : Int) + d852 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d848, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22793 pattern childGuard
    simpa only [d848, d852, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d848, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22788 pattern childGuard
    simpa only [d848, d852, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22795 (pattern : Twelve) (guard : d1 pattern = 1) : d858 pattern ≤ (5 : Int) + d860 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d858, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22792 pattern childGuard
    simpa only [d858, d860, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d858, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22794 pattern childGuard
    simpa only [d858, d860, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22796 (pattern : Twelve) (guard : d1 pattern = 1) : d864 pattern ≤ (5 : Int) + d1261 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d864, d1261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22790 pattern childGuard
    simpa only [d864, d1261, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d864, d1261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22795 pattern childGuard
    simpa only [d864, d1261, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22797 (pattern : Twelve) (guard : d1 pattern = 1) : d834 pattern ≤ (5 : Int) + d1250 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d834, d1250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22684 pattern childGuard
    simpa only [d834, d1250, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d834, d1250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22712 pattern childGuard
    simpa only [d834, d1250, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22798 (pattern : Twelve) (guard : d1 pattern = 1) : d849 pattern ≤ (5 : Int) + d1255 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d849, d1255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22681 pattern childGuard
    simpa only [d849, d1255, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d849, d1255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22797 pattern childGuard
    simpa only [d849, d1255, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22799 (pattern : Twelve) (guard : d1 pattern = 1) : d835 pattern ≤ (5 : Int) + d837 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d835, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22684 pattern childGuard
    simpa only [d835, d837, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d835, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22715 pattern childGuard
    simpa only [d835, d837, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22800 (pattern : Twelve) (guard : d1 pattern = 1) : d850 pattern ≤ (5 : Int) + d852 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d850, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22799 pattern childGuard
    simpa only [d850, d852, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d850, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22788 pattern childGuard
    simpa only [d850, d852, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22801 (pattern : Twelve) (guard : d1 pattern = 1) : d859 pattern ≤ (5 : Int) + d1259 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d859, d1259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22798 pattern childGuard
    simpa only [d859, d1259, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d859, d1259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22800 pattern childGuard
    simpa only [d859, d1259, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22802 (pattern : Twelve) (guard : d1 pattern = 1) : d836 pattern ≤ (5 : Int) + d1251 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d836, d1251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22726 pattern childGuard
    simpa only [d836, d1251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d836, d1251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22720 pattern childGuard
    simpa only [d836, d1251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22803 (pattern : Twelve) (guard : d1 pattern = 1) : d851 pattern ≤ (5 : Int) + d1256 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d851, d1256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22719 pattern childGuard
    simpa only [d851, d1256, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d851, d1256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22802 pattern childGuard
    simpa only [d851, d1256, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22804 (pattern : Twelve) (guard : d1 pattern = 1) : d837 pattern ≤ (5 : Int) + d787 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d837, d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22726 pattern childGuard
    simpa only [d837, d787, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d837, d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22723 pattern childGuard
    simpa only [d837, d787, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22805 (pattern : Twelve) (guard : d1 pattern = 1) : d831 pattern ≤ (5 : Int) + d1252 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d831, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13226 pattern childGuard
    simpa only [d831, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d831, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13159 pattern childGuard
    simpa only [d831, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22806 (pattern : Twelve) (guard : d1 pattern = 1) : d852 pattern ≤ (5 : Int) + d1257 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d852, d1257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22804 pattern childGuard
    simpa only [d852, d1257, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d852, d1257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22805 pattern childGuard
    simpa only [d852, d1257, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22807 (pattern : Twelve) (guard : d1 pattern = 1) : d860 pattern ≤ (5 : Int) + d1260 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d860, d1260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22803 pattern childGuard
    simpa only [d860, d1260, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d860, d1260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22806 pattern childGuard
    simpa only [d860, d1260, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22808 (pattern : Twelve) (guard : d1 pattern = 1) : d865 pattern ≤ (5 : Int) + d1262 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d865, d1262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22801 pattern childGuard
    simpa only [d865, d1262, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d865, d1262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22807 pattern childGuard
    simpa only [d865, d1262, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22809 (pattern : Twelve) (guard : d1 pattern = 1) : d866 pattern ≤ (5 : Int) + d1263 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d866, d1263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22795 pattern childGuard
    simpa only [d866, d1263, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d866, d1263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12988 pattern childGuard
    simpa only [d866, d1263, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22810 (pattern : Twelve) (guard : d1 pattern = 1) : d868 pattern ≤ (5 : Int) + d1264 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d868, d1264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22808 pattern childGuard
    simpa only [d868, d1264, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d868, d1264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22809 pattern childGuard
    simpa only [d868, d1264, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22811 (pattern : Twelve) (guard : d1 pattern = 1) : d870 pattern ≤ (5 : Int) + d1265 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d870, d1265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22796 pattern childGuard
    simpa only [d870, d1265, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d870, d1265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22810 pattern childGuard
    simpa only [d870, d1265, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22812 (pattern : Twelve) (guard : d1 pattern = 1) : d871 pattern ≤ (5 : Int) + d1266 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d871, d1266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22782 pattern childGuard
    simpa only [d871, d1266, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d871, d1266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22811 pattern childGuard
    simpa only [d871, d1266, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22813 (pattern : Twelve) (guard : d0 pattern = 1) : d1266 pattern ≤ (5 : Int) + d1266 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c22814 (pattern : Twelve) (guard : d1878 pattern = 1) : d1267 pattern ≤ (5 : Int) + d1266 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1878, d1267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22812 pattern childGuard
    simpa only [d1878, d1267, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1878, d1267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22813 pattern childGuard
    simpa only [d1878, d1267, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22815 (pattern : Twelve) (guard : d1 pattern = 1) : d1275 pattern ≤ (5 : Int) + d1275 pattern := by
  omega
theorem c22816 (pattern : Twelve) (guard : d1 pattern = 1) : d1278 pattern ≤ (5 : Int) + d1325 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1278, d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22815 pattern childGuard
    simpa only [d1278, d1325, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1278, d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13197 pattern childGuard
    simpa only [d1278, d1325, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22817 (pattern : Twelve) (guard : d1 pattern = 1) : d872 pattern ≤ (5 : Int) + d872 pattern := by
  omega
theorem c22818 (pattern : Twelve) (guard : d1 pattern = 1) : d872 pattern ≤ (5 : Int) + d1326 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22817 pattern childGuard
    simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13197 pattern childGuard
    simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c22819 (pattern : Twelve) (guard : d1 pattern = 1) : d1284 pattern ≤ (5 : Int) + d1333 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1284, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22816 pattern childGuard
    simpa only [d1284, d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1284, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22818 pattern childGuard
    simpa only [d1284, d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
