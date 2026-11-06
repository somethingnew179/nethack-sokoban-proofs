/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons104
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c14700 (pattern : Twelve) (guard : d2301 pattern = 1) : d238 pattern ≤ (2 : Int) + d2358 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d238, d2358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14698 pattern childGuard
    simpa only [d2301, d238, d2358, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d238, d2358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14699 pattern childGuard
    simpa only [d2301, d238, d2358, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14701 (pattern : Twelve) (guard : d2301 pattern = 1) : d257 pattern ≤ (2 : Int) + d2417 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d257, d2417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14695 pattern childGuard
    simpa only [d257, d2417, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d257, d2417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14700 pattern childGuard
    simpa only [d257, d2417, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14702 (pattern : Twelve) (guard : d2301 pattern = 1) : d272 pattern ≤ (2 : Int) + d2418 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d272, d2418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14693 pattern childGuard
    simpa only [d272, d2418, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d272, d2418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14701 pattern childGuard
    simpa only [d272, d2418, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14703 (pattern : Twelve) (guard : d0 pattern = 1) : d175 pattern ≤ (2 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14704 (pattern : Twelve) (guard : d2301 pattern = 1) : d239 pattern ≤ (2 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14183 pattern childGuard
    simpa only [d2301, d239, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14703 pattern childGuard
    simpa only [d2301, d239, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14705 (pattern : Twelve) (guard : d0 pattern = 1) : d176 pattern ≤ (2 : Int) + d17 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14706 (pattern : Twelve) (guard : d2301 pattern = 1) : d240 pattern ≤ (2 : Int) + d2357 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d240, d2357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14183 pattern childGuard
    simpa only [d2301, d240, d2357, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d240, d2357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14705 pattern childGuard
    simpa only [d2301, d240, d2357, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14707 (pattern : Twelve) (guard : d2301 pattern = 1) : d258 pattern ≤ (2 : Int) + d2416 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d258, d2416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14704 pattern childGuard
    simpa only [d258, d2416, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d258, d2416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14706 pattern childGuard
    simpa only [d258, d2416, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14708 (pattern : Twelve) (guard : d0 pattern = 1) : d176 pattern ≤ (2 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14709 (pattern : Twelve) (guard : d2301 pattern = 1) : d240 pattern ≤ (2 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14183 pattern childGuard
    simpa only [d2301, d240, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14708 pattern childGuard
    simpa only [d2301, d240, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14710 (pattern : Twelve) (guard : d2301 pattern = 1) : d241 pattern ≤ (2 : Int) + d2358 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d241, d2358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14301 pattern childGuard
    simpa only [d2301, d241, d2358, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d241, d2358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14036 pattern childGuard
    simpa only [d2301, d241, d2358, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14711 (pattern : Twelve) (guard : d2301 pattern = 1) : d259 pattern ≤ (2 : Int) + d2417 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d259, d2417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14709 pattern childGuard
    simpa only [d259, d2417, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d259, d2417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14710 pattern childGuard
    simpa only [d259, d2417, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14712 (pattern : Twelve) (guard : d2301 pattern = 1) : d273 pattern ≤ (2 : Int) + d2418 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d273, d2418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14707 pattern childGuard
    simpa only [d273, d2418, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d273, d2418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14711 pattern childGuard
    simpa only [d273, d2418, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14713 (pattern : Twelve) (guard : d2301 pattern = 1) : d284 pattern ≤ (2 : Int) + d2418 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14702 pattern childGuard
    simpa only [d284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14712 pattern childGuard
    simpa only [d284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14714 (pattern : Twelve) (guard : d2301 pattern = 1) : d242 pattern ≤ (2 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14501 pattern childGuard
    simpa only [d2301, d242, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14703 pattern childGuard
    simpa only [d2301, d242, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14715 (pattern : Twelve) (guard : d2301 pattern = 1) : d243 pattern ≤ (2 : Int) + d2357 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d243, d2357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14690 pattern childGuard
    simpa only [d2301, d243, d2357, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d243, d2357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14705 pattern childGuard
    simpa only [d2301, d243, d2357, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14716 (pattern : Twelve) (guard : d2301 pattern = 1) : d260 pattern ≤ (2 : Int) + d2416 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d260, d2416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14714 pattern childGuard
    simpa only [d260, d2416, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d260, d2416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14715 pattern childGuard
    simpa only [d260, d2416, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14717 (pattern : Twelve) (guard : d2301 pattern = 1) : d244 pattern ≤ (2 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14501 pattern childGuard
    simpa only [d2301, d244, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14708 pattern childGuard
    simpa only [d2301, d244, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14718 (pattern : Twelve) (guard : d2301 pattern = 1) : d261 pattern ≤ (2 : Int) + d2417 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d261, d2417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14717 pattern childGuard
    simpa only [d261, d2417, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d261, d2417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14710 pattern childGuard
    simpa only [d261, d2417, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14719 (pattern : Twelve) (guard : d2301 pattern = 1) : d274 pattern ≤ (2 : Int) + d2418 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d274, d2418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14716 pattern childGuard
    simpa only [d274, d2418, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d274, d2418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14718 pattern childGuard
    simpa only [d274, d2418, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14720 (pattern : Twelve) (guard : d0 pattern = 1) : d178 pattern ≤ (2 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14721 (pattern : Twelve) (guard : d2301 pattern = 1) : d245 pattern ≤ (2 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14183 pattern childGuard
    simpa only [d2301, d245, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14720 pattern childGuard
    simpa only [d2301, d245, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14722 (pattern : Twelve) (guard : d2301 pattern = 1) : d246 pattern ≤ (2 : Int) + d2357 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d246, d2357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14183 pattern childGuard
    simpa only [d2301, d246, d2357, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d246, d2357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13990 pattern childGuard
    simpa only [d2301, d246, d2357, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14723 (pattern : Twelve) (guard : d2301 pattern = 1) : d262 pattern ≤ (2 : Int) + d2416 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d262, d2416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14721 pattern childGuard
    simpa only [d262, d2416, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d262, d2416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14722 pattern childGuard
    simpa only [d262, d2416, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14724 (pattern : Twelve) (guard : d2301 pattern = 1) : d246 pattern ≤ (2 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14183 pattern childGuard
    simpa only [d2301, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13932 pattern childGuard
    simpa only [d2301, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14725 (pattern : Twelve) (guard : d2301 pattern = 1) : d263 pattern ≤ (2 : Int) + d2417 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d263, d2417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14724 pattern childGuard
    simpa only [d263, d2417, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d263, d2417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14710 pattern childGuard
    simpa only [d263, d2417, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14726 (pattern : Twelve) (guard : d2301 pattern = 1) : d275 pattern ≤ (2 : Int) + d2418 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d275, d2418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14723 pattern childGuard
    simpa only [d275, d2418, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d275, d2418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14725 pattern childGuard
    simpa only [d275, d2418, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14727 (pattern : Twelve) (guard : d2301 pattern = 1) : d285 pattern ≤ (2 : Int) + d2418 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14719 pattern childGuard
    simpa only [d285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14726 pattern childGuard
    simpa only [d285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14728 (pattern : Twelve) (guard : d2301 pattern = 1) : d293 pattern ≤ (2 : Int) + d2418 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14713 pattern childGuard
    simpa only [d293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14727 pattern childGuard
    simpa only [d293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14729 (pattern : Twelve) (guard : d0 pattern = 1) : d180 pattern ≤ (2 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14730 (pattern : Twelve) (guard : d2301 pattern = 1) : d247 pattern ≤ (2 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14183 pattern childGuard
    simpa only [d2301, d247, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14729 pattern childGuard
    simpa only [d2301, d247, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14731 (pattern : Twelve) (guard : d0 pattern = 1) : d181 pattern ≤ (2 : Int) + d17 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14732 (pattern : Twelve) (guard : d2301 pattern = 1) : d248 pattern ≤ (2 : Int) + d2357 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d248, d2357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14183 pattern childGuard
    simpa only [d2301, d248, d2357, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d248, d2357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14731 pattern childGuard
    simpa only [d2301, d248, d2357, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14733 (pattern : Twelve) (guard : d2301 pattern = 1) : d264 pattern ≤ (2 : Int) + d2416 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d264, d2416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14730 pattern childGuard
    simpa only [d264, d2416, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d264, d2416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14732 pattern childGuard
    simpa only [d264, d2416, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14734 (pattern : Twelve) (guard : d0 pattern = 1) : d181 pattern ≤ (2 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14735 (pattern : Twelve) (guard : d2301 pattern = 1) : d248 pattern ≤ (2 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14183 pattern childGuard
    simpa only [d2301, d248, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14734 pattern childGuard
    simpa only [d2301, d248, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14736 (pattern : Twelve) (guard : d2301 pattern = 1) : d265 pattern ≤ (2 : Int) + d2417 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d265, d2417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14735 pattern childGuard
    simpa only [d265, d2417, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d265, d2417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14710 pattern childGuard
    simpa only [d265, d2417, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14737 (pattern : Twelve) (guard : d2301 pattern = 1) : d276 pattern ≤ (2 : Int) + d2418 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d276, d2418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14733 pattern childGuard
    simpa only [d276, d2418, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d276, d2418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14736 pattern childGuard
    simpa only [d276, d2418, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14738 (pattern : Twelve) (guard : d0 pattern = 1) : d183 pattern ≤ (2 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14739 (pattern : Twelve) (guard : d2301 pattern = 1) : d249 pattern ≤ (2 : Int) + d2 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14215 pattern childGuard
    simpa only [d2301, d249, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14738 pattern childGuard
    simpa only [d2301, d249, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14740 (pattern : Twelve) (guard : d2301 pattern = 1) : d250 pattern ≤ (2 : Int) + d2360 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d250, d2360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14215 pattern childGuard
    simpa only [d2301, d250, d2360, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d250, d2360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14051 pattern childGuard
    simpa only [d2301, d250, d2360, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14741 (pattern : Twelve) (guard : d2301 pattern = 1) : d266 pattern ≤ (2 : Int) + d2419 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d266, d2419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14739 pattern childGuard
    simpa only [d266, d2419, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d266, d2419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14740 pattern childGuard
    simpa only [d266, d2419, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14742 (pattern : Twelve) (guard : d2301 pattern = 1) : d250 pattern ≤ (2 : Int) + d2 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14215 pattern childGuard
    simpa only [d2301, d250, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13966 pattern childGuard
    simpa only [d2301, d250, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14743 (pattern : Twelve) (guard : d2301 pattern = 1) : d251 pattern ≤ (2 : Int) + d2361 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d251, d2361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14320 pattern childGuard
    simpa only [d2301, d251, d2361, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d251, d2361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14074 pattern childGuard
    simpa only [d2301, d251, d2361, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14744 (pattern : Twelve) (guard : d2301 pattern = 1) : d267 pattern ≤ (2 : Int) + d2420 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d267, d2420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14742 pattern childGuard
    simpa only [d267, d2420, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d267, d2420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14743 pattern childGuard
    simpa only [d267, d2420, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14745 (pattern : Twelve) (guard : d2301 pattern = 1) : d277 pattern ≤ (2 : Int) + d2421 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d277, d2421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14741 pattern childGuard
    simpa only [d277, d2421, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d277, d2421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14744 pattern childGuard
    simpa only [d277, d2421, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14746 (pattern : Twelve) (guard : d2301 pattern = 1) : d286 pattern ≤ (2 : Int) + d2422 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d286, d2422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14737 pattern childGuard
    simpa only [d286, d2422, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d286, d2422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14745 pattern childGuard
    simpa only [d286, d2422, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14747 (pattern : Twelve) (guard : d0 pattern = 1) : d183 pattern ≤ (2 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14748 (pattern : Twelve) (guard : d2301 pattern = 1) : d252 pattern ≤ (2 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14183 pattern childGuard
    simpa only [d2301, d252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14747 pattern childGuard
    simpa only [d2301, d252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14749 (pattern : Twelve) (guard : d2301 pattern = 1) : d268 pattern ≤ (2 : Int) + d2416 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d268, d2416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14748 pattern childGuard
    simpa only [d268, d2416, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d268, d2416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14722 pattern childGuard
    simpa only [d268, d2416, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14750 (pattern : Twelve) (guard : d2301 pattern = 1) : d278 pattern ≤ (2 : Int) + d2418 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d278, d2418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14749 pattern childGuard
    simpa only [d278, d2418, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d278, d2418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14725 pattern childGuard
    simpa only [d278, d2418, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14751 (pattern : Twelve) (guard : d2301 pattern = 1) : d287 pattern ≤ (2 : Int) + d2423 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d287, d2423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14750 pattern childGuard
    simpa only [d287, d2423, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d287, d2423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14238 pattern childGuard
    simpa only [d287, d2423, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14752 (pattern : Twelve) (guard : d2301 pattern = 1) : d294 pattern ≤ (2 : Int) + d2424 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d294, d2424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14746 pattern childGuard
    simpa only [d294, d2424, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d294, d2424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14751 pattern childGuard
    simpa only [d294, d2424, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14753 (pattern : Twelve) (guard : d2301 pattern = 1) : d297 pattern ≤ (2 : Int) + d2425 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d297, d2425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14728 pattern childGuard
    simpa only [d297, d2425, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d297, d2425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14752 pattern childGuard
    simpa only [d297, d2425, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14754 (pattern : Twelve) (guard : d2301 pattern = 1) : d253 pattern ≤ (2 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14501 pattern childGuard
    simpa only [d2301, d253, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13932 pattern childGuard
    simpa only [d2301, d253, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14755 (pattern : Twelve) (guard : d2301 pattern = 1) : d254 pattern ≤ (2 : Int) + d2357 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d254, d2357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14690 pattern childGuard
    simpa only [d2301, d254, d2357, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d254, d2357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13990 pattern childGuard
    simpa only [d2301, d254, d2357, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14756 (pattern : Twelve) (guard : d2301 pattern = 1) : d269 pattern ≤ (2 : Int) + d2416 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d269, d2416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14754 pattern childGuard
    simpa only [d269, d2416, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d269, d2416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14755 pattern childGuard
    simpa only [d269, d2416, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14757 (pattern : Twelve) (guard : d2301 pattern = 1) : d279 pattern ≤ (2 : Int) + d2418 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d279, d2418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14756 pattern childGuard
    simpa only [d279, d2418, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d279, d2418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14725 pattern childGuard
    simpa only [d279, d2418, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14758 (pattern : Twelve) (guard : d2301 pattern = 1) : d246 pattern ≤ (2 : Int) + d2416 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d2416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14724 pattern childGuard
    simpa only [d2416, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d2416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14722 pattern childGuard
    simpa only [d2416, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14759 (pattern : Twelve) (guard : d2301 pattern = 1) : d280 pattern ≤ (2 : Int) + d2418 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d280, d2418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14758 pattern childGuard
    simpa only [d280, d2418, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d280, d2418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14725 pattern childGuard
    simpa only [d280, d2418, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14760 (pattern : Twelve) (guard : d2301 pattern = 1) : d288 pattern ≤ (2 : Int) + d2418 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14757 pattern childGuard
    simpa only [d288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14759 pattern childGuard
    simpa only [d288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14761 (pattern : Twelve) (guard : d2301 pattern = 1) : d250 pattern ≤ (2 : Int) + d2419 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d2419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14742 pattern childGuard
    simpa only [d2419, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d2419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14740 pattern childGuard
    simpa only [d2419, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14762 (pattern : Twelve) (guard : d2301 pattern = 1) : d281 pattern ≤ (2 : Int) + d2421 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d281, d2421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14761 pattern childGuard
    simpa only [d281, d2421, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d281, d2421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14744 pattern childGuard
    simpa only [d281, d2421, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14763 (pattern : Twelve) (guard : d2301 pattern = 1) : d289 pattern ≤ (2 : Int) + d2422 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d289, d2422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14759 pattern childGuard
    simpa only [d289, d2422, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d289, d2422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14762 pattern childGuard
    simpa only [d289, d2422, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14764 (pattern : Twelve) (guard : d2301 pattern = 1) : d290 pattern ≤ (2 : Int) + d2423 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d290, d2423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14759 pattern childGuard
    simpa only [d290, d2423, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d290, d2423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14238 pattern childGuard
    simpa only [d290, d2423, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14765 (pattern : Twelve) (guard : d2301 pattern = 1) : d295 pattern ≤ (2 : Int) + d2424 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d295, d2424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14763 pattern childGuard
    simpa only [d295, d2424, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d295, d2424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14764 pattern childGuard
    simpa only [d295, d2424, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14766 (pattern : Twelve) (guard : d2301 pattern = 1) : d298 pattern ≤ (2 : Int) + d2425 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d298, d2425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14760 pattern childGuard
    simpa only [d298, d2425, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d298, d2425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14765 pattern childGuard
    simpa only [d298, d2425, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14767 (pattern : Twelve) (guard : d2301 pattern = 1) : d300 pattern ≤ (2 : Int) + d2425 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14753 pattern childGuard
    simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14766 pattern childGuard
    simpa only [d300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14768 (pattern : Twelve) (guard : d2301 pattern = 1) : d255 pattern ≤ (2 : Int) + d2358 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d255, d2358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14698 pattern childGuard
    simpa only [d2301, d255, d2358, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d255, d2358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14036 pattern childGuard
    simpa only [d2301, d255, d2358, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14769 (pattern : Twelve) (guard : d2301 pattern = 1) : d270 pattern ≤ (2 : Int) + d2417 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d270, d2417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14754 pattern childGuard
    simpa only [d270, d2417, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d270, d2417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14768 pattern childGuard
    simpa only [d270, d2417, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14770 (pattern : Twelve) (guard : d2301 pattern = 1) : d282 pattern ≤ (2 : Int) + d2418 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d282, d2418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14756 pattern childGuard
    simpa only [d282, d2418, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d282, d2418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14769 pattern childGuard
    simpa only [d282, d2418, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14771 (pattern : Twelve) (guard : d2301 pattern = 1) : d291 pattern ≤ (2 : Int) + d2418 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14770 pattern childGuard
    simpa only [d291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14759 pattern childGuard
    simpa only [d291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14772 (pattern : Twelve) (guard : d2301 pattern = 1) : d271 pattern ≤ (2 : Int) + d2417 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d271, d2417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14754 pattern childGuard
    simpa only [d271, d2417, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d271, d2417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14710 pattern childGuard
    simpa only [d271, d2417, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14773 (pattern : Twelve) (guard : d2301 pattern = 1) : d283 pattern ≤ (2 : Int) + d2418 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d283, d2418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14756 pattern childGuard
    simpa only [d283, d2418, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d283, d2418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14772 pattern childGuard
    simpa only [d283, d2418, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14774 (pattern : Twelve) (guard : d2301 pattern = 1) : d292 pattern ≤ (2 : Int) + d2418 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14773 pattern childGuard
    simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14759 pattern childGuard
    simpa only [d292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14775 (pattern : Twelve) (guard : d2301 pattern = 1) : d296 pattern ≤ (2 : Int) + d2418 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14771 pattern childGuard
    simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14774 pattern childGuard
    simpa only [d296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14776 (pattern : Twelve) (guard : d2301 pattern = 1) : d299 pattern ≤ (2 : Int) + d2425 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d299, d2425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14775 pattern childGuard
    simpa only [d299, d2425, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d299, d2425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14765 pattern childGuard
    simpa only [d299, d2425, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14777 (pattern : Twelve) (guard : d2301 pattern = 1) : d301 pattern ≤ (2 : Int) + d2425 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14776 pattern childGuard
    simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14766 pattern childGuard
    simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14778 (pattern : Twelve) (guard : d2301 pattern = 1) : d302 pattern ≤ (2 : Int) + d2425 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14767 pattern childGuard
    simpa only [d302, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14777 pattern childGuard
    simpa only [d302, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14779 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d119 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14780 (pattern : Twelve) (guard : d2301 pattern = 1) : d250 pattern ≤ (2 : Int) + d2367 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d250, d2367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14215 pattern childGuard
    simpa only [d2301, d250, d2367, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d250, d2367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14779 pattern childGuard
    simpa only [d2301, d250, d2367, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14781 (pattern : Twelve) (guard : d2301 pattern = 1) : d250 pattern ≤ (2 : Int) + d2426 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d2426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14742 pattern childGuard
    simpa only [d2426, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d2426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14780 pattern childGuard
    simpa only [d2426, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14782 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d3 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14783 (pattern : Twelve) (guard : d2301 pattern = 1) : d250 pattern ≤ (2 : Int) + d2427 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d250, d2427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14215 pattern childGuard
    simpa only [d2301, d250, d2427, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d250, d2427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14782 pattern childGuard
    simpa only [d2301, d250, d2427, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14784 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d20 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14785 (pattern : Twelve) (guard : d2301 pattern = 1) : d251 pattern ≤ (2 : Int) + d2368 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d251, d2368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14320 pattern childGuard
    simpa only [d2301, d251, d2368, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d251, d2368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14784 pattern childGuard
    simpa only [d2301, d251, d2368, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14786 (pattern : Twelve) (guard : d2301 pattern = 1) : d267 pattern ≤ (2 : Int) + d2428 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d267, d2428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14783 pattern childGuard
    simpa only [d267, d2428, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d267, d2428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14785 pattern childGuard
    simpa only [d267, d2428, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14787 (pattern : Twelve) (guard : d2301 pattern = 1) : d281 pattern ≤ (2 : Int) + d2429 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d281, d2429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14781 pattern childGuard
    simpa only [d281, d2429, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d281, d2429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14786 pattern childGuard
    simpa only [d281, d2429, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14788 (pattern : Twelve) (guard : d2301 pattern = 1) : d289 pattern ≤ (2 : Int) + d2430 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d289, d2430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14759 pattern childGuard
    simpa only [d289, d2430, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d289, d2430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14787 pattern childGuard
    simpa only [d289, d2430, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14789 (pattern : Twelve) (guard : d2301 pattern = 1) : d295 pattern ≤ (2 : Int) + d2431 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d295, d2431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14788 pattern childGuard
    simpa only [d295, d2431, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d295, d2431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14764 pattern childGuard
    simpa only [d295, d2431, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14790 (pattern : Twelve) (guard : d2301 pattern = 1) : d299 pattern ≤ (2 : Int) + d2432 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d299, d2432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14775 pattern childGuard
    simpa only [d299, d2432, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d299, d2432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14789 pattern childGuard
    simpa only [d299, d2432, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14791 (pattern : Twelve) (guard : d2301 pattern = 1) : d298 pattern ≤ (2 : Int) + d2432 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d298, d2432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14760 pattern childGuard
    simpa only [d298, d2432, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d298, d2432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14789 pattern childGuard
    simpa only [d298, d2432, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14792 (pattern : Twelve) (guard : d2301 pattern = 1) : d301 pattern ≤ (2 : Int) + d2432 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14790 pattern childGuard
    simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14791 pattern childGuard
    simpa only [d301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14793 (pattern : Twelve) (guard : d2301 pattern = 1) : d303 pattern ≤ (2 : Int) + d2433 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d303, d2433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14778 pattern childGuard
    simpa only [d303, d2433, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d303, d2433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14792 pattern childGuard
    simpa only [d303, d2433, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14794 (pattern : Twelve) (guard : d26 pattern = 1) : d27 pattern ≤ (2 : Int) + d17 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14300 pattern childGuard
    simpa only [d26, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13322 pattern childGuard
    simpa only [d26, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14795 (pattern : Twelve) (guard : d0 pattern = 1) : d173 pattern ≤ (2 : Int) + d814 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14796 (pattern : Twelve) (guard : d2301 pattern = 1) : d940 pattern ≤ (2 : Int) + d2374 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d940, d2374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14794 pattern childGuard
    simpa only [d2301, d940, d2374, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d940, d2374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14795 pattern childGuard
    simpa only [d2301, d940, d2374, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14797 (pattern : Twelve) (guard : d2301 pattern = 1) : d947 pattern ≤ (2 : Int) + d2434 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d947, d2434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14695 pattern childGuard
    simpa only [d947, d2434, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d947, d2434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14796 pattern childGuard
    simpa only [d947, d2434, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14798 (pattern : Twelve) (guard : d26 pattern = 1) : d17 pattern ≤ (2 : Int) + d17 pattern := by
  omega
theorem c14799 (pattern : Twelve) (guard : d0 pattern = 1) : d173 pattern ≤ (2 : Int) + d17 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14800 (pattern : Twelve) (guard : d2301 pattern = 1) : d941 pattern ≤ (2 : Int) + d17 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14798 pattern childGuard
    simpa only [d2301, d941, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14799 pattern childGuard
    simpa only [d2301, d941, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14801 (pattern : Twelve) (guard : d2301 pattern = 1) : d942 pattern ≤ (2 : Int) + d2375 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d942, d2375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14388 pattern childGuard
    simpa only [d2301, d942, d2375, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d942, d2375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14074 pattern childGuard
    simpa only [d2301, d942, d2375, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14802 (pattern : Twelve) (guard : d2301 pattern = 1) : d948 pattern ≤ (2 : Int) + d2435 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d948, d2435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14800 pattern childGuard
    simpa only [d948, d2435, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d948, d2435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14801 pattern childGuard
    simpa only [d948, d2435, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14803 (pattern : Twelve) (guard : d2301 pattern = 1) : d955 pattern ≤ (2 : Int) + d2436 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d955, d2436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14797 pattern childGuard
    simpa only [d955, d2436, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d955, d2436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14802 pattern childGuard
    simpa only [d955, d2436, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14804 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d814 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14805 (pattern : Twelve) (guard : d2301 pattern = 1) : d241 pattern ≤ (2 : Int) + d2374 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d241, d2374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14301 pattern childGuard
    simpa only [d2301, d241, d2374, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d241, d2374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14804 pattern childGuard
    simpa only [d2301, d241, d2374, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14806 (pattern : Twelve) (guard : d2301 pattern = 1) : d259 pattern ≤ (2 : Int) + d2434 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d259, d2434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14709 pattern childGuard
    simpa only [d259, d2434, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d259, d2434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14805 pattern childGuard
    simpa only [d259, d2434, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14807 (pattern : Twelve) (guard : d2301 pattern = 1) : d241 pattern ≤ (2 : Int) + d17 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14301 pattern childGuard
    simpa only [d2301, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13990 pattern childGuard
    simpa only [d2301, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14808 (pattern : Twelve) (guard : d2301 pattern = 1) : d949 pattern ≤ (2 : Int) + d2435 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d949, d2435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14807 pattern childGuard
    simpa only [d949, d2435, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d949, d2435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14801 pattern childGuard
    simpa only [d949, d2435, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14809 (pattern : Twelve) (guard : d2301 pattern = 1) : d956 pattern ≤ (2 : Int) + d2436 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d956, d2436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14806 pattern childGuard
    simpa only [d956, d2436, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d956, d2436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14808 pattern childGuard
    simpa only [d956, d2436, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14810 (pattern : Twelve) (guard : d2301 pattern = 1) : d963 pattern ≤ (2 : Int) + d2436 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14803 pattern childGuard
    simpa only [d963, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14809 pattern childGuard
    simpa only [d963, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14811 (pattern : Twelve) (guard : d2301 pattern = 1) : d943 pattern ≤ (2 : Int) + d2374 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d943, d2374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14794 pattern childGuard
    simpa only [d2301, d943, d2374, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d943, d2374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14804 pattern childGuard
    simpa only [d2301, d943, d2374, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14812 (pattern : Twelve) (guard : d2301 pattern = 1) : d950 pattern ≤ (2 : Int) + d2434 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d950, d2434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14717 pattern childGuard
    simpa only [d950, d2434, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d950, d2434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14811 pattern childGuard
    simpa only [d950, d2434, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14813 (pattern : Twelve) (guard : d2301 pattern = 1) : d944 pattern ≤ (2 : Int) + d17 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14798 pattern childGuard
    simpa only [d2301, d944, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13990 pattern childGuard
    simpa only [d2301, d944, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14814 (pattern : Twelve) (guard : d2301 pattern = 1) : d951 pattern ≤ (2 : Int) + d2435 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d951, d2435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14813 pattern childGuard
    simpa only [d951, d2435, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d951, d2435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14801 pattern childGuard
    simpa only [d951, d2435, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14815 (pattern : Twelve) (guard : d2301 pattern = 1) : d957 pattern ≤ (2 : Int) + d2436 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d957, d2436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14812 pattern childGuard
    simpa only [d957, d2436, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d957, d2436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14814 pattern childGuard
    simpa only [d957, d2436, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14816 (pattern : Twelve) (guard : d2301 pattern = 1) : d263 pattern ≤ (2 : Int) + d2434 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d263, d2434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14724 pattern childGuard
    simpa only [d263, d2434, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d263, d2434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14805 pattern childGuard
    simpa only [d263, d2434, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14817 (pattern : Twelve) (guard : d2301 pattern = 1) : d958 pattern ≤ (2 : Int) + d2436 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d958, d2436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14816 pattern childGuard
    simpa only [d958, d2436, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d958, d2436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14808 pattern childGuard
    simpa only [d958, d2436, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14818 (pattern : Twelve) (guard : d2301 pattern = 1) : d964 pattern ≤ (2 : Int) + d2436 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14815 pattern childGuard
    simpa only [d964, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14817 pattern childGuard
    simpa only [d964, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14819 (pattern : Twelve) (guard : d2301 pattern = 1) : d970 pattern ≤ (2 : Int) + d2436 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14810 pattern childGuard
    simpa only [d970, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14818 pattern childGuard
    simpa only [d970, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14820 (pattern : Twelve) (guard : d2301 pattern = 1) : d265 pattern ≤ (2 : Int) + d2434 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d265, d2434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14735 pattern childGuard
    simpa only [d265, d2434, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d265, d2434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14805 pattern childGuard
    simpa only [d265, d2434, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14821 (pattern : Twelve) (guard : d2301 pattern = 1) : d959 pattern ≤ (2 : Int) + d2436 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d959, d2436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14820 pattern childGuard
    simpa only [d959, d2436, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d959, d2436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14808 pattern childGuard
    simpa only [d959, d2436, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14822 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d815 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14823 (pattern : Twelve) (guard : d2301 pattern = 1) : d251 pattern ≤ (2 : Int) + d2377 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d251, d2377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14320 pattern childGuard
    simpa only [d2301, d251, d2377, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d251, d2377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14822 pattern childGuard
    simpa only [d2301, d251, d2377, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14824 (pattern : Twelve) (guard : d2301 pattern = 1) : d267 pattern ≤ (2 : Int) + d2437 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d267, d2437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14742 pattern childGuard
    simpa only [d267, d2437, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d267, d2437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14823 pattern childGuard
    simpa only [d267, d2437, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14825 (pattern : Twelve) (guard : d2301 pattern = 1) : d251 pattern ≤ (2 : Int) + d23 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14320 pattern childGuard
    simpa only [d2301, d251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14051 pattern childGuard
    simpa only [d2301, d251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14826 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (2 : Int) + d21 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c14827 (pattern : Twelve) (guard : d2301 pattern = 1) : d945 pattern ≤ (2 : Int) + d2378 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d945, d2378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14405 pattern childGuard
    simpa only [d2301, d945, d2378, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d945, d2378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14826 pattern childGuard
    simpa only [d2301, d945, d2378, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14828 (pattern : Twelve) (guard : d2301 pattern = 1) : d952 pattern ≤ (2 : Int) + d2438 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d952, d2438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14825 pattern childGuard
    simpa only [d952, d2438, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d952, d2438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14827 pattern childGuard
    simpa only [d952, d2438, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14829 (pattern : Twelve) (guard : d2301 pattern = 1) : d960 pattern ≤ (2 : Int) + d2439 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d960, d2439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14824 pattern childGuard
    simpa only [d960, d2439, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d960, d2439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14828 pattern childGuard
    simpa only [d960, d2439, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14830 (pattern : Twelve) (guard : d2301 pattern = 1) : d965 pattern ≤ (2 : Int) + d2440 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d965, d2440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14821 pattern childGuard
    simpa only [d965, d2440, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d965, d2440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14829 pattern childGuard
    simpa only [d965, d2440, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14831 (pattern : Twelve) (guard : d2301 pattern = 1) : d966 pattern ≤ (2 : Int) + d2441 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d966, d2441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14817 pattern childGuard
    simpa only [d966, d2441, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d966, d2441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14238 pattern childGuard
    simpa only [d966, d2441, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14832 (pattern : Twelve) (guard : d2301 pattern = 1) : d971 pattern ≤ (2 : Int) + d2442 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d971, d2442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14830 pattern childGuard
    simpa only [d971, d2442, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d971, d2442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14831 pattern childGuard
    simpa only [d971, d2442, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14833 (pattern : Twelve) (guard : d2301 pattern = 1) : d973 pattern ≤ (2 : Int) + d2443 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d973, d2443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14819 pattern childGuard
    simpa only [d973, d2443, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d973, d2443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14832 pattern childGuard
    simpa only [d973, d2443, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14834 (pattern : Twelve) (guard : d2301 pattern = 1) : d953 pattern ≤ (2 : Int) + d2434 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d953, d2434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14754 pattern childGuard
    simpa only [d953, d2434, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d953, d2434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14811 pattern childGuard
    simpa only [d953, d2434, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14835 (pattern : Twelve) (guard : d26 pattern = 1) : d823 pattern ≤ (2 : Int) + d17 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d26, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14300 pattern childGuard
    simpa only [d26, d823, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13393 pattern childGuard
    simpa only [d26, d823, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14836 (pattern : Twelve) (guard : d2301 pattern = 1) : d946 pattern ≤ (2 : Int) + d17 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d26 pattern = 1 := by simpa only [d2301, d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14835 pattern childGuard
    simpa only [d2301, d946, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d2301, d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13990 pattern childGuard
    simpa only [d2301, d946, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14837 (pattern : Twelve) (guard : d2301 pattern = 1) : d954 pattern ≤ (2 : Int) + d2435 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d954, d2435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14836 pattern childGuard
    simpa only [d954, d2435, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d954, d2435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14801 pattern childGuard
    simpa only [d954, d2435, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14838 (pattern : Twelve) (guard : d2301 pattern = 1) : d961 pattern ≤ (2 : Int) + d2436 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d961, d2436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14834 pattern childGuard
    simpa only [d961, d2436, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d961, d2436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14837 pattern childGuard
    simpa only [d961, d2436, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c14839 (pattern : Twelve) (guard : d2301 pattern = 1) : d967 pattern ≤ (2 : Int) + d2436 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d2301 pattern = 1 := by simpa only [d967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14838 pattern childGuard
    simpa only [d967, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d2301 pattern = 1 := by simpa only [d967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14817 pattern childGuard
    simpa only [d967, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
