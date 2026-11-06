/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons005
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c840 (pattern : Twelve) (guard : d1837 pattern = 1) : d261 pattern ≤ (0 : Int) + d76 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d261, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c839 pattern childGuard
    simpa only [d261, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d261, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c829 pattern childGuard
    simpa only [d261, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c841 (pattern : Twelve) (guard : d1837 pattern = 1) : d274 pattern ≤ (0 : Int) + d93 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d274, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c837 pattern childGuard
    simpa only [d274, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d274, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c840 pattern childGuard
    simpa only [d274, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c842 (pattern : Twelve) (guard : d0 pattern = 1) : d178 pattern ≤ (0 : Int) + d35 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c843 (pattern : Twelve) (guard : d1837 pattern = 1) : d245 pattern ≤ (0 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d245, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1837, d245, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d245, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c842 pattern childGuard
    simpa only [d1837, d245, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c844 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d36 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c845 (pattern : Twelve) (guard : d1837 pattern = 1) : d246 pattern ≤ (0 : Int) + d57 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d246, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1837, d246, d57, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d246, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c844 pattern childGuard
    simpa only [d1837, d246, d57, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c846 (pattern : Twelve) (guard : d1837 pattern = 1) : d262 pattern ≤ (0 : Int) + d77 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d262, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c843 pattern childGuard
    simpa only [d262, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d262, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c845 pattern childGuard
    simpa only [d262, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c847 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d35 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c848 (pattern : Twelve) (guard : d1837 pattern = 1) : d246 pattern ≤ (0 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d246, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1837, d246, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d246, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c847 pattern childGuard
    simpa only [d1837, d246, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c849 (pattern : Twelve) (guard : d1837 pattern = 1) : d263 pattern ≤ (0 : Int) + d78 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d263, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c848 pattern childGuard
    simpa only [d263, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d263, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c829 pattern childGuard
    simpa only [d263, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c850 (pattern : Twelve) (guard : d1837 pattern = 1) : d275 pattern ≤ (0 : Int) + d94 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d275, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c846 pattern childGuard
    simpa only [d275, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d275, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c849 pattern childGuard
    simpa only [d275, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c851 (pattern : Twelve) (guard : d1837 pattern = 1) : d285 pattern ≤ (0 : Int) + d103 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d285, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c841 pattern childGuard
    simpa only [d285, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d285, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c850 pattern childGuard
    simpa only [d285, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c852 (pattern : Twelve) (guard : d1837 pattern = 1) : d293 pattern ≤ (0 : Int) + d110 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d293, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c832 pattern childGuard
    simpa only [d293, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d293, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c851 pattern childGuard
    simpa only [d293, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c853 (pattern : Twelve) (guard : d0 pattern = 1) : d180 pattern ≤ (0 : Int) + d30 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c854 (pattern : Twelve) (guard : d1837 pattern = 1) : d247 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1837, d247, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c853 pattern childGuard
    simpa only [d1837, d247, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c855 (pattern : Twelve) (guard : d0 pattern = 1) : d181 pattern ≤ (0 : Int) + d37 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c856 (pattern : Twelve) (guard : d1837 pattern = 1) : d248 pattern ≤ (0 : Int) + d58 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d248, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1837, d248, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d248, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c855 pattern childGuard
    simpa only [d1837, d248, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c857 (pattern : Twelve) (guard : d1837 pattern = 1) : d264 pattern ≤ (0 : Int) + d79 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d264, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c854 pattern childGuard
    simpa only [d264, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d264, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c856 pattern childGuard
    simpa only [d264, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c858 (pattern : Twelve) (guard : d0 pattern = 1) : d181 pattern ≤ (0 : Int) + d30 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c859 (pattern : Twelve) (guard : d1837 pattern = 1) : d248 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1837, d248, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c858 pattern childGuard
    simpa only [d1837, d248, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c860 (pattern : Twelve) (guard : d1837 pattern = 1) : d265 pattern ≤ (0 : Int) + d80 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d265, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c859 pattern childGuard
    simpa only [d265, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d265, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c829 pattern childGuard
    simpa only [d265, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c861 (pattern : Twelve) (guard : d1837 pattern = 1) : d276 pattern ≤ (0 : Int) + d95 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d276, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c857 pattern childGuard
    simpa only [d276, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d276, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c860 pattern childGuard
    simpa only [d276, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c862 (pattern : Twelve) (guard : d0 pattern = 1) : d183 pattern ≤ (0 : Int) + d39 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c863 (pattern : Twelve) (guard : d1837 pattern = 1) : d249 pattern ≤ (0 : Int) + d59 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d249, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c135 pattern childGuard
    simpa only [d1837, d249, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d249, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c862 pattern childGuard
    simpa only [d1837, d249, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c864 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d40 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c865 (pattern : Twelve) (guard : d1837 pattern = 1) : d250 pattern ≤ (0 : Int) + d60 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d250, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c135 pattern childGuard
    simpa only [d1837, d250, d60, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d250, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c864 pattern childGuard
    simpa only [d1837, d250, d60, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c866 (pattern : Twelve) (guard : d1837 pattern = 1) : d266 pattern ≤ (0 : Int) + d81 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d266, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c863 pattern childGuard
    simpa only [d266, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d266, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c865 pattern childGuard
    simpa only [d266, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c867 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d39 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c868 (pattern : Twelve) (guard : d1837 pattern = 1) : d250 pattern ≤ (0 : Int) + d59 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d250, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c135 pattern childGuard
    simpa only [d1837, d250, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d250, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c867 pattern childGuard
    simpa only [d1837, d250, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c869 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d42 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c870 (pattern : Twelve) (guard : d1837 pattern = 1) : d251 pattern ≤ (0 : Int) + d61 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d251, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c143 pattern childGuard
    simpa only [d1837, d251, d61, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d251, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c869 pattern childGuard
    simpa only [d1837, d251, d61, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c871 (pattern : Twelve) (guard : d1837 pattern = 1) : d267 pattern ≤ (0 : Int) + d82 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d267, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c868 pattern childGuard
    simpa only [d267, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d267, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c870 pattern childGuard
    simpa only [d267, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c872 (pattern : Twelve) (guard : d1837 pattern = 1) : d277 pattern ≤ (0 : Int) + d96 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d277, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c866 pattern childGuard
    simpa only [d277, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d277, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c871 pattern childGuard
    simpa only [d277, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c873 (pattern : Twelve) (guard : d1837 pattern = 1) : d286 pattern ≤ (0 : Int) + d104 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d286, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c861 pattern childGuard
    simpa only [d286, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d286, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c872 pattern childGuard
    simpa only [d286, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c874 (pattern : Twelve) (guard : d0 pattern = 1) : d183 pattern ≤ (0 : Int) + d35 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c875 (pattern : Twelve) (guard : d1837 pattern = 1) : d252 pattern ≤ (0 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d252, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1837, d252, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d252, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c874 pattern childGuard
    simpa only [d1837, d252, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c876 (pattern : Twelve) (guard : d1837 pattern = 1) : d268 pattern ≤ (0 : Int) + d77 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d268, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c875 pattern childGuard
    simpa only [d268, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d268, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c845 pattern childGuard
    simpa only [d268, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c877 (pattern : Twelve) (guard : d1837 pattern = 1) : d278 pattern ≤ (0 : Int) + d94 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d278, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c876 pattern childGuard
    simpa only [d278, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d278, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c849 pattern childGuard
    simpa only [d278, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c878 (pattern : Twelve) (guard : d1837 pattern = 1) : d287 pattern ≤ (0 : Int) + d105 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d287, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c877 pattern childGuard
    simpa only [d287, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d287, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c153 pattern childGuard
    simpa only [d287, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c879 (pattern : Twelve) (guard : d1837 pattern = 1) : d294 pattern ≤ (0 : Int) + d111 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d294, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c873 pattern childGuard
    simpa only [d294, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d294, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c878 pattern childGuard
    simpa only [d294, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c880 (pattern : Twelve) (guard : d1837 pattern = 1) : d297 pattern ≤ (0 : Int) + d114 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d297, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c852 pattern childGuard
    simpa only [d297, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d297, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c879 pattern childGuard
    simpa only [d297, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c881 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d0 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c882 (pattern : Twelve) (guard : d1837 pattern = 1) : d253 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1837, d253, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c881 pattern childGuard
    simpa only [d1837, d253, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c883 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d27 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c884 (pattern : Twelve) (guard : d1837 pattern = 1) : d254 pattern ≤ (0 : Int) + d50 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d254, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c81 pattern childGuard
    simpa only [d1837, d254, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d254, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c883 pattern childGuard
    simpa only [d1837, d254, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c885 (pattern : Twelve) (guard : d1837 pattern = 1) : d269 pattern ≤ (0 : Int) + d72 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d269, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c882 pattern childGuard
    simpa only [d269, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d269, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c884 pattern childGuard
    simpa only [d269, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c886 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d30 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c887 (pattern : Twelve) (guard : d1837 pattern = 1) : d246 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1837, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c886 pattern childGuard
    simpa only [d1837, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c888 (pattern : Twelve) (guard : d1837 pattern = 1) : d263 pattern ≤ (0 : Int) + d80 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d263, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c887 pattern childGuard
    simpa only [d263, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d263, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c829 pattern childGuard
    simpa only [d263, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c889 (pattern : Twelve) (guard : d1837 pattern = 1) : d279 pattern ≤ (0 : Int) + d97 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d279, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c885 pattern childGuard
    simpa only [d279, d97, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d279, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c888 pattern childGuard
    simpa only [d279, d97, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c890 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d31 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c891 (pattern : Twelve) (guard : d1837 pattern = 1) : d246 pattern ≤ (0 : Int) + d52 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d246, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1837, d246, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d246, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c890 pattern childGuard
    simpa only [d1837, d246, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c892 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d43 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c893 (pattern : Twelve) (guard : d1837 pattern = 1) : d246 pattern ≤ (0 : Int) + d62 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d246, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1837, d246, d62, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d246, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c892 pattern childGuard
    simpa only [d1837, d246, d62, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c894 (pattern : Twelve) (guard : d1837 pattern = 1) : d246 pattern ≤ (0 : Int) + d83 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c891 pattern childGuard
    simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c893 pattern childGuard
    simpa only [d83, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c895 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d44 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c896 (pattern : Twelve) (guard : d1837 pattern = 1) : d246 pattern ≤ (0 : Int) + d63 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d246, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1837, d246, d63, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d246, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c895 pattern childGuard
    simpa only [d1837, d246, d63, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c897 (pattern : Twelve) (guard : d1837 pattern = 1) : d241 pattern ≤ (0 : Int) + d64 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d241, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c100 pattern childGuard
    simpa only [d1837, d241, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d241, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c864 pattern childGuard
    simpa only [d1837, d241, d64, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c898 (pattern : Twelve) (guard : d1837 pattern = 1) : d263 pattern ≤ (0 : Int) + d84 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d263, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c896 pattern childGuard
    simpa only [d263, d84, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d263, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c897 pattern childGuard
    simpa only [d263, d84, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c899 (pattern : Twelve) (guard : d1837 pattern = 1) : d280 pattern ≤ (0 : Int) + d98 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d280, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c894 pattern childGuard
    simpa only [d280, d98, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d280, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c898 pattern childGuard
    simpa only [d280, d98, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c900 (pattern : Twelve) (guard : d1837 pattern = 1) : d288 pattern ≤ (0 : Int) + d106 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d288, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c889 pattern childGuard
    simpa only [d288, d106, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d288, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c899 pattern childGuard
    simpa only [d288, d106, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c901 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d45 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c902 (pattern : Twelve) (guard : d1837 pattern = 1) : d246 pattern ≤ (0 : Int) + d65 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d246, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1837, d246, d65, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d246, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c901 pattern childGuard
    simpa only [d1837, d246, d65, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c903 (pattern : Twelve) (guard : d1837 pattern = 1) : d246 pattern ≤ (0 : Int) + d85 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c848 pattern childGuard
    simpa only [d85, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c902 pattern childGuard
    simpa only [d85, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c904 (pattern : Twelve) (guard : d1837 pattern = 1) : d246 pattern ≤ (0 : Int) + d66 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d246, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1837, d246, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d246, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c867 pattern childGuard
    simpa only [d1837, d246, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c905 (pattern : Twelve) (guard : d1837 pattern = 1) : d263 pattern ≤ (0 : Int) + d86 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d263, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c904 pattern childGuard
    simpa only [d263, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d263, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c897 pattern childGuard
    simpa only [d263, d86, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c906 (pattern : Twelve) (guard : d1837 pattern = 1) : d280 pattern ≤ (0 : Int) + d99 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d280, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c903 pattern childGuard
    simpa only [d280, d99, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d280, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c905 pattern childGuard
    simpa only [d280, d99, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c907 (pattern : Twelve) (guard : d1837 pattern = 1) : d288 pattern ≤ (0 : Int) + d107 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d288, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c889 pattern childGuard
    simpa only [d288, d107, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d288, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c906 pattern childGuard
    simpa only [d288, d107, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c908 (pattern : Twelve) (guard : d1837 pattern = 1) : d288 pattern ≤ (0 : Int) + d112 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c900 pattern childGuard
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c907 pattern childGuard
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c909 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d46 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c910 (pattern : Twelve) (guard : d1837 pattern = 1) : d246 pattern ≤ (0 : Int) + d67 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d246, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1837, d246, d67, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d246, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c909 pattern childGuard
    simpa only [d1837, d246, d67, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c911 (pattern : Twelve) (guard : d1837 pattern = 1) : d246 pattern ≤ (0 : Int) + d87 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c887 pattern childGuard
    simpa only [d87, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c910 pattern childGuard
    simpa only [d87, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c912 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d38 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c913 (pattern : Twelve) (guard : d1837 pattern = 1) : d246 pattern ≤ (0 : Int) + d68 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d246, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1837, d246, d68, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d246, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c912 pattern childGuard
    simpa only [d1837, d246, d68, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c914 (pattern : Twelve) (guard : d1837 pattern = 1) : d263 pattern ≤ (0 : Int) + d88 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d263, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c913 pattern childGuard
    simpa only [d263, d88, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d263, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c897 pattern childGuard
    simpa only [d263, d88, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c915 (pattern : Twelve) (guard : d1837 pattern = 1) : d280 pattern ≤ (0 : Int) + d100 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d280, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c911 pattern childGuard
    simpa only [d280, d100, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d280, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c914 pattern childGuard
    simpa only [d280, d100, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c916 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d47 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c917 (pattern : Twelve) (guard : d1837 pattern = 1) : d250 pattern ≤ (0 : Int) + d69 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d250, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c135 pattern childGuard
    simpa only [d1837, d250, d69, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d250, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c916 pattern childGuard
    simpa only [d1837, d250, d69, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c918 (pattern : Twelve) (guard : d1837 pattern = 1) : d250 pattern ≤ (0 : Int) + d89 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c868 pattern childGuard
    simpa only [d89, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c917 pattern childGuard
    simpa only [d89, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c919 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d48 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c920 (pattern : Twelve) (guard : d1837 pattern = 1) : d250 pattern ≤ (0 : Int) + d70 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d250, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c135 pattern childGuard
    simpa only [d1837, d250, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d250, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c919 pattern childGuard
    simpa only [d1837, d250, d70, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c921 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d49 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c922 (pattern : Twelve) (guard : d1837 pattern = 1) : d251 pattern ≤ (0 : Int) + d71 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d251, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c143 pattern childGuard
    simpa only [d1837, d251, d71, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d251, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c921 pattern childGuard
    simpa only [d1837, d251, d71, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c923 (pattern : Twelve) (guard : d1837 pattern = 1) : d267 pattern ≤ (0 : Int) + d90 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d267, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c920 pattern childGuard
    simpa only [d267, d90, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d267, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c922 pattern childGuard
    simpa only [d267, d90, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c924 (pattern : Twelve) (guard : d1837 pattern = 1) : d281 pattern ≤ (0 : Int) + d101 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d281, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c918 pattern childGuard
    simpa only [d281, d101, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d281, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c923 pattern childGuard
    simpa only [d281, d101, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c925 (pattern : Twelve) (guard : d1837 pattern = 1) : d289 pattern ≤ (0 : Int) + d108 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d289, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c915 pattern childGuard
    simpa only [d289, d108, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d289, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c924 pattern childGuard
    simpa only [d289, d108, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c926 (pattern : Twelve) (guard : d1837 pattern = 1) : d290 pattern ≤ (0 : Int) + d109 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d290, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c906 pattern childGuard
    simpa only [d290, d109, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d290, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c153 pattern childGuard
    simpa only [d290, d109, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c927 (pattern : Twelve) (guard : d1837 pattern = 1) : d295 pattern ≤ (0 : Int) + d113 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d295, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c925 pattern childGuard
    simpa only [d295, d113, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d295, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c926 pattern childGuard
    simpa only [d295, d113, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c928 (pattern : Twelve) (guard : d1837 pattern = 1) : d298 pattern ≤ (0 : Int) + d115 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d298, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c908 pattern childGuard
    simpa only [d298, d115, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d298, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c927 pattern childGuard
    simpa only [d298, d115, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c929 (pattern : Twelve) (guard : d1837 pattern = 1) : d300 pattern ≤ (0 : Int) + d116 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d300, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c880 pattern childGuard
    simpa only [d300, d116, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d300, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c928 pattern childGuard
    simpa only [d300, d116, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c930 (pattern : Twelve) (guard : d1837 pattern = 1) : d255 pattern ≤ (0 : Int) + d51 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d255, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c87 pattern childGuard
    simpa only [d1837, d255, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d255, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c828 pattern childGuard
    simpa only [d1837, d255, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c931 (pattern : Twelve) (guard : d1837 pattern = 1) : d270 pattern ≤ (0 : Int) + d73 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d270, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c882 pattern childGuard
    simpa only [d270, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d270, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c930 pattern childGuard
    simpa only [d270, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c932 (pattern : Twelve) (guard : d1837 pattern = 1) : d282 pattern ≤ (0 : Int) + d91 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d282, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c885 pattern childGuard
    simpa only [d282, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d282, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c931 pattern childGuard
    simpa only [d282, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c933 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d32 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c934 (pattern : Twelve) (guard : d1837 pattern = 1) : d246 pattern ≤ (0 : Int) + d53 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d246, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1837, d246, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d246, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c933 pattern childGuard
    simpa only [d1837, d246, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c935 (pattern : Twelve) (guard : d1837 pattern = 1) : d246 pattern ≤ (0 : Int) + d74 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c891 pattern childGuard
    simpa only [d74, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c934 pattern childGuard
    simpa only [d74, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c936 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d33 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c937 (pattern : Twelve) (guard : d1837 pattern = 1) : d246 pattern ≤ (0 : Int) + d54 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d246, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1837, d246, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d246, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c936 pattern childGuard
    simpa only [d1837, d246, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c938 (pattern : Twelve) (guard : d1837 pattern = 1) : d263 pattern ≤ (0 : Int) + d75 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d263, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c937 pattern childGuard
    simpa only [d263, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d263, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c829 pattern childGuard
    simpa only [d263, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c939 (pattern : Twelve) (guard : d1837 pattern = 1) : d280 pattern ≤ (0 : Int) + d92 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d280, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c935 pattern childGuard
    simpa only [d280, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d280, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c938 pattern childGuard
    simpa only [d280, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c940 (pattern : Twelve) (guard : d1837 pattern = 1) : d291 pattern ≤ (0 : Int) + d102 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d291, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c932 pattern childGuard
    simpa only [d291, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d291, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c939 pattern childGuard
    simpa only [d291, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c941 (pattern : Twelve) (guard : d1837 pattern = 1) : d271 pattern ≤ (0 : Int) + d76 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d271, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c882 pattern childGuard
    simpa only [d271, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d271, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c829 pattern childGuard
    simpa only [d271, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c942 (pattern : Twelve) (guard : d1837 pattern = 1) : d283 pattern ≤ (0 : Int) + d93 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d283, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c885 pattern childGuard
    simpa only [d283, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d283, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c941 pattern childGuard
    simpa only [d283, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c943 (pattern : Twelve) (guard : d1837 pattern = 1) : d246 pattern ≤ (0 : Int) + d77 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c848 pattern childGuard
    simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c845 pattern childGuard
    simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c944 (pattern : Twelve) (guard : d1837 pattern = 1) : d280 pattern ≤ (0 : Int) + d94 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d280, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c943 pattern childGuard
    simpa only [d280, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d280, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c849 pattern childGuard
    simpa only [d280, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c945 (pattern : Twelve) (guard : d1837 pattern = 1) : d292 pattern ≤ (0 : Int) + d103 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d292, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c942 pattern childGuard
    simpa only [d292, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d292, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c944 pattern childGuard
    simpa only [d292, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c946 (pattern : Twelve) (guard : d1837 pattern = 1) : d296 pattern ≤ (0 : Int) + d110 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d296, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c940 pattern childGuard
    simpa only [d296, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d296, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c945 pattern childGuard
    simpa only [d296, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c947 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d37 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c948 (pattern : Twelve) (guard : d1837 pattern = 1) : d246 pattern ≤ (0 : Int) + d58 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d246, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1837, d246, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d246, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c947 pattern childGuard
    simpa only [d1837, d246, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c949 (pattern : Twelve) (guard : d1837 pattern = 1) : d246 pattern ≤ (0 : Int) + d79 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c887 pattern childGuard
    simpa only [d79, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c948 pattern childGuard
    simpa only [d79, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c950 (pattern : Twelve) (guard : d1837 pattern = 1) : d280 pattern ≤ (0 : Int) + d95 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d280, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c949 pattern childGuard
    simpa only [d280, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d280, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c888 pattern childGuard
    simpa only [d280, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c951 (pattern : Twelve) (guard : d1837 pattern = 1) : d250 pattern ≤ (0 : Int) + d81 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c868 pattern childGuard
    simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c865 pattern childGuard
    simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c952 (pattern : Twelve) (guard : d1837 pattern = 1) : d281 pattern ≤ (0 : Int) + d96 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d281, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c951 pattern childGuard
    simpa only [d281, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d281, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c871 pattern childGuard
    simpa only [d281, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c953 (pattern : Twelve) (guard : d1837 pattern = 1) : d289 pattern ≤ (0 : Int) + d104 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d289, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c950 pattern childGuard
    simpa only [d289, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d289, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c952 pattern childGuard
    simpa only [d289, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c954 (pattern : Twelve) (guard : d1837 pattern = 1) : d290 pattern ≤ (0 : Int) + d105 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d290, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c944 pattern childGuard
    simpa only [d290, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d290, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c153 pattern childGuard
    simpa only [d290, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c955 (pattern : Twelve) (guard : d1837 pattern = 1) : d295 pattern ≤ (0 : Int) + d111 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d295, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c953 pattern childGuard
    simpa only [d295, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d295, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c954 pattern childGuard
    simpa only [d295, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c956 (pattern : Twelve) (guard : d1837 pattern = 1) : d299 pattern ≤ (0 : Int) + d114 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d299, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c946 pattern childGuard
    simpa only [d299, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d299, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c955 pattern childGuard
    simpa only [d299, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c957 (pattern : Twelve) (guard : d1837 pattern = 1) : d301 pattern ≤ (0 : Int) + d116 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d301, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c956 pattern childGuard
    simpa only [d301, d116, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d301, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c928 pattern childGuard
    simpa only [d301, d116, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c958 (pattern : Twelve) (guard : d1837 pattern = 1) : d302 pattern ≤ (0 : Int) + d116 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c929 pattern childGuard
    simpa only [d302, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c957 pattern childGuard
    simpa only [d302, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c959 (pattern : Twelve) (guard : d1837 pattern = 1) : d303 pattern ≤ (0 : Int) + d116 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c958 pattern childGuard
    simpa only [d303, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c957 pattern childGuard
    simpa only [d303, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c960 (pattern : Twelve) (guard : d0 pattern = 1) : d173 pattern ≤ (0 : Int) + d816 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c961 (pattern : Twelve) (guard : d1837 pattern = 1) : d940 pattern ≤ (0 : Int) + d824 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d940, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c236 pattern childGuard
    simpa only [d1837, d940, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d940, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c960 pattern childGuard
    simpa only [d1837, d940, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c962 (pattern : Twelve) (guard : d1837 pattern = 1) : d947 pattern ≤ (0 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d947, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c816 pattern childGuard
    simpa only [d947, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d947, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c961 pattern childGuard
    simpa only [d947, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c963 (pattern : Twelve) (guard : d0 pattern = 1) : d173 pattern ≤ (0 : Int) + d17 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c964 (pattern : Twelve) (guard : d1837 pattern = 1) : d941 pattern ≤ (0 : Int) + d17 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1837, d941, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c963 pattern childGuard
    simpa only [d1837, d941, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c965 (pattern : Twelve) (guard : d1837 pattern = 1) : d942 pattern ≤ (0 : Int) + d825 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d942, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c243 pattern childGuard
    simpa only [d1837, d942, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d942, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c869 pattern childGuard
    simpa only [d1837, d942, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c966 (pattern : Twelve) (guard : d1837 pattern = 1) : d948 pattern ≤ (0 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d948, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c964 pattern childGuard
    simpa only [d948, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d948, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c965 pattern childGuard
    simpa only [d948, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c967 (pattern : Twelve) (guard : d1837 pattern = 1) : d955 pattern ≤ (0 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d955, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c962 pattern childGuard
    simpa only [d955, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d955, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c966 pattern childGuard
    simpa only [d955, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c968 (pattern : Twelve) (guard : d0 pattern = 1) : d176 pattern ≤ (0 : Int) + d35 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c969 (pattern : Twelve) (guard : d1837 pattern = 1) : d240 pattern ≤ (0 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d240, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1837, d240, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d240, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c968 pattern childGuard
    simpa only [d1837, d240, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c970 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d818 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c971 (pattern : Twelve) (guard : d1837 pattern = 1) : d241 pattern ≤ (0 : Int) + d826 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d241, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c100 pattern childGuard
    simpa only [d1837, d241, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d241, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c970 pattern childGuard
    simpa only [d1837, d241, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c972 (pattern : Twelve) (guard : d1837 pattern = 1) : d259 pattern ≤ (0 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d259, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c969 pattern childGuard
    simpa only [d259, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d259, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c971 pattern childGuard
    simpa only [d259, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c973 (pattern : Twelve) (guard : d1837 pattern = 1) : d241 pattern ≤ (0 : Int) + d827 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d241, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c100 pattern childGuard
    simpa only [d1837, d241, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d241, d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c844 pattern childGuard
    simpa only [d1837, d241, d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c974 (pattern : Twelve) (guard : d1837 pattern = 1) : d949 pattern ≤ (0 : Int) + d841 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d949, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c973 pattern childGuard
    simpa only [d949, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d949, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c965 pattern childGuard
    simpa only [d949, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c975 (pattern : Twelve) (guard : d1837 pattern = 1) : d956 pattern ≤ (0 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d956, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c972 pattern childGuard
    simpa only [d956, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d956, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c974 pattern childGuard
    simpa only [d956, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c976 (pattern : Twelve) (guard : d1837 pattern = 1) : d963 pattern ≤ (0 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d963, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c967 pattern childGuard
    simpa only [d963, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d963, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c975 pattern childGuard
    simpa only [d963, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c977 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d816 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c978 (pattern : Twelve) (guard : d1837 pattern = 1) : d943 pattern ≤ (0 : Int) + d824 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d943, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c236 pattern childGuard
    simpa only [d1837, d943, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d943, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c977 pattern childGuard
    simpa only [d1837, d943, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c979 (pattern : Twelve) (guard : d1837 pattern = 1) : d950 pattern ≤ (0 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d950, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c839 pattern childGuard
    simpa only [d950, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d950, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c978 pattern childGuard
    simpa only [d950, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
