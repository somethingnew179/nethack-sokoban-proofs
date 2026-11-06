/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons127
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c17920 (pattern : Twelve) (guard : d1865 pattern = 1) : d564 pattern ≤ (1 : Int) + d75 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d564, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17918 pattern childGuard
    simpa only [d564, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d564, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17919 pattern childGuard
    simpa only [d564, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17921 (pattern : Twelve) (guard : d1865 pattern = 1) : d589 pattern ≤ (1 : Int) + d92 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d589, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17915 pattern childGuard
    simpa only [d589, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d589, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17920 pattern childGuard
    simpa only [d589, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17922 (pattern : Twelve) (guard : d1865 pattern = 1) : d606 pattern ≤ (1 : Int) + d102 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d606, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17905 pattern childGuard
    simpa only [d606, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d606, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17921 pattern childGuard
    simpa only [d606, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17923 (pattern : Twelve) (guard : d1865 pattern = 1) : d512 pattern ≤ (1 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d512, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12253 pattern childGuard
    simpa only [d512, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d512, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12223 pattern childGuard
    simpa only [d512, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17924 (pattern : Twelve) (guard : d1865 pattern = 1) : d541 pattern ≤ (1 : Int) + d50 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d541, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17923 pattern childGuard
    simpa only [d541, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d541, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12360 pattern childGuard
    simpa only [d541, d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17925 (pattern : Twelve) (guard : d1865 pattern = 1) : d565 pattern ≤ (1 : Int) + d72 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d565, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12283 pattern childGuard
    simpa only [d565, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d565, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17924 pattern childGuard
    simpa only [d565, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17926 (pattern : Twelve) (guard : d1865 pattern = 1) : d542 pattern ≤ (1 : Int) + d0 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12282 pattern childGuard
    simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12281 pattern childGuard
    simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17927 (pattern : Twelve) (guard : d1865 pattern = 1) : d566 pattern ≤ (1 : Int) + d76 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d566, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17926 pattern childGuard
    simpa only [d566, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d566, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17919 pattern childGuard
    simpa only [d566, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17928 (pattern : Twelve) (guard : d1865 pattern = 1) : d590 pattern ≤ (1 : Int) + d93 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d590, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17925 pattern childGuard
    simpa only [d590, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d590, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17927 pattern childGuard
    simpa only [d590, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17929 (pattern : Twelve) (guard : d1865 pattern = 1) : d544 pattern ≤ (1 : Int) + d57 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d544, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12367 pattern childGuard
    simpa only [d544, d57, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d544, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12302 pattern childGuard
    simpa only [d544, d57, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17930 (pattern : Twelve) (guard : d1865 pattern = 1) : d567 pattern ≤ (1 : Int) + d77 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d567, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12297 pattern childGuard
    simpa only [d567, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d567, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17929 pattern childGuard
    simpa only [d567, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17931 (pattern : Twelve) (guard : d1865 pattern = 1) : d568 pattern ≤ (1 : Int) + d78 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d568, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12378 pattern childGuard
    simpa only [d568, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d568, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17919 pattern childGuard
    simpa only [d568, d78, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17932 (pattern : Twelve) (guard : d1865 pattern = 1) : d591 pattern ≤ (1 : Int) + d94 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d591, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17930 pattern childGuard
    simpa only [d591, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d591, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17931 pattern childGuard
    simpa only [d591, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17933 (pattern : Twelve) (guard : d1865 pattern = 1) : d607 pattern ≤ (1 : Int) + d103 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d607, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17928 pattern childGuard
    simpa only [d607, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d607, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17932 pattern childGuard
    simpa only [d607, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17934 (pattern : Twelve) (guard : d1865 pattern = 1) : d618 pattern ≤ (1 : Int) + d110 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d618, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17922 pattern childGuard
    simpa only [d618, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d618, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17933 pattern childGuard
    simpa only [d618, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17935 (pattern : Twelve) (guard : d1865 pattern = 1) : d518 pattern ≤ (1 : Int) + d37 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d518, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12233 pattern childGuard
    simpa only [d518, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d518, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12319 pattern childGuard
    simpa only [d518, d37, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17936 (pattern : Twelve) (guard : d1865 pattern = 1) : d546 pattern ≤ (1 : Int) + d58 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d546, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12313 pattern childGuard
    simpa only [d546, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d546, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17935 pattern childGuard
    simpa only [d546, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17937 (pattern : Twelve) (guard : d1865 pattern = 1) : d569 pattern ≤ (1 : Int) + d79 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d569, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12314 pattern childGuard
    simpa only [d569, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d569, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17936 pattern childGuard
    simpa only [d569, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17938 (pattern : Twelve) (guard : d1865 pattern = 1) : d547 pattern ≤ (1 : Int) + d30 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12313 pattern childGuard
    simpa only [d547, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12367 pattern childGuard
    simpa only [d547, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17939 (pattern : Twelve) (guard : d1865 pattern = 1) : d570 pattern ≤ (1 : Int) + d80 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d570, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17938 pattern childGuard
    simpa only [d570, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d570, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17919 pattern childGuard
    simpa only [d570, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17940 (pattern : Twelve) (guard : d1865 pattern = 1) : d592 pattern ≤ (1 : Int) + d95 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d592, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17937 pattern childGuard
    simpa only [d592, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d592, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17939 pattern childGuard
    simpa only [d592, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17941 (pattern : Twelve) (guard : d1865 pattern = 1) : d549 pattern ≤ (1 : Int) + d60 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d549, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12387 pattern childGuard
    simpa only [d549, d60, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d549, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12339 pattern childGuard
    simpa only [d549, d60, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17942 (pattern : Twelve) (guard : d1865 pattern = 1) : d571 pattern ≤ (1 : Int) + d81 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d571, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12331 pattern childGuard
    simpa only [d571, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d571, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17941 pattern childGuard
    simpa only [d571, d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17943 (pattern : Twelve) (guard : d1 pattern = 1) : d16 pattern ≤ (1 : Int) + d16 pattern := by
  omega
theorem c17944 (pattern : Twelve) (guard : d1865 pattern = 1) : d495 pattern ≤ (1 : Int) + d25 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d495, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17943 pattern childGuard
    simpa only [d1865, d495, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d495, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12238 pattern childGuard
    simpa only [d1865, d495, d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17945 (pattern : Twelve) (guard : d1865 pattern = 1) : d522 pattern ≤ (1 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d522, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17944 pattern childGuard
    simpa only [d522, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d522, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d522, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17946 (pattern : Twelve) (guard : d1865 pattern = 1) : d550 pattern ≤ (1 : Int) + d61 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d550, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12334 pattern childGuard
    simpa only [d550, d61, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d550, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17945 pattern childGuard
    simpa only [d550, d61, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17947 (pattern : Twelve) (guard : d1865 pattern = 1) : d572 pattern ≤ (1 : Int) + d82 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d572, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12388 pattern childGuard
    simpa only [d572, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d572, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17946 pattern childGuard
    simpa only [d572, d82, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17948 (pattern : Twelve) (guard : d1865 pattern = 1) : d593 pattern ≤ (1 : Int) + d96 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d593, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17942 pattern childGuard
    simpa only [d593, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d593, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17947 pattern childGuard
    simpa only [d593, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17949 (pattern : Twelve) (guard : d1865 pattern = 1) : d608 pattern ≤ (1 : Int) + d104 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d608, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17940 pattern childGuard
    simpa only [d608, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d608, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17948 pattern childGuard
    simpa only [d608, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17950 (pattern : Twelve) (guard : d1865 pattern = 1) : d573 pattern ≤ (1 : Int) + d77 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d573, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12354 pattern childGuard
    simpa only [d573, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d573, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17929 pattern childGuard
    simpa only [d573, d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17951 (pattern : Twelve) (guard : d1865 pattern = 1) : d594 pattern ≤ (1 : Int) + d94 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d594, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17950 pattern childGuard
    simpa only [d594, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d594, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17931 pattern childGuard
    simpa only [d594, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17952 (pattern : Twelve) (guard : d1865 pattern = 1) : d609 pattern ≤ (1 : Int) + d105 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d609, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17951 pattern childGuard
    simpa only [d609, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d609, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d609, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17953 (pattern : Twelve) (guard : d1865 pattern = 1) : d619 pattern ≤ (1 : Int) + d111 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d619, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17949 pattern childGuard
    simpa only [d619, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d619, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17952 pattern childGuard
    simpa only [d619, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17954 (pattern : Twelve) (guard : d1865 pattern = 1) : d624 pattern ≤ (1 : Int) + d114 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d624, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17934 pattern childGuard
    simpa only [d624, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d624, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17953 pattern childGuard
    simpa only [d624, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17955 (pattern : Twelve) (guard : d1865 pattern = 1) : d513 pattern ≤ (1 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d513, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12281 pattern childGuard
    simpa only [d513, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d513, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12223 pattern childGuard
    simpa only [d513, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17956 (pattern : Twelve) (guard : d1865 pattern = 1) : d513 pattern ≤ (1 : Int) + d50 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17955 pattern childGuard
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12360 pattern childGuard
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17957 (pattern : Twelve) (guard : d1865 pattern = 1) : d574 pattern ≤ (1 : Int) + d72 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d574, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12281 pattern childGuard
    simpa only [d574, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d574, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17956 pattern childGuard
    simpa only [d574, d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17958 (pattern : Twelve) (guard : d1865 pattern = 1) : d524 pattern ≤ (1 : Int) + d28 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d524, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12233 pattern childGuard
    simpa only [d524, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d524, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17898 pattern childGuard
    simpa only [d524, d28, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17959 (pattern : Twelve) (guard : d1865 pattern = 1) : d552 pattern ≤ (1 : Int) + d51 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d552, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17958 pattern childGuard
    simpa only [d552, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d552, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17902 pattern childGuard
    simpa only [d552, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17960 (pattern : Twelve) (guard : d1865 pattern = 1) : d575 pattern ≤ (1 : Int) + d73 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d575, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12281 pattern childGuard
    simpa only [d575, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d575, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17959 pattern childGuard
    simpa only [d575, d73, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17961 (pattern : Twelve) (guard : d1865 pattern = 1) : d595 pattern ≤ (1 : Int) + d91 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d595, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17957 pattern childGuard
    simpa only [d595, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d595, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17960 pattern childGuard
    simpa only [d595, d91, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17962 (pattern : Twelve) (guard : d1865 pattern = 1) : d525 pattern ≤ (1 : Int) + d31 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d525, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12281 pattern childGuard
    simpa only [d525, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d525, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17907 pattern childGuard
    simpa only [d525, d31, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17963 (pattern : Twelve) (guard : d1865 pattern = 1) : d553 pattern ≤ (1 : Int) + d52 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d553, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12367 pattern childGuard
    simpa only [d553, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d553, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17962 pattern childGuard
    simpa only [d553, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17964 (pattern : Twelve) (guard : d1865 pattern = 1) : d554 pattern ≤ (1 : Int) + d53 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d554, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12367 pattern childGuard
    simpa only [d554, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d554, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17913 pattern childGuard
    simpa only [d554, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17965 (pattern : Twelve) (guard : d1865 pattern = 1) : d576 pattern ≤ (1 : Int) + d74 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d576, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17963 pattern childGuard
    simpa only [d576, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d576, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17964 pattern childGuard
    simpa only [d576, d74, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17966 (pattern : Twelve) (guard : d1865 pattern = 1) : d555 pattern ≤ (1 : Int) + d54 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d555, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12367 pattern childGuard
    simpa only [d555, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d555, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17917 pattern childGuard
    simpa only [d555, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17967 (pattern : Twelve) (guard : d1865 pattern = 1) : d577 pattern ≤ (1 : Int) + d75 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d577, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17966 pattern childGuard
    simpa only [d577, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d577, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17919 pattern childGuard
    simpa only [d577, d75, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17968 (pattern : Twelve) (guard : d1865 pattern = 1) : d596 pattern ≤ (1 : Int) + d92 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d596, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17965 pattern childGuard
    simpa only [d596, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d596, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17967 pattern childGuard
    simpa only [d596, d92, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17969 (pattern : Twelve) (guard : d1865 pattern = 1) : d610 pattern ≤ (1 : Int) + d102 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d610, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17961 pattern childGuard
    simpa only [d610, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d610, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17968 pattern childGuard
    simpa only [d610, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17970 (pattern : Twelve) (guard : d1865 pattern = 1) : d578 pattern ≤ (1 : Int) + d76 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d578, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12281 pattern childGuard
    simpa only [d578, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d578, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17919 pattern childGuard
    simpa only [d578, d76, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17971 (pattern : Twelve) (guard : d1865 pattern = 1) : d597 pattern ≤ (1 : Int) + d93 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d597, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17957 pattern childGuard
    simpa only [d597, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d597, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17970 pattern childGuard
    simpa only [d597, d93, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17972 (pattern : Twelve) (guard : d1865 pattern = 1) : d544 pattern ≤ (1 : Int) + d77 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12378 pattern childGuard
    simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17929 pattern childGuard
    simpa only [d77, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17973 (pattern : Twelve) (guard : d1865 pattern = 1) : d598 pattern ≤ (1 : Int) + d94 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d598, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17972 pattern childGuard
    simpa only [d598, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d598, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17931 pattern childGuard
    simpa only [d598, d94, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17974 (pattern : Twelve) (guard : d1865 pattern = 1) : d611 pattern ≤ (1 : Int) + d103 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d611, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17971 pattern childGuard
    simpa only [d611, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d611, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17973 pattern childGuard
    simpa only [d611, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17975 (pattern : Twelve) (guard : d1865 pattern = 1) : d620 pattern ≤ (1 : Int) + d110 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d620, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17969 pattern childGuard
    simpa only [d620, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d620, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17974 pattern childGuard
    simpa only [d620, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17976 (pattern : Twelve) (guard : d1865 pattern = 1) : d556 pattern ≤ (1 : Int) + d58 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d556, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12367 pattern childGuard
    simpa only [d556, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d556, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17935 pattern childGuard
    simpa only [d556, d58, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17977 (pattern : Twelve) (guard : d1865 pattern = 1) : d579 pattern ≤ (1 : Int) + d79 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d579, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12367 pattern childGuard
    simpa only [d579, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d579, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17976 pattern childGuard
    simpa only [d579, d79, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17978 (pattern : Twelve) (guard : d1865 pattern = 1) : d580 pattern ≤ (1 : Int) + d80 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d580, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12367 pattern childGuard
    simpa only [d580, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d580, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17919 pattern childGuard
    simpa only [d580, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17979 (pattern : Twelve) (guard : d1865 pattern = 1) : d599 pattern ≤ (1 : Int) + d95 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d599, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17977 pattern childGuard
    simpa only [d599, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d599, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17978 pattern childGuard
    simpa only [d599, d95, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17980 (pattern : Twelve) (guard : d1865 pattern = 1) : d549 pattern ≤ (1 : Int) + d81 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12388 pattern childGuard
    simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17941 pattern childGuard
    simpa only [d81, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17981 (pattern : Twelve) (guard : d1865 pattern = 1) : d600 pattern ≤ (1 : Int) + d96 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d600, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17980 pattern childGuard
    simpa only [d600, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d600, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17947 pattern childGuard
    simpa only [d600, d96, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17982 (pattern : Twelve) (guard : d1865 pattern = 1) : d612 pattern ≤ (1 : Int) + d104 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d612, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17979 pattern childGuard
    simpa only [d612, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d612, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17981 pattern childGuard
    simpa only [d612, d104, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17983 (pattern : Twelve) (guard : d1865 pattern = 1) : d613 pattern ≤ (1 : Int) + d105 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d613, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17973 pattern childGuard
    simpa only [d613, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d613, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d613, d105, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17984 (pattern : Twelve) (guard : d1865 pattern = 1) : d621 pattern ≤ (1 : Int) + d111 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d621, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17982 pattern childGuard
    simpa only [d621, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d621, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17983 pattern childGuard
    simpa only [d621, d111, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17985 (pattern : Twelve) (guard : d1865 pattern = 1) : d625 pattern ≤ (1 : Int) + d114 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d625, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17975 pattern childGuard
    simpa only [d625, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d625, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17984 pattern childGuard
    simpa only [d625, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17986 (pattern : Twelve) (guard : d1865 pattern = 1) : d627 pattern ≤ (1 : Int) + d114 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17954 pattern childGuard
    simpa only [d627, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17985 pattern childGuard
    simpa only [d627, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17987 (pattern : Twelve) (guard : d1865 pattern = 1) : d628 pattern ≤ (1 : Int) + d114 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17986 pattern childGuard
    simpa only [d628, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17985 pattern childGuard
    simpa only [d628, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17988 (pattern : Twelve) (guard : d1865 pattern = 1) : d526 pattern ≤ (1 : Int) + d120 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d526, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12233 pattern childGuard
    simpa only [d526, d120, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d526, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17944 pattern childGuard
    simpa only [d526, d120, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17989 (pattern : Twelve) (guard : d1865 pattern = 1) : d557 pattern ≤ (1 : Int) + d129 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d557, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17988 pattern childGuard
    simpa only [d557, d129, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d557, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17902 pattern childGuard
    simpa only [d557, d129, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17990 (pattern : Twelve) (guard : d1865 pattern = 1) : d581 pattern ≤ (1 : Int) + d136 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d581, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12281 pattern childGuard
    simpa only [d581, d136, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d581, d136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17989 pattern childGuard
    simpa only [d581, d136, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17991 (pattern : Twelve) (guard : d1865 pattern = 1) : d601 pattern ≤ (1 : Int) + d144 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d601, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17957 pattern childGuard
    simpa only [d601, d144, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d601, d144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17990 pattern childGuard
    simpa only [d601, d144, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17992 (pattern : Twelve) (guard : d1865 pattern = 1) : d509 pattern ≤ (1 : Int) + d121 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d509, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12281 pattern childGuard
    simpa only [d509, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d509, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12260 pattern childGuard
    simpa only [d509, d121, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17993 (pattern : Twelve) (guard : d1865 pattern = 1) : d544 pattern ≤ (1 : Int) + d130 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d544, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17992 pattern childGuard
    simpa only [d544, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d544, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12302 pattern childGuard
    simpa only [d544, d130, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17994 (pattern : Twelve) (guard : d1865 pattern = 1) : d582 pattern ≤ (1 : Int) + d137 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d582, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17963 pattern childGuard
    simpa only [d582, d137, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d582, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17993 pattern childGuard
    simpa only [d582, d137, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17995 (pattern : Twelve) (guard : d1865 pattern = 1) : d583 pattern ≤ (1 : Int) + d138 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d583, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12378 pattern childGuard
    simpa only [d583, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d583, d138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17989 pattern childGuard
    simpa only [d583, d138, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17996 (pattern : Twelve) (guard : d1865 pattern = 1) : d602 pattern ≤ (1 : Int) + d145 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d602, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17994 pattern childGuard
    simpa only [d602, d145, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d602, d145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17995 pattern childGuard
    simpa only [d602, d145, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17997 (pattern : Twelve) (guard : d1865 pattern = 1) : d614 pattern ≤ (1 : Int) + d149 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d614, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17991 pattern childGuard
    simpa only [d614, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d614, d149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17996 pattern childGuard
    simpa only [d614, d149, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17998 (pattern : Twelve) (guard : d1865 pattern = 1) : d544 pattern ≤ (1 : Int) + d139 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12378 pattern childGuard
    simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17993 pattern childGuard
    simpa only [d139, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c17999 (pattern : Twelve) (guard : d1865 pattern = 1) : d603 pattern ≤ (1 : Int) + d146 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d603, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17998 pattern childGuard
    simpa only [d603, d146, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d603, d146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17995 pattern childGuard
    simpa only [d603, d146, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18000 (pattern : Twelve) (guard : d1865 pattern = 1) : d615 pattern ≤ (1 : Int) + d150 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d615, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17991 pattern childGuard
    simpa only [d615, d150, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d615, d150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17999 pattern childGuard
    simpa only [d615, d150, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18001 (pattern : Twelve) (guard : d1865 pattern = 1) : d622 pattern ≤ (1 : Int) + d153 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d622, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17997 pattern childGuard
    simpa only [d622, d153, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d622, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18000 pattern childGuard
    simpa only [d622, d153, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18002 (pattern : Twelve) (guard : d1865 pattern = 1) : d527 pattern ≤ (1 : Int) + d122 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d527, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12233 pattern childGuard
    simpa only [d527, d122, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d527, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12328 pattern childGuard
    simpa only [d527, d122, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18003 (pattern : Twelve) (guard : d1865 pattern = 1) : d558 pattern ≤ (1 : Int) + d131 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d558, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17992 pattern childGuard
    simpa only [d558, d131, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d558, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18002 pattern childGuard
    simpa only [d558, d131, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18004 (pattern : Twelve) (guard : d1865 pattern = 1) : d584 pattern ≤ (1 : Int) + d140 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d584, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12367 pattern childGuard
    simpa only [d584, d140, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d584, d140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18003 pattern childGuard
    simpa only [d584, d140, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18005 (pattern : Twelve) (guard : d1865 pattern = 1) : d518 pattern ≤ (1 : Int) + d123 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d518, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12281 pattern childGuard
    simpa only [d518, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d518, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12319 pattern childGuard
    simpa only [d518, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18006 (pattern : Twelve) (guard : d1865 pattern = 1) : d556 pattern ≤ (1 : Int) + d132 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d556, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12367 pattern childGuard
    simpa only [d556, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d556, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18005 pattern childGuard
    simpa only [d556, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18007 (pattern : Twelve) (guard : d1865 pattern = 1) : d585 pattern ≤ (1 : Int) + d141 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d585, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18006 pattern childGuard
    simpa only [d585, d141, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d585, d141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17989 pattern childGuard
    simpa only [d585, d141, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18008 (pattern : Twelve) (guard : d1865 pattern = 1) : d604 pattern ≤ (1 : Int) + d147 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d604, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18004 pattern childGuard
    simpa only [d604, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d604, d147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18007 pattern childGuard
    simpa only [d604, d147, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18009 (pattern : Twelve) (guard : d1865 pattern = 1) : d528 pattern ≤ (1 : Int) + d124 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d528, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12294 pattern childGuard
    simpa only [d528, d124, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d528, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12433 pattern childGuard
    simpa only [d528, d124, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18010 (pattern : Twelve) (guard : d1865 pattern = 1) : d559 pattern ≤ (1 : Int) + d133 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d559, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18009 pattern childGuard
    simpa only [d559, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d559, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12435 pattern childGuard
    simpa only [d559, d133, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18011 (pattern : Twelve) (guard : d1865 pattern = 1) : d586 pattern ≤ (1 : Int) + d142 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d586, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12388 pattern childGuard
    simpa only [d586, d142, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d586, d142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18010 pattern childGuard
    simpa only [d586, d142, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18012 (pattern : Twelve) (guard : d1865 pattern = 1) : d497 pattern ≤ (1 : Int) + d5 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11385 pattern childGuard
    simpa only [d1865, d497, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c16043 pattern childGuard
    simpa only [d1865, d497, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18013 (pattern : Twelve) (guard : d1865 pattern = 1) : d528 pattern ≤ (1 : Int) + d126 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d528, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12294 pattern childGuard
    simpa only [d528, d126, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d528, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18012 pattern childGuard
    simpa only [d528, d126, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18014 (pattern : Twelve) (guard : d1865 pattern = 1) : d529 pattern ≤ (1 : Int) + d47 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d529, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12319 pattern childGuard
    simpa only [d529, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d529, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d529, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18015 (pattern : Twelve) (guard : d1865 pattern = 1) : d559 pattern ≤ (1 : Int) + d134 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d559, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18013 pattern childGuard
    simpa only [d559, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d559, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18014 pattern childGuard
    simpa only [d559, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18016 (pattern : Twelve) (guard : d1865 pattern = 1) : d530 pattern ≤ (1 : Int) + d127 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d530, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12260 pattern childGuard
    simpa only [d530, d127, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d530, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17916 pattern childGuard
    simpa only [d530, d127, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18017 (pattern : Twelve) (guard : d1865 pattern = 1) : d531 pattern ≤ (1 : Int) + d128 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d531, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17907 pattern childGuard
    simpa only [d531, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d531, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d531, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18018 (pattern : Twelve) (guard : d1865 pattern = 1) : d560 pattern ≤ (1 : Int) + d135 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d560, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18016 pattern childGuard
    simpa only [d560, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d560, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18017 pattern childGuard
    simpa only [d560, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18019 (pattern : Twelve) (guard : d1865 pattern = 1) : d587 pattern ≤ (1 : Int) + d143 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d587, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18015 pattern childGuard
    simpa only [d587, d143, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d587, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18018 pattern childGuard
    simpa only [d587, d143, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18020 (pattern : Twelve) (guard : d1865 pattern = 1) : d605 pattern ≤ (1 : Int) + d148 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d605, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18011 pattern childGuard
    simpa only [d605, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d605, d148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18019 pattern childGuard
    simpa only [d605, d148, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18021 (pattern : Twelve) (guard : d1865 pattern = 1) : d616 pattern ≤ (1 : Int) + d151 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d616, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18008 pattern childGuard
    simpa only [d616, d151, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d616, d151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18020 pattern childGuard
    simpa only [d616, d151, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18022 (pattern : Twelve) (guard : d1865 pattern = 1) : d617 pattern ≤ (1 : Int) + d152 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d617, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17999 pattern childGuard
    simpa only [d617, d152, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d617, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d617, d152, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18023 (pattern : Twelve) (guard : d1865 pattern = 1) : d623 pattern ≤ (1 : Int) + d154 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d623, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18021 pattern childGuard
    simpa only [d623, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d623, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18022 pattern childGuard
    simpa only [d623, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18024 (pattern : Twelve) (guard : d1865 pattern = 1) : d626 pattern ≤ (1 : Int) + d155 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d626, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18001 pattern childGuard
    simpa only [d626, d155, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d626, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18023 pattern childGuard
    simpa only [d626, d155, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18025 (pattern : Twelve) (guard : d1865 pattern = 1) : d629 pattern ≤ (1 : Int) + d156 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d629, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17987 pattern childGuard
    simpa only [d629, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d629, d156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18024 pattern childGuard
    simpa only [d629, d156, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18026 (pattern : Twelve) (guard : d1865 pattern = 1) : d1105 pattern ≤ (1 : Int) + d814 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d1105, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11211 pattern childGuard
    simpa only [d1865, d1105, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d1105, d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11094 pattern childGuard
    simpa only [d1865, d1105, d814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18027 (pattern : Twelve) (guard : d1865 pattern = 1) : d1108 pattern ≤ (1 : Int) + d816 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1108, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18026 pattern childGuard
    simpa only [d1108, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1108, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12223 pattern childGuard
    simpa only [d1108, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18028 (pattern : Twelve) (guard : d1865 pattern = 1) : d1118 pattern ≤ (1 : Int) + d824 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1118, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17891 pattern childGuard
    simpa only [d1118, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1118, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18027 pattern childGuard
    simpa only [d1118, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18029 (pattern : Twelve) (guard : d1865 pattern = 1) : d1132 pattern ≤ (1 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1132, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17896 pattern childGuard
    simpa only [d1132, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1132, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18028 pattern childGuard
    simpa only [d1132, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18030 (pattern : Twelve) (guard : d1865 pattern = 1) : d1119 pattern ≤ (1 : Int) + d17 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12234 pattern childGuard
    simpa only [d1119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12233 pattern childGuard
    simpa only [d1119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18031 (pattern : Twelve) (guard : d1865 pattern = 1) : d1109 pattern ≤ (1 : Int) + d817 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1109, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17901 pattern childGuard
    simpa only [d1109, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1109, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17944 pattern childGuard
    simpa only [d1109, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18032 (pattern : Twelve) (guard : d1865 pattern = 1) : d1120 pattern ≤ (1 : Int) + d825 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1120, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18031 pattern childGuard
    simpa only [d1120, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1120, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17945 pattern childGuard
    simpa only [d1120, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18033 (pattern : Twelve) (guard : d1865 pattern = 1) : d1133 pattern ≤ (1 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1133, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18030 pattern childGuard
    simpa only [d1133, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1133, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18032 pattern childGuard
    simpa only [d1133, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18034 (pattern : Twelve) (guard : d1865 pattern = 1) : d1152 pattern ≤ (1 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1152, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18029 pattern childGuard
    simpa only [d1152, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1152, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18033 pattern childGuard
    simpa only [d1152, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18035 (pattern : Twelve) (guard : d1865 pattern = 1) : d1121 pattern ≤ (1 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1121, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17910 pattern childGuard
    simpa only [d1121, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1121, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12296 pattern childGuard
    simpa only [d1121, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18036 (pattern : Twelve) (guard : d1865 pattern = 1) : d1110 pattern ≤ (1 : Int) + d818 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1110, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18026 pattern childGuard
    simpa only [d1110, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1110, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1110, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18037 (pattern : Twelve) (guard : d1865 pattern = 1) : d1122 pattern ≤ (1 : Int) + d826 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1122, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12298 pattern childGuard
    simpa only [d1122, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1122, d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18036 pattern childGuard
    simpa only [d1122, d826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18038 (pattern : Twelve) (guard : d1865 pattern = 1) : d1134 pattern ≤ (1 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1134, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18035 pattern childGuard
    simpa only [d1134, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1134, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18037 pattern childGuard
    simpa only [d1134, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18039 (pattern : Twelve) (guard : d1865 pattern = 1) : d1135 pattern ≤ (1 : Int) + d841 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1135, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12303 pattern childGuard
    simpa only [d1135, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1135, d841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18032 pattern childGuard
    simpa only [d1135, d841, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18040 (pattern : Twelve) (guard : d1865 pattern = 1) : d1153 pattern ≤ (1 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1153, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18038 pattern childGuard
    simpa only [d1153, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1153, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18039 pattern childGuard
    simpa only [d1153, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18041 (pattern : Twelve) (guard : d1865 pattern = 1) : d1164 pattern ≤ (1 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1164, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18034 pattern childGuard
    simpa only [d1164, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1164, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18040 pattern childGuard
    simpa only [d1164, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18042 (pattern : Twelve) (guard : d1865 pattern = 1) : d1123 pattern ≤ (1 : Int) + d824 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1123, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12360 pattern childGuard
    simpa only [d1123, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1123, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18027 pattern childGuard
    simpa only [d1123, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18043 (pattern : Twelve) (guard : d1865 pattern = 1) : d1136 pattern ≤ (1 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1136, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17926 pattern childGuard
    simpa only [d1136, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1136, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18042 pattern childGuard
    simpa only [d1136, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18044 (pattern : Twelve) (guard : d1865 pattern = 1) : d1137 pattern ≤ (1 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1137, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12233 pattern childGuard
    simpa only [d1137, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1137, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18032 pattern childGuard
    simpa only [d1137, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18045 (pattern : Twelve) (guard : d1865 pattern = 1) : d1154 pattern ≤ (1 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1154, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18043 pattern childGuard
    simpa only [d1154, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1154, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18044 pattern childGuard
    simpa only [d1154, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18046 (pattern : Twelve) (guard : d1865 pattern = 1) : d1138 pattern ≤ (1 : Int) + d840 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1138, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12378 pattern childGuard
    simpa only [d1138, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1138, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18037 pattern childGuard
    simpa only [d1138, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18047 (pattern : Twelve) (guard : d1865 pattern = 1) : d1155 pattern ≤ (1 : Int) + d854 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1155, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18046 pattern childGuard
    simpa only [d1155, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1155, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18039 pattern childGuard
    simpa only [d1155, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18048 (pattern : Twelve) (guard : d1865 pattern = 1) : d1165 pattern ≤ (1 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1165, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18045 pattern childGuard
    simpa only [d1165, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1165, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18047 pattern childGuard
    simpa only [d1165, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18049 (pattern : Twelve) (guard : d1865 pattern = 1) : d1173 pattern ≤ (1 : Int) + d861 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18041 pattern childGuard
    simpa only [d1173, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18048 pattern childGuard
    simpa only [d1173, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18050 (pattern : Twelve) (guard : d1865 pattern = 1) : d1111 pattern ≤ (1 : Int) + d819 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1111, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18026 pattern childGuard
    simpa only [d1111, d819, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1111, d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12319 pattern childGuard
    simpa only [d1111, d819, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18051 (pattern : Twelve) (guard : d1865 pattern = 1) : d1124 pattern ≤ (1 : Int) + d828 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1124, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12298 pattern childGuard
    simpa only [d1124, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1124, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18050 pattern childGuard
    simpa only [d1124, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18052 (pattern : Twelve) (guard : d1865 pattern = 1) : d1139 pattern ≤ (1 : Int) + d842 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1139, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17938 pattern childGuard
    simpa only [d1139, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1139, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18051 pattern childGuard
    simpa only [d1139, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18053 (pattern : Twelve) (guard : d1865 pattern = 1) : d1140 pattern ≤ (1 : Int) + d843 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1140, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12298 pattern childGuard
    simpa only [d1140, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1140, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18032 pattern childGuard
    simpa only [d1140, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18054 (pattern : Twelve) (guard : d1865 pattern = 1) : d1156 pattern ≤ (1 : Int) + d855 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1156, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18052 pattern childGuard
    simpa only [d1156, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1156, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18053 pattern childGuard
    simpa only [d1156, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18055 (pattern : Twelve) (guard : d1865 pattern = 1) : d1106 pattern ≤ (1 : Int) + d815 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1865, d1106, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c11266 pattern childGuard
    simpa only [d1865, d1106, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1865, d1106, d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12318 pattern childGuard
    simpa only [d1865, d1106, d815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18056 (pattern : Twelve) (guard : d1865 pattern = 1) : d1112 pattern ≤ (1 : Int) + d820 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1112, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18055 pattern childGuard
    simpa only [d1112, d820, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1112, d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12242 pattern childGuard
    simpa only [d1112, d820, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18057 (pattern : Twelve) (guard : d1865 pattern = 1) : d1125 pattern ≤ (1 : Int) + d829 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1125, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12334 pattern childGuard
    simpa only [d1125, d829, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1125, d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18056 pattern childGuard
    simpa only [d1125, d829, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18058 (pattern : Twelve) (guard : d1865 pattern = 1) : d1141 pattern ≤ (1 : Int) + d844 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1141, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c12388 pattern childGuard
    simpa only [d1141, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1141, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c18057 pattern childGuard
    simpa only [d1141, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c18059 (pattern : Twelve) (guard : d1865 pattern = 1) : d1113 pattern ≤ (1 : Int) + d821 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1113, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17944 pattern childGuard
    simpa only [d1113, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1865 pattern = 1 := by simpa only [d1113, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c17912 pattern childGuard
    simpa only [d1113, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
