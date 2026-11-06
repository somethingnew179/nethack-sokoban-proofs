/- Staged soko4-1 certificate. No result until all kernel checks pass. -/
import NetHack.Sokoban41.Comparisons18
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem c3040 (pattern : Ten) (guard : d389 pattern = 1) : d49 pattern ≤ (2 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d389, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2382 pattern childGuard
    simpa only [d389, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d389, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3039 pattern childGuard
    simpa only [d389, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3041 (pattern : Ten) (guard : d518 pattern = 1) : d54 pattern ≤ (2 : Int) + d42 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d518, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3038 pattern childGuard
    simpa only [d518, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d389 pattern = 1 := by simpa only [d518, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3040 pattern childGuard
    simpa only [d518, d54, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3042 (pattern : Ten) (guard : d389 pattern = 1) : d10 pattern ≤ (2 : Int) + d10 pattern := by
  omega
theorem c3043 (pattern : Ten) (guard : d518 pattern = 1) : d27 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d518, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2963 pattern childGuard
    simpa only [d518, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d389 pattern = 1 := by simpa only [d518, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3042 pattern childGuard
    simpa only [d518, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3044 (pattern : Ten) (guard : d518 pattern = 1) : d58 pattern ≤ (2 : Int) + d524 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d518 pattern = 1 := by simpa only [d58, d524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3041 pattern childGuard
    simpa only [d58, d524, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d518 pattern = 1 := by simpa only [d58, d524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3043 pattern childGuard
    simpa only [d58, d524, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3045 (pattern : Ten) (guard : d0 pattern = 1) : d50 pattern ≤ (2 : Int) + d43 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3046 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (2 : Int) + d43 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3047 (pattern : Ten) (guard : d389 pattern = 1) : d51 pattern ≤ (2 : Int) + d43 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d389, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2385 pattern childGuard
    simpa only [d389, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d389, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3046 pattern childGuard
    simpa only [d389, d51, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3048 (pattern : Ten) (guard : d518 pattern = 1) : d55 pattern ≤ (2 : Int) + d43 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d518, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3045 pattern childGuard
    simpa only [d518, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d389 pattern = 1 := by simpa only [d518, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3047 pattern childGuard
    simpa only [d518, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3049 (pattern : Ten) (guard : d518 pattern = 1) : d59 pattern ≤ (2 : Int) + d525 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d518 pattern = 1 := by simpa only [d59, d525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3048 pattern childGuard
    simpa only [d59, d525, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d518 pattern = 1 := by simpa only [d59, d525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3043 pattern childGuard
    simpa only [d59, d525, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3050 (pattern : Ten) (guard : d518 pattern = 1) : d62 pattern ≤ (2 : Int) + d526 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d518 pattern = 1 := by simpa only [d62, d526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3044 pattern childGuard
    simpa only [d62, d526, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d518 pattern = 1 := by simpa only [d62, d526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3049 pattern childGuard
    simpa only [d62, d526, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3051 (pattern : Ten) (guard : d518 pattern = 1) : d64 pattern ≤ (2 : Int) + d527 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d518 pattern = 1 := by simpa only [d64, d527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3041 pattern childGuard
    simpa only [d64, d527, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d518 pattern = 1 := by simpa only [d64, d527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3050 pattern childGuard
    simpa only [d64, d527, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3052 (pattern : Ten) (guard : d0 pattern = 1) : d7 pattern ≤ (2 : Int) + d528 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3053 (pattern : Ten) (guard : d519 pattern = 1) : d133 pattern ≤ (2 : Int) + d529 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d518 pattern = 1 := by simpa only [d519, d133, d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3051 pattern childGuard
    simpa only [d519, d133, d529, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d519, d133, d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3052 pattern childGuard
    simpa only [d519, d133, d529, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3054 (pattern : Ten) (guard : d0 pattern = 1) : d202 pattern ≤ (2 : Int) + d197 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3055 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (2 : Int) + d197 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3056 (pattern : Ten) (guard : d386 pattern = 1) : d203 pattern ≤ (2 : Int) + d197 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d386, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2419 pattern childGuard
    simpa only [d386, d203, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d386, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3055 pattern childGuard
    simpa only [d386, d203, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3057 (pattern : Ten) (guard : d520 pattern = 1) : d207 pattern ≤ (2 : Int) + d197 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d520, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3054 pattern childGuard
    simpa only [d520, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d386 pattern = 1 := by simpa only [d520, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3056 pattern childGuard
    simpa only [d520, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3058 (pattern : Ten) (guard : d520 pattern = 1) : d10 pattern ≤ (2 : Int) + d10 pattern := by
  omega
theorem c3059 (pattern : Ten) (guard : d520 pattern = 1) : d211 pattern ≤ (2 : Int) + d531 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d520 pattern = 1 := by simpa only [d211, d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3057 pattern childGuard
    simpa only [d211, d531, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d520 pattern = 1 := by simpa only [d211, d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3058 pattern childGuard
    simpa only [d211, d531, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3060 (pattern : Ten) (guard : d0 pattern = 1) : d204 pattern ≤ (2 : Int) + d198 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3061 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (2 : Int) + d198 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3062 (pattern : Ten) (guard : d386 pattern = 1) : d205 pattern ≤ (2 : Int) + d198 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d386, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2423 pattern childGuard
    simpa only [d386, d205, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d386, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3061 pattern childGuard
    simpa only [d386, d205, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3063 (pattern : Ten) (guard : d520 pattern = 1) : d208 pattern ≤ (2 : Int) + d198 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d520, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3060 pattern childGuard
    simpa only [d520, d208, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d386 pattern = 1 := by simpa only [d520, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3062 pattern childGuard
    simpa only [d520, d208, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3064 (pattern : Ten) (guard : d520 pattern = 1) : d212 pattern ≤ (2 : Int) + d532 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d520 pattern = 1 := by simpa only [d212, d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3063 pattern childGuard
    simpa only [d212, d532, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d520 pattern = 1 := by simpa only [d212, d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3058 pattern childGuard
    simpa only [d212, d532, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3065 (pattern : Ten) (guard : d520 pattern = 1) : d215 pattern ≤ (2 : Int) + d533 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d520 pattern = 1 := by simpa only [d215, d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3059 pattern childGuard
    simpa only [d215, d533, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d520 pattern = 1 := by simpa only [d215, d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3064 pattern childGuard
    simpa only [d215, d533, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3066 (pattern : Ten) (guard : d520 pattern = 1) : d218 pattern ≤ (2 : Int) + d534 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d520 pattern = 1 := by simpa only [d218, d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3057 pattern childGuard
    simpa only [d218, d534, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d520 pattern = 1 := by simpa only [d218, d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3065 pattern childGuard
    simpa only [d218, d534, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3067 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (2 : Int) + d535 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3068 (pattern : Ten) (guard : d521 pattern = 1) : d289 pattern ≤ (2 : Int) + d536 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d520 pattern = 1 := by simpa only [d521, d289, d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3066 pattern childGuard
    simpa only [d521, d289, d536, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d521, d289, d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3067 pattern childGuard
    simpa only [d521, d289, d536, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3069 (pattern : Ten) (guard : d0 pattern = 1) : d130 pattern ≤ (0 : Int) + d62 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3070 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (0 : Int) + d62 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3071 (pattern : Ten) (guard : d538 pattern = 1) : d131 pattern ≤ (0 : Int) + d62 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d373 pattern = 1 := by simpa only [d538, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c795 pattern childGuard
    simpa only [d538, d131, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d538, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3070 pattern childGuard
    simpa only [d538, d131, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3072 (pattern : Ten) (guard : d539 pattern = 1) : d132 pattern ≤ (0 : Int) + d62 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d539, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3069 pattern childGuard
    simpa only [d539, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d538 pattern = 1 := by simpa only [d539, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3071 pattern childGuard
    simpa only [d539, d132, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3073 (pattern : Ten) (guard : d0 pattern = 1) : d286 pattern ≤ (0 : Int) + d215 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3074 (pattern : Ten) (guard : d541 pattern = 1) : d287 pattern ≤ (0 : Int) + d215 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d372 pattern = 1 := by simpa only [d541, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c809 pattern childGuard
    simpa only [d541, d287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d541, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c912 pattern childGuard
    simpa only [d541, d287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3075 (pattern : Ten) (guard : d542 pattern = 1) : d288 pattern ≤ (0 : Int) + d215 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d542, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3073 pattern childGuard
    simpa only [d542, d288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d541 pattern = 1 := by simpa only [d542, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3074 pattern childGuard
    simpa only [d542, d288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3076 (pattern : Ten) (guard : d0 pattern = 1) : d134 pattern ≤ (2 : Int) + d547 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3077 (pattern : Ten) (guard : d1 pattern = 1) : d7 pattern ≤ (2 : Int) + d6 pattern := by
  change (7 : Int) ≤ (2 : Int) + 6
  decide
theorem c3078 (pattern : Ten) (guard : d1 pattern = 1) : d38 pattern ≤ (2 : Int) + d6 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3077 pattern childGuard
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2421 pattern childGuard
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3079 (pattern : Ten) (guard : d1 pattern = 1) : d40 pattern ≤ (2 : Int) + d6 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3078 pattern childGuard
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2421 pattern childGuard
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3080 (pattern : Ten) (guard : d0 pattern = 1) : d40 pattern ≤ (2 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3081 (pattern : Ten) (guard : d350 pattern = 1) : d40 pattern ≤ (2 : Int) + d6 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3079 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3080 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3082 (pattern : Ten) (guard : d350 pattern = 1) : d46 pattern ≤ (2 : Int) + d43 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d46, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3081 pattern childGuard
    simpa only [d46, d43, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d46, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d46, d43, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3083 (pattern : Ten) (guard : d350 pattern = 1) : d52 pattern ≤ (2 : Int) + d49 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d52, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3082 pattern childGuard
    simpa only [d52, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d52, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d52, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3084 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (2 : Int) + d49 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3085 (pattern : Ten) (guard : d373 pattern = 1) : d56 pattern ≤ (2 : Int) + d49 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d373, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3083 pattern childGuard
    simpa only [d373, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d373, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3084 pattern childGuard
    simpa only [d373, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3086 (pattern : Ten) (guard : d0 pattern = 1) : d56 pattern ≤ (2 : Int) + d546 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3087 (pattern : Ten) (guard : d538 pattern = 1) : d56 pattern ≤ (2 : Int) + d547 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d373 pattern = 1 := by simpa only [d538, d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3085 pattern childGuard
    simpa only [d538, d547, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d538, d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3086 pattern childGuard
    simpa only [d538, d547, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3088 (pattern : Ten) (guard : d539 pattern = 1) : d135 pattern ≤ (2 : Int) + d547 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d539, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3076 pattern childGuard
    simpa only [d539, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d538 pattern = 1 := by simpa only [d539, d135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3087 pattern childGuard
    simpa only [d539, d135, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3089 (pattern : Ten) (guard : d0 pattern = 1) : d290 pattern ≤ (2 : Int) + d552 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3090 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (2 : Int) + d203 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3091 (pattern : Ten) (guard : d372 pattern = 1) : d209 pattern ≤ (2 : Int) + d203 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d372, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2424 pattern childGuard
    simpa only [d372, d209, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d372, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3090 pattern childGuard
    simpa only [d372, d209, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3092 (pattern : Ten) (guard : d0 pattern = 1) : d209 pattern ≤ (2 : Int) + d551 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3093 (pattern : Ten) (guard : d541 pattern = 1) : d209 pattern ≤ (2 : Int) + d552 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d372 pattern = 1 := by simpa only [d541, d552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3091 pattern childGuard
    simpa only [d541, d552, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d541, d552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3092 pattern childGuard
    simpa only [d541, d552, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3094 (pattern : Ten) (guard : d542 pattern = 1) : d291 pattern ≤ (2 : Int) + d552 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d542, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3089 pattern childGuard
    simpa only [d542, d291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d541 pattern = 1 := by simpa only [d542, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3093 pattern childGuard
    simpa only [d542, d291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3095 (pattern : Ten) (guard : d0 pattern = 1) : d151 pattern ≤ (2 : Int) + d54 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3096 (pattern : Ten) (guard : d395 pattern = 1) : d54 pattern ≤ (2 : Int) + d54 pattern := by
  omega
theorem c3097 (pattern : Ten) (guard : d0 pattern = 1) : d55 pattern ≤ (2 : Int) + d54 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3098 (pattern : Ten) (guard : d554 pattern = 1) : d152 pattern ≤ (2 : Int) + d54 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d554, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3096 pattern childGuard
    simpa only [d554, d152, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d554, d152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3097 pattern childGuard
    simpa only [d554, d152, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3099 (pattern : Ten) (guard : d555 pattern = 1) : d154 pattern ≤ (2 : Int) + d54 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d555, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3095 pattern childGuard
    simpa only [d555, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d554 pattern = 1 := by simpa only [d555, d154, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3098 pattern childGuard
    simpa only [d555, d154, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3100 (pattern : Ten) (guard : d0 pattern = 1) : d56 pattern ≤ (2 : Int) + d56 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3101 (pattern : Ten) (guard : d395 pattern = 1) : d56 pattern ≤ (2 : Int) + d56 pattern := by
  omega
theorem c3102 (pattern : Ten) (guard : d0 pattern = 1) : d57 pattern ≤ (2 : Int) + d56 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3103 (pattern : Ten) (guard : d554 pattern = 1) : d153 pattern ≤ (2 : Int) + d56 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d395 pattern = 1 := by simpa only [d554, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3101 pattern childGuard
    simpa only [d554, d153, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d554, d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3102 pattern childGuard
    simpa only [d554, d153, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3104 (pattern : Ten) (guard : d555 pattern = 1) : d155 pattern ≤ (2 : Int) + d56 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d555, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3100 pattern childGuard
    simpa only [d555, d155, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d554 pattern = 1 := by simpa only [d555, d155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3103 pattern childGuard
    simpa only [d555, d155, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3105 (pattern : Ten) (guard : d555 pattern = 1) : d156 pattern ≤ (2 : Int) + d556 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d555 pattern = 1 := by simpa only [d156, d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3099 pattern childGuard
    simpa only [d156, d556, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d555 pattern = 1 := by simpa only [d156, d556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3104 pattern childGuard
    simpa only [d156, d556, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3106 (pattern : Ten) (guard : d0 pattern = 1) : d326 pattern ≤ (2 : Int) + d207 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3107 (pattern : Ten) (guard : d1 pattern = 1) : d1 pattern ≤ (2 : Int) + d0 pattern := by
  change (1 : Int) ≤ (2 : Int) + 0
  decide
theorem c3108 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (2 : Int) + d1 pattern := by
  change (2 : Int) ≤ (2 : Int) + 1
  decide
theorem c3109 (pattern : Ten) (guard : d1 pattern = 1) : d309 pattern ≤ (2 : Int) + d171 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d309, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3107 pattern childGuard
    simpa only [d309, d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d309, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3108 pattern childGuard
    simpa only [d309, d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3110 (pattern : Ten) (guard : d1 pattern = 1) : d313 pattern ≤ (2 : Int) + d171 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2755 pattern childGuard
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3109 pattern childGuard
    simpa only [d313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3111 (pattern : Ten) (guard : d1 pattern = 1) : d3 pattern ≤ (2 : Int) + d2 pattern := by
  change (3 : Int) ≤ (2 : Int) + 2
  decide
theorem c3112 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (2 : Int) + d3 pattern := by
  change (4 : Int) ≤ (2 : Int) + 3
  decide
theorem c3113 (pattern : Ten) (guard : d1 pattern = 1) : d310 pattern ≤ (2 : Int) + d172 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d310, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3111 pattern childGuard
    simpa only [d310, d172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d310, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3112 pattern childGuard
    simpa only [d310, d172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3114 (pattern : Ten) (guard : d1 pattern = 1) : d314 pattern ≤ (2 : Int) + d172 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2768 pattern childGuard
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3113 pattern childGuard
    simpa only [d314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3115 (pattern : Ten) (guard : d1 pattern = 1) : d317 pattern ≤ (2 : Int) + d174 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d317, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3110 pattern childGuard
    simpa only [d317, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d317, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3114 pattern childGuard
    simpa only [d317, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3116 (pattern : Ten) (guard : d1 pattern = 1) : d193 pattern ≤ (2 : Int) + d193 pattern := by
  omega
theorem c3117 (pattern : Ten) (guard : d1 pattern = 1) : d5 pattern ≤ (2 : Int) + d4 pattern := by
  change (5 : Int) ≤ (2 : Int) + 4
  decide
theorem c3118 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (2 : Int) + d5 pattern := by
  change (6 : Int) ≤ (2 : Int) + 5
  decide
theorem c3119 (pattern : Ten) (guard : d1 pattern = 1) : d311 pattern ≤ (2 : Int) + d193 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d311, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3117 pattern childGuard
    simpa only [d311, d193, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d311, d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3118 pattern childGuard
    simpa only [d311, d193, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3120 (pattern : Ten) (guard : d1 pattern = 1) : d315 pattern ≤ (2 : Int) + d193 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3116 pattern childGuard
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3119 pattern childGuard
    simpa only [d315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3121 (pattern : Ten) (guard : d1 pattern = 1) : d318 pattern ≤ (2 : Int) + d197 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d318, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3120 pattern childGuard
    simpa only [d318, d197, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d318, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d318, d197, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3122 (pattern : Ten) (guard : d1 pattern = 1) : d321 pattern ≤ (2 : Int) + d202 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d321, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3115 pattern childGuard
    simpa only [d321, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d321, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3121 pattern childGuard
    simpa only [d321, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3123 (pattern : Ten) (guard : d1 pattern = 1) : d194 pattern ≤ (2 : Int) + d194 pattern := by
  omega
theorem c3124 (pattern : Ten) (guard : d1 pattern = 1) : d8 pattern ≤ (2 : Int) + d7 pattern := by
  change (8 : Int) ≤ (2 : Int) + 7
  decide
theorem c3125 (pattern : Ten) (guard : d1 pattern = 1) : d312 pattern ≤ (2 : Int) + d194 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d312, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3077 pattern childGuard
    simpa only [d312, d194, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d312, d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3124 pattern childGuard
    simpa only [d312, d194, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3126 (pattern : Ten) (guard : d1 pattern = 1) : d316 pattern ≤ (2 : Int) + d194 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3123 pattern childGuard
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3125 pattern childGuard
    simpa only [d316, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3127 (pattern : Ten) (guard : d1 pattern = 1) : d319 pattern ≤ (2 : Int) + d198 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d319, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3126 pattern childGuard
    simpa only [d319, d198, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d319, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d319, d198, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3128 (pattern : Ten) (guard : d1 pattern = 1) : d322 pattern ≤ (2 : Int) + d203 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d322, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3127 pattern childGuard
    simpa only [d322, d203, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d322, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d322, d203, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3129 (pattern : Ten) (guard : d1 pattern = 1) : d324 pattern ≤ (2 : Int) + d207 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d324, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3122 pattern childGuard
    simpa only [d324, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d324, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3128 pattern childGuard
    simpa only [d324, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3130 (pattern : Ten) (guard : d0 pattern = 1) : d324 pattern ≤ (2 : Int) + d207 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3131 (pattern : Ten) (guard : d394 pattern = 1) : d324 pattern ≤ (2 : Int) + d207 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3129 pattern childGuard
    simpa only [d394, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3130 pattern childGuard
    simpa only [d394, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3132 (pattern : Ten) (guard : d0 pattern = 1) : d325 pattern ≤ (2 : Int) + d207 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3133 (pattern : Ten) (guard : d558 pattern = 1) : d327 pattern ≤ (2 : Int) + d207 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d558, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3131 pattern childGuard
    simpa only [d558, d327, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d558, d327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3132 pattern childGuard
    simpa only [d558, d327, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3134 (pattern : Ten) (guard : d559 pattern = 1) : d329 pattern ≤ (2 : Int) + d207 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d559, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3106 pattern childGuard
    simpa only [d559, d329, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d558 pattern = 1 := by simpa only [d559, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3133 pattern childGuard
    simpa only [d559, d329, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3135 (pattern : Ten) (guard : d0 pattern = 1) : d210 pattern ≤ (2 : Int) + d209 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3136 (pattern : Ten) (guard : d394 pattern = 1) : d210 pattern ≤ (2 : Int) + d209 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2438 pattern childGuard
    simpa only [d394, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3135 pattern childGuard
    simpa only [d394, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3137 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (2 : Int) + d209 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3138 (pattern : Ten) (guard : d558 pattern = 1) : d328 pattern ≤ (2 : Int) + d209 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d394 pattern = 1 := by simpa only [d558, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3136 pattern childGuard
    simpa only [d558, d328, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d558, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3137 pattern childGuard
    simpa only [d558, d328, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3139 (pattern : Ten) (guard : d559 pattern = 1) : d330 pattern ≤ (2 : Int) + d209 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d559, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2429 pattern childGuard
    simpa only [d559, d330, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d558 pattern = 1 := by simpa only [d559, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3138 pattern childGuard
    simpa only [d559, d330, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3140 (pattern : Ten) (guard : d559 pattern = 1) : d331 pattern ≤ (2 : Int) + d560 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d559 pattern = 1 := by simpa only [d331, d560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3134 pattern childGuard
    simpa only [d331, d560, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d559 pattern = 1 := by simpa only [d331, d560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3139 pattern childGuard
    simpa only [d331, d560, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3141 (pattern : Ten) (guard : d0 pattern = 1) : d54 pattern ≤ (9 : Int) + d207 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3142 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (9 : Int) + d0 pattern := by
  omega
theorem c3143 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (9 : Int) + d1 pattern := by
  change (0 : Int) ≤ (9 : Int) + 1
  decide
theorem c3144 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (9 : Int) + d171 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3142 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3143 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3145 (pattern : Ten) (guard : d0 pattern = 1) : d0 pattern ≤ (9 : Int) + d171 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3146 (pattern : Ten) (guard : d350 pattern = 1) : d0 pattern ≤ (9 : Int) + d171 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3144 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3145 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3147 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (9 : Int) + d2 pattern := by
  omega
theorem c3148 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (9 : Int) + d3 pattern := by
  change (2 : Int) ≤ (9 : Int) + 3
  decide
theorem c3149 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (9 : Int) + d172 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3147 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3148 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3150 (pattern : Ten) (guard : d0 pattern = 1) : d2 pattern ≤ (9 : Int) + d172 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3151 (pattern : Ten) (guard : d350 pattern = 1) : d2 pattern ≤ (9 : Int) + d172 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3149 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3150 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3152 (pattern : Ten) (guard : d350 pattern = 1) : d15 pattern ≤ (9 : Int) + d174 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3146 pattern childGuard
    simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3151 pattern childGuard
    simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3153 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (9 : Int) + d4 pattern := by
  omega
theorem c3154 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (9 : Int) + d5 pattern := by
  change (4 : Int) ≤ (9 : Int) + 5
  decide
theorem c3155 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (9 : Int) + d193 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3153 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3154 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3156 (pattern : Ten) (guard : d0 pattern = 1) : d4 pattern ≤ (9 : Int) + d193 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3157 (pattern : Ten) (guard : d350 pattern = 1) : d4 pattern ≤ (9 : Int) + d193 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3155 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3156 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3158 (pattern : Ten) (guard : d350 pattern = 1) : d10 pattern ≤ (9 : Int) + d10 pattern := by
  omega
theorem c3159 (pattern : Ten) (guard : d350 pattern = 1) : d42 pattern ≤ (9 : Int) + d197 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d42, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3157 pattern childGuard
    simpa only [d42, d197, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d42, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3158 pattern childGuard
    simpa only [d42, d197, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3160 (pattern : Ten) (guard : d350 pattern = 1) : d48 pattern ≤ (9 : Int) + d202 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d48, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3152 pattern childGuard
    simpa only [d48, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d48, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3159 pattern childGuard
    simpa only [d48, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3161 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (9 : Int) + d6 pattern := by
  omega
theorem c3162 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (9 : Int) + d7 pattern := by
  change (6 : Int) ≤ (9 : Int) + 7
  decide
theorem c3163 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (9 : Int) + d194 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3161 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3162 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3164 (pattern : Ten) (guard : d0 pattern = 1) : d6 pattern ≤ (9 : Int) + d194 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3165 (pattern : Ten) (guard : d350 pattern = 1) : d6 pattern ≤ (9 : Int) + d194 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3163 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3164 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3166 (pattern : Ten) (guard : d350 pattern = 1) : d43 pattern ≤ (9 : Int) + d198 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d43, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3165 pattern childGuard
    simpa only [d43, d198, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d43, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3158 pattern childGuard
    simpa only [d43, d198, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3167 (pattern : Ten) (guard : d350 pattern = 1) : d49 pattern ≤ (9 : Int) + d203 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d49, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3166 pattern childGuard
    simpa only [d49, d203, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d49, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3158 pattern childGuard
    simpa only [d49, d203, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3168 (pattern : Ten) (guard : d350 pattern = 1) : d54 pattern ≤ (9 : Int) + d207 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d54, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3160 pattern childGuard
    simpa only [d54, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d54, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3167 pattern childGuard
    simpa only [d54, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3169 (pattern : Ten) (guard : d1 pattern = 1) : d9 pattern ≤ (9 : Int) + d0 pattern := by
  change (9 : Int) ≤ (9 : Int) + 0
  decide
theorem c3170 (pattern : Ten) (guard : d1 pattern = 1) : d10 pattern ≤ (9 : Int) + d1 pattern := by
  change (10 : Int) ≤ (9 : Int) + 1
  decide
theorem c3171 (pattern : Ten) (guard : d1 pattern = 1) : d11 pattern ≤ (9 : Int) + d171 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3169 pattern childGuard
    simpa only [d11, d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3170 pattern childGuard
    simpa only [d11, d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3172 (pattern : Ten) (guard : d0 pattern = 1) : d11 pattern ≤ (9 : Int) + d171 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3173 (pattern : Ten) (guard : d350 pattern = 1) : d11 pattern ≤ (9 : Int) + d171 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3171 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3172 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3174 (pattern : Ten) (guard : d1 pattern = 1) : d10 pattern ≤ (9 : Int) + d2 pattern := by
  change (10 : Int) ≤ (9 : Int) + 2
  decide
theorem c3175 (pattern : Ten) (guard : d1 pattern = 1) : d10 pattern ≤ (9 : Int) + d3 pattern := by
  change (10 : Int) ≤ (9 : Int) + 3
  decide
theorem c3176 (pattern : Ten) (guard : d1 pattern = 1) : d10 pattern ≤ (9 : Int) + d172 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3174 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3175 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3177 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (9 : Int) + d172 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3178 (pattern : Ten) (guard : d350 pattern = 1) : d10 pattern ≤ (9 : Int) + d172 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3176 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3177 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3179 (pattern : Ten) (guard : d350 pattern = 1) : d14 pattern ≤ (9 : Int) + d174 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d14, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3173 pattern childGuard
    simpa only [d14, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d14, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3178 pattern childGuard
    simpa only [d14, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3180 (pattern : Ten) (guard : d1 pattern = 1) : d10 pattern ≤ (9 : Int) + d4 pattern := by
  change (10 : Int) ≤ (9 : Int) + 4
  decide
theorem c3181 (pattern : Ten) (guard : d1 pattern = 1) : d10 pattern ≤ (9 : Int) + d5 pattern := by
  change (10 : Int) ≤ (9 : Int) + 5
  decide
theorem c3182 (pattern : Ten) (guard : d1 pattern = 1) : d10 pattern ≤ (9 : Int) + d193 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3180 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3181 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3183 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (9 : Int) + d193 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3184 (pattern : Ten) (guard : d350 pattern = 1) : d10 pattern ≤ (9 : Int) + d193 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3182 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3183 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3185 (pattern : Ten) (guard : d350 pattern = 1) : d10 pattern ≤ (9 : Int) + d197 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3184 pattern childGuard
    simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3158 pattern childGuard
    simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3186 (pattern : Ten) (guard : d350 pattern = 1) : d20 pattern ≤ (9 : Int) + d202 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d20, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3179 pattern childGuard
    simpa only [d20, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d20, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3185 pattern childGuard
    simpa only [d20, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3187 (pattern : Ten) (guard : d1 pattern = 1) : d10 pattern ≤ (9 : Int) + d6 pattern := by
  change (10 : Int) ≤ (9 : Int) + 6
  decide
theorem c3188 (pattern : Ten) (guard : d1 pattern = 1) : d10 pattern ≤ (9 : Int) + d7 pattern := by
  change (10 : Int) ≤ (9 : Int) + 7
  decide
theorem c3189 (pattern : Ten) (guard : d1 pattern = 1) : d10 pattern ≤ (9 : Int) + d194 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3187 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3188 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3190 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (9 : Int) + d194 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c3191 (pattern : Ten) (guard : d350 pattern = 1) : d10 pattern ≤ (9 : Int) + d194 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3189 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3190 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3192 (pattern : Ten) (guard : d350 pattern = 1) : d10 pattern ≤ (9 : Int) + d198 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3191 pattern childGuard
    simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3158 pattern childGuard
    simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3193 (pattern : Ten) (guard : d350 pattern = 1) : d10 pattern ≤ (9 : Int) + d203 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3192 pattern childGuard
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3158 pattern childGuard
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3194 (pattern : Ten) (guard : d350 pattern = 1) : d27 pattern ≤ (9 : Int) + d207 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d27, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3186 pattern childGuard
    simpa only [d27, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d27, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3193 pattern childGuard
    simpa only [d27, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3195 (pattern : Ten) (guard : d350 pattern = 1) : d58 pattern ≤ (9 : Int) + d207 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3168 pattern childGuard
    simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3194 pattern childGuard
    simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3196 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (9 : Int) + d0 pattern := by
  change (2 : Int) ≤ (9 : Int) + 0
  decide
theorem c3197 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (9 : Int) + d1 pattern := by
  change (2 : Int) ≤ (9 : Int) + 1
  decide
theorem c3198 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (9 : Int) + d171 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3196 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3197 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c3199 (pattern : Ten) (guard : d0 pattern = 1) : d2 pattern ≤ (9 : Int) + d171 pattern := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban41.Diagram
