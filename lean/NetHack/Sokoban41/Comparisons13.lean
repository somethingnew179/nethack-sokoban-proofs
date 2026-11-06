/- Staged soko4-1 certificate. No result until all kernel checks pass. -/
import NetHack.Sokoban41.Comparisons12
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem c2080 (pattern : Ten) (guard : d1 pattern = 1) : d1 pattern ≤ (7 : Int) + d10 pattern := by
  change (1 : Int) ≤ (7 : Int) + 10
  decide
theorem c2081 (pattern : Ten) (guard : d1 pattern = 1) : d171 pattern ≤ (7 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2079 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2080 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2082 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (7 : Int) + d10 pattern := by
  change (2 : Int) ≤ (7 : Int) + 10
  decide
theorem c2083 (pattern : Ten) (guard : d1 pattern = 1) : d3 pattern ≤ (7 : Int) + d10 pattern := by
  change (3 : Int) ≤ (7 : Int) + 10
  decide
theorem c2084 (pattern : Ten) (guard : d1 pattern = 1) : d172 pattern ≤ (7 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2082 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2083 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2085 (pattern : Ten) (guard : d1 pattern = 1) : d174 pattern ≤ (7 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2081 pattern childGuard
    simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2084 pattern childGuard
    simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2086 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (7 : Int) + d10 pattern := by
  change (4 : Int) ≤ (7 : Int) + 10
  decide
theorem c2087 (pattern : Ten) (guard : d1 pattern = 1) : d5 pattern ≤ (7 : Int) + d10 pattern := by
  change (5 : Int) ≤ (7 : Int) + 10
  decide
theorem c2088 (pattern : Ten) (guard : d1 pattern = 1) : d193 pattern ≤ (7 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2086 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2087 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2089 (pattern : Ten) (guard : d1 pattern = 1) : d197 pattern ≤ (7 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2088 pattern childGuard
    simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2056 pattern childGuard
    simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2090 (pattern : Ten) (guard : d1 pattern = 1) : d202 pattern ≤ (7 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2085 pattern childGuard
    simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2089 pattern childGuard
    simpa only [d202, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2091 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (7 : Int) + d10 pattern := by
  change (6 : Int) ≤ (7 : Int) + 10
  decide
theorem c2092 (pattern : Ten) (guard : d1 pattern = 1) : d7 pattern ≤ (7 : Int) + d10 pattern := by
  change (7 : Int) ≤ (7 : Int) + 10
  decide
theorem c2093 (pattern : Ten) (guard : d1 pattern = 1) : d194 pattern ≤ (7 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2091 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2092 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2094 (pattern : Ten) (guard : d1 pattern = 1) : d198 pattern ≤ (7 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2093 pattern childGuard
    simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2056 pattern childGuard
    simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2095 (pattern : Ten) (guard : d1 pattern = 1) : d203 pattern ≤ (7 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2094 pattern childGuard
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2056 pattern childGuard
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2096 (pattern : Ten) (guard : d1 pattern = 1) : d207 pattern ≤ (7 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2090 pattern childGuard
    simpa only [d207, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2095 pattern childGuard
    simpa only [d207, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2097 (pattern : Ten) (guard : d1 pattern = 1) : d211 pattern ≤ (7 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2096 pattern childGuard
    simpa only [d211, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2056 pattern childGuard
    simpa only [d211, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2098 (pattern : Ten) (guard : d1 pattern = 1) : d199 pattern ≤ (7 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2084 pattern childGuard
    simpa only [d199, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2088 pattern childGuard
    simpa only [d199, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2099 (pattern : Ten) (guard : d1 pattern = 1) : d204 pattern ≤ (7 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2098 pattern childGuard
    simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2094 pattern childGuard
    simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2100 (pattern : Ten) (guard : d1 pattern = 1) : d8 pattern ≤ (7 : Int) + d10 pattern := by
  change (8 : Int) ≤ (7 : Int) + 10
  decide
theorem c2101 (pattern : Ten) (guard : d1 pattern = 1) : d195 pattern ≤ (7 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2100 pattern childGuard
    simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2055 pattern childGuard
    simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2102 (pattern : Ten) (guard : d1 pattern = 1) : d200 pattern ≤ (7 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2101 pattern childGuard
    simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2056 pattern childGuard
    simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2103 (pattern : Ten) (guard : d1 pattern = 1) : d205 pattern ≤ (7 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2102 pattern childGuard
    simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2056 pattern childGuard
    simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2104 (pattern : Ten) (guard : d1 pattern = 1) : d208 pattern ≤ (7 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2099 pattern childGuard
    simpa only [d208, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2103 pattern childGuard
    simpa only [d208, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2105 (pattern : Ten) (guard : d1 pattern = 1) : d212 pattern ≤ (7 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2104 pattern childGuard
    simpa only [d212, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2056 pattern childGuard
    simpa only [d212, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2106 (pattern : Ten) (guard : d1 pattern = 1) : d215 pattern ≤ (7 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2097 pattern childGuard
    simpa only [d215, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2105 pattern childGuard
    simpa only [d215, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2107 (pattern : Ten) (guard : d1 pattern = 1) : d218 pattern ≤ (7 : Int) + d10 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2096 pattern childGuard
    simpa only [d218, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2106 pattern childGuard
    simpa only [d218, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2108 (pattern : Ten) (guard : d0 pattern = 1) : d10 pattern ≤ (7 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2109 (pattern : Ten) (guard : d361 pattern = 1) : d289 pattern ≤ (7 : Int) + d10 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d361, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2107 pattern childGuard
    simpa only [d361, d289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d361, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2108 pattern childGuard
    simpa only [d361, d289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2110 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (0 : Int) + d7 pattern := by
  change (0 : Int) ≤ (0 : Int) + 7
  decide
theorem c2111 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (0 : Int) + d8 pattern := by
  change (0 : Int) ≤ (0 : Int) + 8
  decide
theorem c2112 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (0 : Int) + d38 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2110 pattern childGuard
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2111 pattern childGuard
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2113 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (0 : Int) + d40 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2112 pattern childGuard
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2111 pattern childGuard
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2114 (pattern : Ten) (guard : d0 pattern = 1) : d0 pattern ≤ (0 : Int) + d40 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2115 (pattern : Ten) (guard : d350 pattern = 1) : d0 pattern ≤ (0 : Int) + d40 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2113 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2114 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2116 (pattern : Ten) (guard : d350 pattern = 1) : d2 pattern ≤ (0 : Int) + d10 pattern := by
  change (2 : Int) ≤ (0 : Int) + 10
  decide
theorem c2117 (pattern : Ten) (guard : d350 pattern = 1) : d15 pattern ≤ (0 : Int) + d46 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2115 pattern childGuard
    simpa only [d15, d46, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2116 pattern childGuard
    simpa only [d15, d46, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2118 (pattern : Ten) (guard : d350 pattern = 1) : d4 pattern ≤ (0 : Int) + d10 pattern := by
  change (4 : Int) ≤ (0 : Int) + 10
  decide
theorem c2119 (pattern : Ten) (guard : d350 pattern = 1) : d42 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2118 pattern childGuard
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c322 pattern childGuard
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2120 (pattern : Ten) (guard : d350 pattern = 1) : d48 pattern ≤ (0 : Int) + d52 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d48, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2117 pattern childGuard
    simpa only [d48, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d48, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2119 pattern childGuard
    simpa only [d48, d52, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2121 (pattern : Ten) (guard : d350 pattern = 1) : d6 pattern ≤ (0 : Int) + d10 pattern := by
  change (6 : Int) ≤ (0 : Int) + 10
  decide
theorem c2122 (pattern : Ten) (guard : d350 pattern = 1) : d43 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2121 pattern childGuard
    simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c322 pattern childGuard
    simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2123 (pattern : Ten) (guard : d350 pattern = 1) : d49 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2122 pattern childGuard
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c322 pattern childGuard
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2124 (pattern : Ten) (guard : d350 pattern = 1) : d54 pattern ≤ (0 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d54, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2120 pattern childGuard
    simpa only [d54, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d54, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2123 pattern childGuard
    simpa only [d54, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2125 (pattern : Ten) (guard : d1 pattern = 1) : d9 pattern ≤ (0 : Int) + d10 pattern := by
  change (9 : Int) ≤ (0 : Int) + 10
  decide
theorem c2126 (pattern : Ten) (guard : d1 pattern = 1) : d10 pattern ≤ (0 : Int) + d10 pattern := by
  omega
theorem c2127 (pattern : Ten) (guard : d1 pattern = 1) : d11 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2125 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2126 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2128 (pattern : Ten) (guard : d350 pattern = 1) : d11 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2127 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c462 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2129 (pattern : Ten) (guard : d350 pattern = 1) : d14 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2128 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c322 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2130 (pattern : Ten) (guard : d350 pattern = 1) : d20 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2129 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c322 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2131 (pattern : Ten) (guard : d350 pattern = 1) : d27 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2130 pattern childGuard
    simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c322 pattern childGuard
    simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2132 (pattern : Ten) (guard : d350 pattern = 1) : d58 pattern ≤ (0 : Int) + d60 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d58, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2124 pattern childGuard
    simpa only [d58, d60, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d58, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2131 pattern childGuard
    simpa only [d58, d60, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2133 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (0 : Int) + d9 pattern := by
  change (2 : Int) ≤ (0 : Int) + 9
  decide
theorem c2134 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (0 : Int) + d10 pattern := by
  change (2 : Int) ≤ (0 : Int) + 10
  decide
theorem c2135 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (0 : Int) + d39 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2133 pattern childGuard
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2134 pattern childGuard
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2136 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (0 : Int) + d41 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2135 pattern childGuard
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2134 pattern childGuard
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2137 (pattern : Ten) (guard : d0 pattern = 1) : d2 pattern ≤ (0 : Int) + d41 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2138 (pattern : Ten) (guard : d350 pattern = 1) : d2 pattern ≤ (0 : Int) + d41 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2136 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2137 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2139 (pattern : Ten) (guard : d350 pattern = 1) : d44 pattern ≤ (0 : Int) + d47 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d44, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2138 pattern childGuard
    simpa only [d44, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d44, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2118 pattern childGuard
    simpa only [d44, d47, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2140 (pattern : Ten) (guard : d350 pattern = 1) : d50 pattern ≤ (0 : Int) + d53 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d50, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2139 pattern childGuard
    simpa only [d50, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d50, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2122 pattern childGuard
    simpa only [d50, d53, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2141 (pattern : Ten) (guard : d350 pattern = 1) : d8 pattern ≤ (0 : Int) + d10 pattern := by
  change (8 : Int) ≤ (0 : Int) + 10
  decide
theorem c2142 (pattern : Ten) (guard : d350 pattern = 1) : d45 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2141 pattern childGuard
    simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c322 pattern childGuard
    simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2143 (pattern : Ten) (guard : d350 pattern = 1) : d51 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2142 pattern childGuard
    simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c322 pattern childGuard
    simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2144 (pattern : Ten) (guard : d350 pattern = 1) : d55 pattern ≤ (0 : Int) + d57 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d55, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2140 pattern childGuard
    simpa only [d55, d57, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d55, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2143 pattern childGuard
    simpa only [d55, d57, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2145 (pattern : Ten) (guard : d350 pattern = 1) : d59 pattern ≤ (0 : Int) + d61 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d59, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2144 pattern childGuard
    simpa only [d59, d61, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d59, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2131 pattern childGuard
    simpa only [d59, d61, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2146 (pattern : Ten) (guard : d350 pattern = 1) : d62 pattern ≤ (0 : Int) + d63 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d62, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2132 pattern childGuard
    simpa only [d62, d63, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d62, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2145 pattern childGuard
    simpa only [d62, d63, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2147 (pattern : Ten) (guard : d350 pattern = 1) : d64 pattern ≤ (0 : Int) + d65 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d64, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2124 pattern childGuard
    simpa only [d64, d65, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d64, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2146 pattern childGuard
    simpa only [d64, d65, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2148 (pattern : Ten) (guard : d0 pattern = 1) : d65 pattern ≤ (0 : Int) + d65 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2149 (pattern : Ten) (guard : d362 pattern = 1) : d66 pattern ≤ (0 : Int) + d65 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d362, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2147 pattern childGuard
    simpa only [d362, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d362, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2148 pattern childGuard
    simpa only [d362, d66, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2150 (pattern : Ten) (guard : d1 pattern = 1) : d1 pattern ≤ (0 : Int) + d9 pattern := by
  change (1 : Int) ≤ (0 : Int) + 9
  decide
theorem c2151 (pattern : Ten) (guard : d1 pattern = 1) : d171 pattern ≤ (0 : Int) + d195 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2111 pattern childGuard
    simpa only [d171, d195, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2150 pattern childGuard
    simpa only [d171, d195, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2152 (pattern : Ten) (guard : d1 pattern = 1) : d3 pattern ≤ (0 : Int) + d10 pattern := by
  change (3 : Int) ≤ (0 : Int) + 10
  decide
theorem c2153 (pattern : Ten) (guard : d1 pattern = 1) : d172 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2134 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2152 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2154 (pattern : Ten) (guard : d1 pattern = 1) : d174 pattern ≤ (0 : Int) + d200 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d174, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2151 pattern childGuard
    simpa only [d174, d200, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d174, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2153 pattern childGuard
    simpa only [d174, d200, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2155 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (0 : Int) + d10 pattern := by
  change (4 : Int) ≤ (0 : Int) + 10
  decide
theorem c2156 (pattern : Ten) (guard : d1 pattern = 1) : d5 pattern ≤ (0 : Int) + d10 pattern := by
  change (5 : Int) ≤ (0 : Int) + 10
  decide
theorem c2157 (pattern : Ten) (guard : d1 pattern = 1) : d193 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2155 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2156 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2158 (pattern : Ten) (guard : d1 pattern = 1) : d197 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2157 pattern childGuard
    simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2126 pattern childGuard
    simpa only [d197, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2159 (pattern : Ten) (guard : d1 pattern = 1) : d202 pattern ≤ (0 : Int) + d205 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d202, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2154 pattern childGuard
    simpa only [d202, d205, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d202, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2158 pattern childGuard
    simpa only [d202, d205, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2160 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (0 : Int) + d10 pattern := by
  change (6 : Int) ≤ (0 : Int) + 10
  decide
theorem c2161 (pattern : Ten) (guard : d1 pattern = 1) : d7 pattern ≤ (0 : Int) + d10 pattern := by
  change (7 : Int) ≤ (0 : Int) + 10
  decide
theorem c2162 (pattern : Ten) (guard : d1 pattern = 1) : d194 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2160 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2161 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2163 (pattern : Ten) (guard : d1 pattern = 1) : d198 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2162 pattern childGuard
    simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2126 pattern childGuard
    simpa only [d198, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2164 (pattern : Ten) (guard : d1 pattern = 1) : d203 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2163 pattern childGuard
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2126 pattern childGuard
    simpa only [d203, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2165 (pattern : Ten) (guard : d1 pattern = 1) : d207 pattern ≤ (0 : Int) + d209 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d207, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2159 pattern childGuard
    simpa only [d207, d209, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d207, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2164 pattern childGuard
    simpa only [d207, d209, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2166 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (0 : Int) + d9 pattern := by
  change (0 : Int) ≤ (0 : Int) + 9
  decide
theorem c2167 (pattern : Ten) (guard : d1 pattern = 1) : d1 pattern ≤ (0 : Int) + d10 pattern := by
  change (1 : Int) ≤ (0 : Int) + 10
  decide
theorem c2168 (pattern : Ten) (guard : d1 pattern = 1) : d171 pattern ≤ (0 : Int) + d11 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2166 pattern childGuard
    simpa only [d171, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2167 pattern childGuard
    simpa only [d171, d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2169 (pattern : Ten) (guard : d1 pattern = 1) : d171 pattern ≤ (0 : Int) + d196 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2151 pattern childGuard
    simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2168 pattern childGuard
    simpa only [d196, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2170 (pattern : Ten) (guard : d1 pattern = 1) : d174 pattern ≤ (0 : Int) + d201 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d174, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2169 pattern childGuard
    simpa only [d174, d201, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d174, d201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2153 pattern childGuard
    simpa only [d174, d201, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2171 (pattern : Ten) (guard : d1 pattern = 1) : d202 pattern ≤ (0 : Int) + d206 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d202, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2170 pattern childGuard
    simpa only [d202, d206, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d202, d206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2158 pattern childGuard
    simpa only [d202, d206, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2172 (pattern : Ten) (guard : d1 pattern = 1) : d207 pattern ≤ (0 : Int) + d210 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d207, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2171 pattern childGuard
    simpa only [d207, d210, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d207, d210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2164 pattern childGuard
    simpa only [d207, d210, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2173 (pattern : Ten) (guard : d1 pattern = 1) : d207 pattern ≤ (0 : Int) + d213 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2165 pattern childGuard
    simpa only [d213, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2172 pattern childGuard
    simpa only [d213, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2174 (pattern : Ten) (guard : d1 pattern = 1) : d207 pattern ≤ (0 : Int) + d216 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2165 pattern childGuard
    simpa only [d216, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2173 pattern childGuard
    simpa only [d216, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2175 (pattern : Ten) (guard : d1 pattern = 1) : d211 pattern ≤ (0 : Int) + d214 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d211, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2165 pattern childGuard
    simpa only [d211, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d211, d214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2126 pattern childGuard
    simpa only [d211, d214, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2176 (pattern : Ten) (guard : d1 pattern = 1) : d199 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2153 pattern childGuard
    simpa only [d199, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2157 pattern childGuard
    simpa only [d199, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2177 (pattern : Ten) (guard : d1 pattern = 1) : d204 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2176 pattern childGuard
    simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2163 pattern childGuard
    simpa only [d204, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2178 (pattern : Ten) (guard : d1 pattern = 1) : d8 pattern ≤ (0 : Int) + d10 pattern := by
  change (8 : Int) ≤ (0 : Int) + 10
  decide
theorem c2179 (pattern : Ten) (guard : d1 pattern = 1) : d195 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2178 pattern childGuard
    simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2125 pattern childGuard
    simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2180 (pattern : Ten) (guard : d1 pattern = 1) : d200 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2179 pattern childGuard
    simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2126 pattern childGuard
    simpa only [d200, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2181 (pattern : Ten) (guard : d1 pattern = 1) : d205 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2180 pattern childGuard
    simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2126 pattern childGuard
    simpa only [d205, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2182 (pattern : Ten) (guard : d1 pattern = 1) : d208 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2177 pattern childGuard
    simpa only [d208, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2181 pattern childGuard
    simpa only [d208, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2183 (pattern : Ten) (guard : d1 pattern = 1) : d212 pattern ≤ (0 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2182 pattern childGuard
    simpa only [d212, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2126 pattern childGuard
    simpa only [d212, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2184 (pattern : Ten) (guard : d1 pattern = 1) : d215 pattern ≤ (0 : Int) + d217 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d215, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2175 pattern childGuard
    simpa only [d215, d217, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d215, d217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2183 pattern childGuard
    simpa only [d215, d217, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2185 (pattern : Ten) (guard : d1 pattern = 1) : d218 pattern ≤ (0 : Int) + d219 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d218, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2174 pattern childGuard
    simpa only [d218, d219, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d218, d219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2184 pattern childGuard
    simpa only [d218, d219, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2186 (pattern : Ten) (guard : d0 pattern = 1) : d219 pattern ≤ (0 : Int) + d219 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2187 (pattern : Ten) (guard : d361 pattern = 1) : d220 pattern ≤ (0 : Int) + d219 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d361, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2185 pattern childGuard
    simpa only [d361, d220, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d361, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2186 pattern childGuard
    simpa only [d361, d220, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2188 (pattern : Ten) (guard : d0 pattern = 1) : d54 pattern ≤ (8 : Int) + d207 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2189 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (8 : Int) + d0 pattern := by
  omega
theorem c2190 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (8 : Int) + d1 pattern := by
  change (0 : Int) ≤ (8 : Int) + 1
  decide
theorem c2191 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (8 : Int) + d171 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2189 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2190 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2192 (pattern : Ten) (guard : d0 pattern = 1) : d0 pattern ≤ (8 : Int) + d171 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2193 (pattern : Ten) (guard : d350 pattern = 1) : d0 pattern ≤ (8 : Int) + d171 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2191 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2192 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2194 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (8 : Int) + d2 pattern := by
  omega
theorem c2195 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (8 : Int) + d3 pattern := by
  change (2 : Int) ≤ (8 : Int) + 3
  decide
theorem c2196 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (8 : Int) + d172 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2194 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2195 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2197 (pattern : Ten) (guard : d0 pattern = 1) : d2 pattern ≤ (8 : Int) + d172 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2198 (pattern : Ten) (guard : d350 pattern = 1) : d2 pattern ≤ (8 : Int) + d172 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2196 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2197 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2199 (pattern : Ten) (guard : d350 pattern = 1) : d15 pattern ≤ (8 : Int) + d174 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2193 pattern childGuard
    simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2198 pattern childGuard
    simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2200 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (8 : Int) + d4 pattern := by
  omega
theorem c2201 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (8 : Int) + d5 pattern := by
  change (4 : Int) ≤ (8 : Int) + 5
  decide
theorem c2202 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (8 : Int) + d193 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2200 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2201 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2203 (pattern : Ten) (guard : d0 pattern = 1) : d4 pattern ≤ (8 : Int) + d193 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2204 (pattern : Ten) (guard : d350 pattern = 1) : d4 pattern ≤ (8 : Int) + d193 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2202 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2203 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2205 (pattern : Ten) (guard : d350 pattern = 1) : d10 pattern ≤ (8 : Int) + d10 pattern := by
  omega
theorem c2206 (pattern : Ten) (guard : d350 pattern = 1) : d42 pattern ≤ (8 : Int) + d197 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d42, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2204 pattern childGuard
    simpa only [d42, d197, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d42, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2205 pattern childGuard
    simpa only [d42, d197, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2207 (pattern : Ten) (guard : d350 pattern = 1) : d48 pattern ≤ (8 : Int) + d202 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d48, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2199 pattern childGuard
    simpa only [d48, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d48, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2206 pattern childGuard
    simpa only [d48, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2208 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (8 : Int) + d6 pattern := by
  omega
theorem c2209 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (8 : Int) + d7 pattern := by
  change (6 : Int) ≤ (8 : Int) + 7
  decide
theorem c2210 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (8 : Int) + d194 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2208 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2209 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2211 (pattern : Ten) (guard : d0 pattern = 1) : d6 pattern ≤ (8 : Int) + d194 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2212 (pattern : Ten) (guard : d350 pattern = 1) : d6 pattern ≤ (8 : Int) + d194 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2210 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2211 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2213 (pattern : Ten) (guard : d350 pattern = 1) : d43 pattern ≤ (8 : Int) + d198 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d43, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2212 pattern childGuard
    simpa only [d43, d198, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d43, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2205 pattern childGuard
    simpa only [d43, d198, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2214 (pattern : Ten) (guard : d350 pattern = 1) : d49 pattern ≤ (8 : Int) + d203 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d49, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2213 pattern childGuard
    simpa only [d49, d203, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d49, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2205 pattern childGuard
    simpa only [d49, d203, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2215 (pattern : Ten) (guard : d350 pattern = 1) : d54 pattern ≤ (8 : Int) + d207 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d54, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2207 pattern childGuard
    simpa only [d54, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d54, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2214 pattern childGuard
    simpa only [d54, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2216 (pattern : Ten) (guard : d432 pattern = 1) : d54 pattern ≤ (8 : Int) + d207 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2188 pattern childGuard
    simpa only [d432, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2215 pattern childGuard
    simpa only [d432, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2217 (pattern : Ten) (guard : d0 pattern = 1) : d8 pattern ≤ (8 : Int) + d211 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2218 (pattern : Ten) (guard : d433 pattern = 1) : d134 pattern ≤ (8 : Int) + d434 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d432 pattern = 1 := by simpa only [d433, d134, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2216 pattern childGuard
    simpa only [d433, d134, d434, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d433, d134, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2217 pattern childGuard
    simpa only [d433, d134, d434, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2219 (pattern : Ten) (guard : d0 pattern = 1) : d56 pattern ≤ (8 : Int) + d209 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2220 (pattern : Ten) (guard : d1 pattern = 1) : d7 pattern ≤ (8 : Int) + d8 pattern := by
  change (7 : Int) ≤ (8 : Int) + 8
  decide
theorem c2221 (pattern : Ten) (guard : d1 pattern = 1) : d8 pattern ≤ (8 : Int) + d8 pattern := by
  omega
theorem c2222 (pattern : Ten) (guard : d1 pattern = 1) : d38 pattern ≤ (8 : Int) + d8 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2220 pattern childGuard
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2221 pattern childGuard
    simpa only [d38, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2223 (pattern : Ten) (guard : d1 pattern = 1) : d8 pattern ≤ (8 : Int) + d9 pattern := by
  change (8 : Int) ≤ (8 : Int) + 9
  decide
theorem c2224 (pattern : Ten) (guard : d1 pattern = 1) : d40 pattern ≤ (8 : Int) + d195 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2222 pattern childGuard
    simpa only [d40, d195, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d40, d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2223 pattern childGuard
    simpa only [d40, d195, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2225 (pattern : Ten) (guard : d0 pattern = 1) : d40 pattern ≤ (8 : Int) + d195 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2226 (pattern : Ten) (guard : d350 pattern = 1) : d40 pattern ≤ (8 : Int) + d195 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2224 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2225 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2227 (pattern : Ten) (guard : d350 pattern = 1) : d46 pattern ≤ (8 : Int) + d200 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d46, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2226 pattern childGuard
    simpa only [d46, d200, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d46, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2205 pattern childGuard
    simpa only [d46, d200, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2228 (pattern : Ten) (guard : d350 pattern = 1) : d52 pattern ≤ (8 : Int) + d205 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d52, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2227 pattern childGuard
    simpa only [d52, d205, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d52, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2205 pattern childGuard
    simpa only [d52, d205, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2229 (pattern : Ten) (guard : d350 pattern = 1) : d56 pattern ≤ (8 : Int) + d209 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d56, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2228 pattern childGuard
    simpa only [d56, d209, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d56, d209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2205 pattern childGuard
    simpa only [d56, d209, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2230 (pattern : Ten) (guard : d432 pattern = 1) : d56 pattern ≤ (8 : Int) + d209 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2219 pattern childGuard
    simpa only [d432, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2229 pattern childGuard
    simpa only [d432, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2231 (pattern : Ten) (guard : d0 pattern = 1) : d56 pattern ≤ (8 : Int) + d214 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2232 (pattern : Ten) (guard : d433 pattern = 1) : d56 pattern ≤ (8 : Int) + d237 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d432 pattern = 1 := by simpa only [d433, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2230 pattern childGuard
    simpa only [d433, d237, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d433, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2231 pattern childGuard
    simpa only [d433, d237, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2233 (pattern : Ten) (guard : d433 pattern = 1) : d135 pattern ≤ (8 : Int) + d435 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d433 pattern = 1 := by simpa only [d135, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2218 pattern childGuard
    simpa only [d135, d435, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d433 pattern = 1 := by simpa only [d135, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2232 pattern childGuard
    simpa only [d135, d435, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2234 (pattern : Ten) (guard : d0 pattern = 1) : d207 pattern ≤ (8 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2235 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (8 : Int) + d10 pattern := by
  change (0 : Int) ≤ (8 : Int) + 10
  decide
theorem c2236 (pattern : Ten) (guard : d1 pattern = 1) : d1 pattern ≤ (8 : Int) + d10 pattern := by
  change (1 : Int) ≤ (8 : Int) + 10
  decide
theorem c2237 (pattern : Ten) (guard : d1 pattern = 1) : d171 pattern ≤ (8 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2235 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2236 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2238 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (8 : Int) + d10 pattern := by
  change (2 : Int) ≤ (8 : Int) + 10
  decide
theorem c2239 (pattern : Ten) (guard : d1 pattern = 1) : d3 pattern ≤ (8 : Int) + d10 pattern := by
  change (3 : Int) ≤ (8 : Int) + 10
  decide
end NetHack.Sokoban41.Diagram
