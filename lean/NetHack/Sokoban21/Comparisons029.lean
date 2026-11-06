/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons028
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c4060 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d932 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4061 (pattern : Twelve) (guard : d1842 pattern = 1) : d1013 pattern ≤ (0 : Int) + d935 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1842, d1013, d935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c43 pattern childGuard
    simpa only [d1842, d1013, d935, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1842, d1013, d935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4060 pattern childGuard
    simpa only [d1842, d1013, d935, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4062 (pattern : Twelve) (guard : d1842 pattern = 1) : d1015 pattern ≤ (0 : Int) + d937 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1842 pattern = 1 := by simpa only [d1015, d937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4061 pattern childGuard
    simpa only [d1015, d937, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1842 pattern = 1 := by simpa only [d1015, d937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4058 pattern childGuard
    simpa only [d1015, d937, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4063 (pattern : Twelve) (guard : d1842 pattern = 1) : d1016 pattern ≤ (0 : Int) + d938 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1842 pattern = 1 := by simpa only [d1016, d938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4059 pattern childGuard
    simpa only [d1016, d938, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1842 pattern = 1 := by simpa only [d1016, d938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4062 pattern childGuard
    simpa only [d1016, d938, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4064 (pattern : Twelve) (guard : d1842 pattern = 1) : d1017 pattern ≤ (0 : Int) + d939 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1842 pattern = 1 := by simpa only [d1017, d939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4063 pattern childGuard
    simpa only [d1017, d939, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1842 pattern = 1 := by simpa only [d1017, d939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4062 pattern childGuard
    simpa only [d1017, d939, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4065 (pattern : Twelve) (guard : d0 pattern = 1) : d1363 pattern ≤ (0 : Int) + d1369 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4066 (pattern : Twelve) (guard : d1842 pattern = 1) : d1428 pattern ≤ (0 : Int) + d1373 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1842, d1428, d1373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c52 pattern childGuard
    simpa only [d1842, d1428, d1373, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1842, d1428, d1373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4065 pattern childGuard
    simpa only [d1842, d1428, d1373, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4067 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1371 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4068 (pattern : Twelve) (guard : d1842 pattern = 1) : d1429 pattern ≤ (0 : Int) + d1374 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1842, d1429, d1374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c59 pattern childGuard
    simpa only [d1842, d1429, d1374, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1842, d1429, d1374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4067 pattern childGuard
    simpa only [d1842, d1429, d1374, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4069 (pattern : Twelve) (guard : d1842 pattern = 1) : d1431 pattern ≤ (0 : Int) + d1376 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1842 pattern = 1 := by simpa only [d1431, d1376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4066 pattern childGuard
    simpa only [d1431, d1376, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1842 pattern = 1 := by simpa only [d1431, d1376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4068 pattern childGuard
    simpa only [d1431, d1376, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4070 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1369 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4071 (pattern : Twelve) (guard : d1842 pattern = 1) : d1430 pattern ≤ (0 : Int) + d1375 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1842, d1430, d1375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c66 pattern childGuard
    simpa only [d1842, d1430, d1375, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1842, d1430, d1375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4070 pattern childGuard
    simpa only [d1842, d1430, d1375, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4072 (pattern : Twelve) (guard : d1842 pattern = 1) : d1432 pattern ≤ (0 : Int) + d1377 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1842 pattern = 1 := by simpa only [d1432, d1377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4071 pattern childGuard
    simpa only [d1432, d1377, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1842 pattern = 1 := by simpa only [d1432, d1377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4068 pattern childGuard
    simpa only [d1432, d1377, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4073 (pattern : Twelve) (guard : d1842 pattern = 1) : d1433 pattern ≤ (0 : Int) + d1378 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1842 pattern = 1 := by simpa only [d1433, d1378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4069 pattern childGuard
    simpa only [d1433, d1378, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1842 pattern = 1 := by simpa only [d1433, d1378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4072 pattern childGuard
    simpa only [d1433, d1378, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4074 (pattern : Twelve) (guard : d1842 pattern = 1) : d1434 pattern ≤ (0 : Int) + d1379 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1842 pattern = 1 := by simpa only [d1434, d1379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4073 pattern childGuard
    simpa only [d1434, d1379, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1842 pattern = 1 := by simpa only [d1434, d1379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4072 pattern childGuard
    simpa only [d1434, d1379, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4075 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1687 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4076 (pattern : Twelve) (guard : d1842 pattern = 1) : d1714 pattern ≤ (0 : Int) + d1688 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1835 pattern = 1 := by simpa only [d1842, d1714, d1688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c73 pattern childGuard
    simpa only [d1842, d1714, d1688, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1842, d1714, d1688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4075 pattern childGuard
    simpa only [d1842, d1714, d1688, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4077 (pattern : Twelve) (guard : d1 pattern = 1) : d93 pattern ≤ (0 : Int) + d93 pattern := by
  omega
theorem c4078 (pattern : Twelve) (guard : d0 pattern = 1) : d94 pattern ≤ (0 : Int) + d209 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4079 (pattern : Twelve) (guard : d1844 pattern = 1) : d103 pattern ≤ (0 : Int) + d353 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1844, d103, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4077 pattern childGuard
    simpa only [d1844, d103, d353, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1844, d103, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4078 pattern childGuard
    simpa only [d1844, d103, d353, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4080 (pattern : Twelve) (guard : d1844 pattern = 1) : d110 pattern ≤ (0 : Int) + d358 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d110, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c734 pattern childGuard
    simpa only [d110, d358, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1844 pattern = 1 := by simpa only [d110, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4079 pattern childGuard
    simpa only [d110, d358, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4081 (pattern : Twelve) (guard : d0 pattern = 1) : d217 pattern ≤ (0 : Int) + d359 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4082 (pattern : Twelve) (guard : d1868 pattern = 1) : d345 pattern ≤ (0 : Int) + d361 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1868, d345, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4080 pattern childGuard
    simpa only [d1868, d345, d361, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1868, d345, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4081 pattern childGuard
    simpa only [d1868, d345, d361, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4083 (pattern : Twelve) (guard : d0 pattern = 1) : d99 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4084 (pattern : Twelve) (guard : d1844 pattern = 1) : d107 pattern ≤ (0 : Int) + d356 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1844, d107, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c739 pattern childGuard
    simpa only [d1844, d107, d356, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1844, d107, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4083 pattern childGuard
    simpa only [d1844, d107, d356, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4085 (pattern : Twelve) (guard : d1844 pattern = 1) : d112 pattern ≤ (0 : Int) + d356 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c741 pattern childGuard
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1844 pattern = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4084 pattern childGuard
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4086 (pattern : Twelve) (guard : d1868 pattern = 1) : d346 pattern ≤ (0 : Int) + d356 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1868, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4085 pattern childGuard
    simpa only [d1868, d346, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1868, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c742 pattern childGuard
    simpa only [d1868, d346, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4087 (pattern : Twelve) (guard : d1868 pattern = 1) : d348 pattern ≤ (0 : Int) + d362 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d348, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4082 pattern childGuard
    simpa only [d348, d362, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d348, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4086 pattern childGuard
    simpa only [d348, d362, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4088 (pattern : Twelve) (guard : d0 pattern = 1) : d94 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4089 (pattern : Twelve) (guard : d1844 pattern = 1) : d103 pattern ≤ (0 : Int) + d355 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1844, d103, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4077 pattern childGuard
    simpa only [d1844, d103, d355, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1844, d103, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4088 pattern childGuard
    simpa only [d1844, d103, d355, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4090 (pattern : Twelve) (guard : d1844 pattern = 1) : d110 pattern ≤ (0 : Int) + d360 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d110, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c748 pattern childGuard
    simpa only [d110, d360, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1844 pattern = 1 := by simpa only [d110, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4089 pattern childGuard
    simpa only [d110, d360, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4091 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d360 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4092 (pattern : Twelve) (guard : d1868 pattern = 1) : d347 pattern ≤ (0 : Int) + d360 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1868, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4090 pattern childGuard
    simpa only [d1868, d347, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1868, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4091 pattern childGuard
    simpa only [d1868, d347, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4093 (pattern : Twelve) (guard : d1868 pattern = 1) : d349 pattern ≤ (0 : Int) + d363 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d349, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4092 pattern childGuard
    simpa only [d349, d363, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d349, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4086 pattern childGuard
    simpa only [d349, d363, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4094 (pattern : Twelve) (guard : d1868 pattern = 1) : d350 pattern ≤ (0 : Int) + d364 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d350, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4087 pattern childGuard
    simpa only [d350, d364, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d350, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4093 pattern childGuard
    simpa only [d350, d364, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4095 (pattern : Twelve) (guard : d1868 pattern = 1) : d351 pattern ≤ (0 : Int) + d365 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d351, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4094 pattern childGuard
    simpa only [d351, d365, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d351, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4093 pattern childGuard
    simpa only [d351, d365, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4096 (pattern : Twelve) (guard : d0 pattern = 1) : d854 pattern ≤ (0 : Int) + d914 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4097 (pattern : Twelve) (guard : d1844 pattern = 1) : d861 pattern ≤ (0 : Int) + d1019 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1844, d861, d1019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c756 pattern childGuard
    simpa only [d1844, d861, d1019, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1844, d861, d1019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4096 pattern childGuard
    simpa only [d1844, d861, d1019, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4098 (pattern : Twelve) (guard : d1844 pattern = 1) : d861 pattern ≤ (0 : Int) + d1023 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c758 pattern childGuard
    simpa only [d1023, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4097 pattern childGuard
    simpa only [d1023, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4099 (pattern : Twelve) (guard : d0 pattern = 1) : d922 pattern ≤ (0 : Int) + d1024 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4100 (pattern : Twelve) (guard : d1868 pattern = 1) : d1011 pattern ≤ (0 : Int) + d1025 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1868, d1011, d1025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4098 pattern childGuard
    simpa only [d1868, d1011, d1025, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1868, d1011, d1025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4099 pattern childGuard
    simpa only [d1868, d1011, d1025, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4101 (pattern : Twelve) (guard : d1868 pattern = 1) : d1012 pattern ≤ (0 : Int) + d1022 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1868, d1012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c765 pattern childGuard
    simpa only [d1868, d1012, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1868, d1012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c766 pattern childGuard
    simpa only [d1868, d1012, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4102 (pattern : Twelve) (guard : d1868 pattern = 1) : d1014 pattern ≤ (0 : Int) + d1026 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1014, d1026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4100 pattern childGuard
    simpa only [d1014, d1026, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1014, d1026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4101 pattern childGuard
    simpa only [d1014, d1026, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4103 (pattern : Twelve) (guard : d1868 pattern = 1) : d1013 pattern ≤ (0 : Int) + d1021 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1868, d1013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c772 pattern childGuard
    simpa only [d1868, d1013, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1868, d1013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c773 pattern childGuard
    simpa only [d1868, d1013, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4104 (pattern : Twelve) (guard : d1868 pattern = 1) : d1015 pattern ≤ (0 : Int) + d1027 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1015, d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4103 pattern childGuard
    simpa only [d1015, d1027, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1015, d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4101 pattern childGuard
    simpa only [d1015, d1027, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4105 (pattern : Twelve) (guard : d1868 pattern = 1) : d1016 pattern ≤ (0 : Int) + d1028 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1016, d1028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4102 pattern childGuard
    simpa only [d1016, d1028, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1016, d1028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4104 pattern childGuard
    simpa only [d1016, d1028, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4106 (pattern : Twelve) (guard : d1868 pattern = 1) : d1017 pattern ≤ (0 : Int) + d1029 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1017, d1029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4105 pattern childGuard
    simpa only [d1017, d1029, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1017, d1029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4104 pattern childGuard
    simpa only [d1017, d1029, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4107 (pattern : Twelve) (guard : d1844 pattern = 1) : d1313 pattern ≤ (0 : Int) + d1438 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c782 pattern childGuard
    simpa only [d1438, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c796 pattern childGuard
    simpa only [d1438, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4108 (pattern : Twelve) (guard : d0 pattern = 1) : d1363 pattern ≤ (0 : Int) + d1436 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4109 (pattern : Twelve) (guard : d1868 pattern = 1) : d1428 pattern ≤ (0 : Int) + d1439 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1868, d1428, d1439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4107 pattern childGuard
    simpa only [d1868, d1428, d1439, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1868, d1428, d1439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4108 pattern childGuard
    simpa only [d1868, d1428, d1439, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4110 (pattern : Twelve) (guard : d1868 pattern = 1) : d1429 pattern ≤ (0 : Int) + d1437 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1868, d1429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c789 pattern childGuard
    simpa only [d1868, d1429, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1868, d1429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c790 pattern childGuard
    simpa only [d1868, d1429, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4111 (pattern : Twelve) (guard : d1868 pattern = 1) : d1431 pattern ≤ (0 : Int) + d1440 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1431, d1440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4109 pattern childGuard
    simpa only [d1431, d1440, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1431, d1440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4110 pattern childGuard
    simpa only [d1431, d1440, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4112 (pattern : Twelve) (guard : d1868 pattern = 1) : d1430 pattern ≤ (0 : Int) + d1436 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1868, d1430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c796 pattern childGuard
    simpa only [d1868, d1430, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1868, d1430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c797 pattern childGuard
    simpa only [d1868, d1430, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4113 (pattern : Twelve) (guard : d1868 pattern = 1) : d1432 pattern ≤ (0 : Int) + d1441 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1432, d1441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4112 pattern childGuard
    simpa only [d1432, d1441, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1432, d1441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4110 pattern childGuard
    simpa only [d1432, d1441, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4114 (pattern : Twelve) (guard : d1868 pattern = 1) : d1433 pattern ≤ (0 : Int) + d1442 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1433, d1442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4111 pattern childGuard
    simpa only [d1433, d1442, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1433, d1442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4113 pattern childGuard
    simpa only [d1433, d1442, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4115 (pattern : Twelve) (guard : d1868 pattern = 1) : d1434 pattern ≤ (0 : Int) + d1443 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1434, d1443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4114 pattern childGuard
    simpa only [d1434, d1443, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1434, d1443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4113 pattern childGuard
    simpa only [d1434, d1443, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4116 (pattern : Twelve) (guard : d1868 pattern = 1) : d1714 pattern ≤ (0 : Int) + d1715 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1868, d1714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c805 pattern childGuard
    simpa only [d1868, d1714, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1868, d1714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c806 pattern childGuard
    simpa only [d1868, d1714, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4117 (pattern : Twelve) (guard : d0 pattern = 1) : d217 pattern ≤ (0 : Int) + d111 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4118 (pattern : Twelve) (guard : d1841 pattern = 1) : d345 pattern ≤ (0 : Int) + d114 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1841, d345, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c606 pattern childGuard
    simpa only [d1841, d345, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1841, d345, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4117 pattern childGuard
    simpa only [d1841, d345, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4119 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d113 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4120 (pattern : Twelve) (guard : d1841 pattern = 1) : d346 pattern ≤ (0 : Int) + d115 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1841, d346, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c609 pattern childGuard
    simpa only [d1841, d346, d115, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1841, d346, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4119 pattern childGuard
    simpa only [d1841, d346, d115, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4121 (pattern : Twelve) (guard : d1841 pattern = 1) : d348 pattern ≤ (0 : Int) + d116 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1841 pattern = 1 := by simpa only [d348, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4118 pattern childGuard
    simpa only [d348, d116, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1841 pattern = 1 := by simpa only [d348, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4120 pattern childGuard
    simpa only [d348, d116, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4122 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d111 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4123 (pattern : Twelve) (guard : d1841 pattern = 1) : d347 pattern ≤ (0 : Int) + d114 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1841, d347, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c606 pattern childGuard
    simpa only [d1841, d347, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1841, d347, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4122 pattern childGuard
    simpa only [d1841, d347, d114, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4124 (pattern : Twelve) (guard : d1841 pattern = 1) : d349 pattern ≤ (0 : Int) + d116 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1841 pattern = 1 := by simpa only [d349, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4123 pattern childGuard
    simpa only [d349, d116, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1841 pattern = 1 := by simpa only [d349, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4120 pattern childGuard
    simpa only [d349, d116, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4125 (pattern : Twelve) (guard : d1841 pattern = 1) : d350 pattern ≤ (0 : Int) + d116 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1841 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4121 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1841 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4124 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4126 (pattern : Twelve) (guard : d1841 pattern = 1) : d351 pattern ≤ (0 : Int) + d116 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1841 pattern = 1 := by simpa only [d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4125 pattern childGuard
    simpa only [d351, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1841 pattern = 1 := by simpa only [d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4124 pattern childGuard
    simpa only [d351, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4127 (pattern : Twelve) (guard : d0 pattern = 1) : d922 pattern ≤ (0 : Int) + d867 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4128 (pattern : Twelve) (guard : d1841 pattern = 1) : d1011 pattern ≤ (0 : Int) + d869 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1841, d1011, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c27 pattern childGuard
    simpa only [d1841, d1011, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1841, d1011, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4127 pattern childGuard
    simpa only [d1841, d1011, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4129 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d868 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4130 (pattern : Twelve) (guard : d1841 pattern = 1) : d1012 pattern ≤ (0 : Int) + d870 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1841, d1012, d870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c34 pattern childGuard
    simpa only [d1841, d1012, d870, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1841, d1012, d870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4129 pattern childGuard
    simpa only [d1841, d1012, d870, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4131 (pattern : Twelve) (guard : d1841 pattern = 1) : d1014 pattern ≤ (0 : Int) + d871 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1841 pattern = 1 := by simpa only [d1014, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4128 pattern childGuard
    simpa only [d1014, d871, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1841 pattern = 1 := by simpa only [d1014, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4130 pattern childGuard
    simpa only [d1014, d871, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4132 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d867 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4133 (pattern : Twelve) (guard : d1841 pattern = 1) : d1013 pattern ≤ (0 : Int) + d869 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1841, d1013, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c27 pattern childGuard
    simpa only [d1841, d1013, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1841, d1013, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4132 pattern childGuard
    simpa only [d1841, d1013, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4134 (pattern : Twelve) (guard : d1841 pattern = 1) : d1015 pattern ≤ (0 : Int) + d871 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1841 pattern = 1 := by simpa only [d1015, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4133 pattern childGuard
    simpa only [d1015, d871, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1841 pattern = 1 := by simpa only [d1015, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4130 pattern childGuard
    simpa only [d1015, d871, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4135 (pattern : Twelve) (guard : d1841 pattern = 1) : d1016 pattern ≤ (0 : Int) + d871 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1841 pattern = 1 := by simpa only [d1016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4131 pattern childGuard
    simpa only [d1016, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1841 pattern = 1 := by simpa only [d1016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4134 pattern childGuard
    simpa only [d1016, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4136 (pattern : Twelve) (guard : d1841 pattern = 1) : d1017 pattern ≤ (0 : Int) + d871 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1841 pattern = 1 := by simpa only [d1017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4135 pattern childGuard
    simpa only [d1017, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1841 pattern = 1 := by simpa only [d1017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4134 pattern childGuard
    simpa only [d1017, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4137 (pattern : Twelve) (guard : d0 pattern = 1) : d1363 pattern ≤ (0 : Int) + d1319 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4138 (pattern : Twelve) (guard : d1841 pattern = 1) : d1428 pattern ≤ (0 : Int) + d1321 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1841, d1428, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c50 pattern childGuard
    simpa only [d1841, d1428, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1841, d1428, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4137 pattern childGuard
    simpa only [d1841, d1428, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4139 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1320 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4140 (pattern : Twelve) (guard : d1841 pattern = 1) : d1429 pattern ≤ (0 : Int) + d1322 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1841, d1429, d1322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c57 pattern childGuard
    simpa only [d1841, d1429, d1322, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1841, d1429, d1322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4139 pattern childGuard
    simpa only [d1841, d1429, d1322, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4141 (pattern : Twelve) (guard : d1841 pattern = 1) : d1431 pattern ≤ (0 : Int) + d1323 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1841 pattern = 1 := by simpa only [d1431, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4138 pattern childGuard
    simpa only [d1431, d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1841 pattern = 1 := by simpa only [d1431, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4140 pattern childGuard
    simpa only [d1431, d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4142 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1319 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4143 (pattern : Twelve) (guard : d1841 pattern = 1) : d1430 pattern ≤ (0 : Int) + d1321 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1841, d1430, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c50 pattern childGuard
    simpa only [d1841, d1430, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1841, d1430, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4142 pattern childGuard
    simpa only [d1841, d1430, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4144 (pattern : Twelve) (guard : d1841 pattern = 1) : d1432 pattern ≤ (0 : Int) + d1323 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1841 pattern = 1 := by simpa only [d1432, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4143 pattern childGuard
    simpa only [d1432, d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1841 pattern = 1 := by simpa only [d1432, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4140 pattern childGuard
    simpa only [d1432, d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4145 (pattern : Twelve) (guard : d1841 pattern = 1) : d1433 pattern ≤ (0 : Int) + d1323 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1841 pattern = 1 := by simpa only [d1433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4141 pattern childGuard
    simpa only [d1433, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1841 pattern = 1 := by simpa only [d1433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4144 pattern childGuard
    simpa only [d1433, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4146 (pattern : Twelve) (guard : d1841 pattern = 1) : d1434 pattern ≤ (0 : Int) + d1323 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1841 pattern = 1 := by simpa only [d1434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4145 pattern childGuard
    simpa only [d1434, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1841 pattern = 1 := by simpa only [d1434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4144 pattern childGuard
    simpa only [d1434, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4147 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1663 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4148 (pattern : Twelve) (guard : d1841 pattern = 1) : d1714 pattern ≤ (0 : Int) + d1664 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1841, d1714, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c71 pattern childGuard
    simpa only [d1841, d1714, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1841, d1714, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4147 pattern childGuard
    simpa only [d1841, d1714, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4149 (pattern : Twelve) (guard : d1848 pattern = 1) : d50 pattern ≤ (0 : Int) + d372 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d50, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1267 pattern childGuard
    simpa only [d50, d372, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d50, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1397 pattern childGuard
    simpa only [d50, d372, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4150 (pattern : Twelve) (guard : d1848 pattern = 1) : d72 pattern ≤ (0 : Int) + d389 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d72, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2546 pattern childGuard
    simpa only [d72, d389, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d72, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4149 pattern childGuard
    simpa only [d72, d389, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4151 (pattern : Twelve) (guard : d1848 pattern = 1) : d51 pattern ≤ (0 : Int) + d374 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d51, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1276 pattern childGuard
    simpa only [d51, d374, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d51, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2795 pattern childGuard
    simpa only [d51, d374, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4152 (pattern : Twelve) (guard : d1848 pattern = 1) : d73 pattern ≤ (0 : Int) + d390 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d73, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2664 pattern childGuard
    simpa only [d73, d390, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d73, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4151 pattern childGuard
    simpa only [d73, d390, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4153 (pattern : Twelve) (guard : d1848 pattern = 1) : d91 pattern ≤ (0 : Int) + d402 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d91, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4150 pattern childGuard
    simpa only [d91, d402, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d91, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4152 pattern childGuard
    simpa only [d91, d402, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4154 (pattern : Twelve) (guard : d0 pattern = 1) : d208 pattern ≤ (0 : Int) + d403 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4155 (pattern : Twelve) (guard : d1869 pattern = 1) : d352 pattern ≤ (0 : Int) + d409 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d352, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4153 pattern childGuard
    simpa only [d1869, d352, d409, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d352, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4154 pattern childGuard
    simpa only [d1869, d352, d409, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4156 (pattern : Twelve) (guard : d1848 pattern = 1) : d50 pattern ≤ (0 : Int) + d376 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d50, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1300 pattern childGuard
    simpa only [d50, d376, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d50, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1415 pattern childGuard
    simpa only [d50, d376, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4157 (pattern : Twelve) (guard : d1848 pattern = 1) : d72 pattern ≤ (0 : Int) + d391 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d72, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2561 pattern childGuard
    simpa only [d72, d391, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d72, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4156 pattern childGuard
    simpa only [d72, d391, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4158 (pattern : Twelve) (guard : d1848 pattern = 1) : d55 pattern ≤ (0 : Int) + d378 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d55, d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1291 pattern childGuard
    simpa only [d55, d378, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d55, d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2795 pattern childGuard
    simpa only [d55, d378, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4159 (pattern : Twelve) (guard : d1848 pattern = 1) : d76 pattern ≤ (0 : Int) + d392 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d76, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2677 pattern childGuard
    simpa only [d76, d392, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d76, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4158 pattern childGuard
    simpa only [d76, d392, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4160 (pattern : Twelve) (guard : d1848 pattern = 1) : d93 pattern ≤ (0 : Int) + d403 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d93, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4157 pattern childGuard
    simpa only [d93, d403, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d93, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4159 pattern childGuard
    simpa only [d93, d403, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4161 (pattern : Twelve) (guard : d0 pattern = 1) : d209 pattern ≤ (0 : Int) + d404 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4162 (pattern : Twelve) (guard : d1869 pattern = 1) : d353 pattern ≤ (0 : Int) + d410 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d353, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4160 pattern childGuard
    simpa only [d1869, d353, d410, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d353, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4161 pattern childGuard
    simpa only [d1869, d353, d410, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4163 (pattern : Twelve) (guard : d1869 pattern = 1) : d358 pattern ≤ (0 : Int) + d415 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d358, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4155 pattern childGuard
    simpa only [d358, d415, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d358, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4162 pattern childGuard
    simpa only [d358, d415, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4164 (pattern : Twelve) (guard : d0 pattern = 1) : d0 pattern ≤ (0 : Int) + d169 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4165 (pattern : Twelve) (guard : d1848 pattern = 1) : d0 pattern ≤ (0 : Int) + d370 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d370, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4164 pattern childGuard
    simpa only [d1848, d370, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4166 (pattern : Twelve) (guard : d0 pattern = 1) : d0 pattern ≤ (0 : Int) + d170 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4167 (pattern : Twelve) (guard : d1848 pattern = 1) : d0 pattern ≤ (0 : Int) + d371 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d371, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4166 pattern childGuard
    simpa only [d1848, d371, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4168 (pattern : Twelve) (guard : d1848 pattern = 1) : d0 pattern ≤ (0 : Int) + d381 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4165 pattern childGuard
    simpa only [d381, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4167 pattern childGuard
    simpa only [d381, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4169 (pattern : Twelve) (guard : d0 pattern = 1) : d1 pattern ≤ (0 : Int) + d170 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4170 (pattern : Twelve) (guard : d1848 pattern = 1) : d26 pattern ≤ (0 : Int) + d371 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d26, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d26, d371, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d26, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4169 pattern childGuard
    simpa only [d1848, d26, d371, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4171 (pattern : Twelve) (guard : d1848 pattern = 1) : d50 pattern ≤ (0 : Int) + d382 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d50, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4170 pattern childGuard
    simpa only [d50, d382, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d50, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1415 pattern childGuard
    simpa only [d50, d382, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4172 (pattern : Twelve) (guard : d1848 pattern = 1) : d72 pattern ≤ (0 : Int) + d395 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d72, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4168 pattern childGuard
    simpa only [d72, d395, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d72, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4171 pattern childGuard
    simpa only [d72, d395, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4173 (pattern : Twelve) (guard : d1848 pattern = 1) : d0 pattern ≤ (0 : Int) + d383 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4167 pattern childGuard
    simpa only [d383, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1354 pattern childGuard
    simpa only [d383, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4174 (pattern : Twelve) (guard : d1848 pattern = 1) : d51 pattern ≤ (0 : Int) + d378 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d51, d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1372 pattern childGuard
    simpa only [d51, d378, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d51, d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2795 pattern childGuard
    simpa only [d51, d378, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4175 (pattern : Twelve) (guard : d1848 pattern = 1) : d73 pattern ≤ (0 : Int) + d396 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d73, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4173 pattern childGuard
    simpa only [d73, d396, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d73, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4174 pattern childGuard
    simpa only [d73, d396, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4176 (pattern : Twelve) (guard : d1848 pattern = 1) : d91 pattern ≤ (0 : Int) + d405 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d91, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4172 pattern childGuard
    simpa only [d91, d405, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d91, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4175 pattern childGuard
    simpa only [d91, d405, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4177 (pattern : Twelve) (guard : d0 pattern = 1) : d211 pattern ≤ (0 : Int) + d406 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4178 (pattern : Twelve) (guard : d1869 pattern = 1) : d354 pattern ≤ (0 : Int) + d411 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d354, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4176 pattern childGuard
    simpa only [d1869, d354, d411, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d354, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4177 pattern childGuard
    simpa only [d1869, d354, d411, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4179 (pattern : Twelve) (guard : d1848 pattern = 1) : d50 pattern ≤ (0 : Int) + d380 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d50, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1357 pattern childGuard
    simpa only [d50, d380, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d50, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1415 pattern childGuard
    simpa only [d50, d380, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4180 (pattern : Twelve) (guard : d1848 pattern = 1) : d72 pattern ≤ (0 : Int) + d399 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d72, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1354 pattern childGuard
    simpa only [d72, d399, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d72, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4179 pattern childGuard
    simpa only [d72, d399, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4181 (pattern : Twelve) (guard : d1848 pattern = 1) : d76 pattern ≤ (0 : Int) + d394 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d76, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1354 pattern childGuard
    simpa only [d76, d394, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d76, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4158 pattern childGuard
    simpa only [d76, d394, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4182 (pattern : Twelve) (guard : d1848 pattern = 1) : d93 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d93, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4180 pattern childGuard
    simpa only [d93, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d93, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4181 pattern childGuard
    simpa only [d93, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4183 (pattern : Twelve) (guard : d1869 pattern = 1) : d355 pattern ≤ (0 : Int) + d412 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d355, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4182 pattern childGuard
    simpa only [d1869, d355, d412, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d355, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1869, d355, d412, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4184 (pattern : Twelve) (guard : d1869 pattern = 1) : d359 pattern ≤ (0 : Int) + d416 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d359, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4178 pattern childGuard
    simpa only [d359, d416, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d359, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4183 pattern childGuard
    simpa only [d359, d416, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4185 (pattern : Twelve) (guard : d1869 pattern = 1) : d361 pattern ≤ (0 : Int) + d419 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d361, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4163 pattern childGuard
    simpa only [d361, d419, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d361, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4184 pattern childGuard
    simpa only [d361, d419, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4186 (pattern : Twelve) (guard : d1848 pattern = 1) : d80 pattern ≤ (0 : Int) + d394 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d80, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1312 pattern childGuard
    simpa only [d80, d394, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d80, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4158 pattern childGuard
    simpa only [d80, d394, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4187 (pattern : Twelve) (guard : d1848 pattern = 1) : d97 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d97, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4180 pattern childGuard
    simpa only [d97, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d97, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4186 pattern childGuard
    simpa only [d97, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4188 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d407 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4189 (pattern : Twelve) (guard : d1869 pattern = 1) : d356 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4187 pattern childGuard
    simpa only [d1869, d356, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4188 pattern childGuard
    simpa only [d1869, d356, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4190 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d406 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4191 (pattern : Twelve) (guard : d1869 pattern = 1) : d356 pattern ≤ (0 : Int) + d413 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d356, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4187 pattern childGuard
    simpa only [d1869, d356, d413, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d356, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4190 pattern childGuard
    simpa only [d1869, d356, d413, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4192 (pattern : Twelve) (guard : d1869 pattern = 1) : d356 pattern ≤ (0 : Int) + d412 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d356, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4187 pattern childGuard
    simpa only [d1869, d356, d412, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d356, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1869, d356, d412, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4193 (pattern : Twelve) (guard : d1869 pattern = 1) : d356 pattern ≤ (0 : Int) + d417 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4191 pattern childGuard
    simpa only [d417, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4192 pattern childGuard
    simpa only [d417, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4194 (pattern : Twelve) (guard : d1869 pattern = 1) : d356 pattern ≤ (0 : Int) + d420 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4189 pattern childGuard
    simpa only [d420, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4193 pattern childGuard
    simpa only [d420, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4195 (pattern : Twelve) (guard : d1869 pattern = 1) : d362 pattern ≤ (0 : Int) + d422 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d362, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4185 pattern childGuard
    simpa only [d362, d422, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d362, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4194 pattern childGuard
    simpa only [d362, d422, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4196 (pattern : Twelve) (guard : d1848 pattern = 1) : d73 pattern ≤ (0 : Int) + d394 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d73, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1354 pattern childGuard
    simpa only [d73, d394, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d73, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4174 pattern childGuard
    simpa only [d73, d394, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4197 (pattern : Twelve) (guard : d1848 pattern = 1) : d91 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d91, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4180 pattern childGuard
    simpa only [d91, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d91, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4196 pattern childGuard
    simpa only [d91, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4198 (pattern : Twelve) (guard : d1869 pattern = 1) : d357 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4197 pattern childGuard
    simpa only [d1869, d357, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4188 pattern childGuard
    simpa only [d1869, d357, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4199 (pattern : Twelve) (guard : d1869 pattern = 1) : d355 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4182 pattern childGuard
    simpa only [d1869, d355, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4188 pattern childGuard
    simpa only [d1869, d355, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
