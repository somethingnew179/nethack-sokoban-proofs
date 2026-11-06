/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons014
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c2100 (pattern : Twelve) (guard : d1839 pattern = 1) : d993 pattern ≤ (0 : Int) + d862 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d993, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2097 pattern childGuard
    simpa only [d993, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d993, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2099 pattern childGuard
    simpa only [d993, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2101 (pattern : Twelve) (guard : d1839 pattern = 1) : d994 pattern ≤ (0 : Int) + d863 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d994, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2093 pattern childGuard
    simpa only [d994, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d994, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c445 pattern childGuard
    simpa only [d994, d863, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2102 (pattern : Twelve) (guard : d1839 pattern = 1) : d1001 pattern ≤ (0 : Int) + d867 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1001, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2100 pattern childGuard
    simpa only [d1001, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1001, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2101 pattern childGuard
    simpa only [d1001, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2103 (pattern : Twelve) (guard : d1839 pattern = 1) : d1004 pattern ≤ (0 : Int) + d869 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1004, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2095 pattern childGuard
    simpa only [d1004, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1004, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2102 pattern childGuard
    simpa only [d1004, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2104 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d846 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2105 (pattern : Twelve) (guard : d1839 pattern = 1) : d986 pattern ≤ (0 : Int) + d857 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d986, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c492 pattern childGuard
    simpa only [d1839, d986, d857, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d986, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2104 pattern childGuard
    simpa only [d1839, d986, d857, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2106 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d848 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2107 (pattern : Twelve) (guard : d1839 pattern = 1) : d987 pattern ≤ (0 : Int) + d858 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d987, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c517 pattern childGuard
    simpa only [d1839, d987, d858, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d987, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2106 pattern childGuard
    simpa only [d1839, d987, d858, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2108 (pattern : Twelve) (guard : d1839 pattern = 1) : d995 pattern ≤ (0 : Int) + d864 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d995, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2105 pattern childGuard
    simpa only [d995, d864, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d995, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2107 pattern childGuard
    simpa only [d995, d864, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2109 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d850 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2110 (pattern : Twelve) (guard : d1839 pattern = 1) : d988 pattern ≤ (0 : Int) + d859 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d988, d859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c521 pattern childGuard
    simpa only [d1839, d988, d859, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d988, d859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2109 pattern childGuard
    simpa only [d1839, d988, d859, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2111 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d852 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2112 (pattern : Twelve) (guard : d1839 pattern = 1) : d989 pattern ≤ (0 : Int) + d860 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d989, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c524 pattern childGuard
    simpa only [d1839, d989, d860, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d989, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2111 pattern childGuard
    simpa only [d1839, d989, d860, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2113 (pattern : Twelve) (guard : d1839 pattern = 1) : d996 pattern ≤ (0 : Int) + d865 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d996, d865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2110 pattern childGuard
    simpa only [d996, d865, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d996, d865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2112 pattern childGuard
    simpa only [d996, d865, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2114 (pattern : Twelve) (guard : d1839 pattern = 1) : d997 pattern ≤ (0 : Int) + d866 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d997, d866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2107 pattern childGuard
    simpa only [d997, d866, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d997, d866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c445 pattern childGuard
    simpa only [d997, d866, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2115 (pattern : Twelve) (guard : d1839 pattern = 1) : d1002 pattern ≤ (0 : Int) + d868 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1002, d868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2113 pattern childGuard
    simpa only [d1002, d868, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1002, d868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2114 pattern childGuard
    simpa only [d1002, d868, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2116 (pattern : Twelve) (guard : d1839 pattern = 1) : d1005 pattern ≤ (0 : Int) + d870 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1005, d870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2108 pattern childGuard
    simpa only [d1005, d870, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1005, d870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2115 pattern childGuard
    simpa only [d1005, d870, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2117 (pattern : Twelve) (guard : d1839 pattern = 1) : d1007 pattern ≤ (0 : Int) + d871 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1007, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2103 pattern childGuard
    simpa only [d1007, d871, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1007, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2116 pattern childGuard
    simpa only [d1007, d871, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2118 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d839 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2119 (pattern : Twelve) (guard : d1839 pattern = 1) : d986 pattern ≤ (0 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d986, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c492 pattern childGuard
    simpa only [d1839, d986, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d986, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2118 pattern childGuard
    simpa only [d1839, d986, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2120 (pattern : Twelve) (guard : d1839 pattern = 1) : d998 pattern ≤ (0 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d998, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2119 pattern childGuard
    simpa only [d998, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d998, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2093 pattern childGuard
    simpa only [d998, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2121 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d843 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2122 (pattern : Twelve) (guard : d1839 pattern = 1) : d990 pattern ≤ (0 : Int) + d855 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d990, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c505 pattern childGuard
    simpa only [d1839, d990, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d990, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2121 pattern childGuard
    simpa only [d1839, d990, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2123 (pattern : Twelve) (guard : d1839 pattern = 1) : d999 pattern ≤ (0 : Int) + d862 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d999, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2122 pattern childGuard
    simpa only [d999, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d999, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2099 pattern childGuard
    simpa only [d999, d862, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2124 (pattern : Twelve) (guard : d1839 pattern = 1) : d1003 pattern ≤ (0 : Int) + d867 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1003, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2123 pattern childGuard
    simpa only [d1003, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1003, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2101 pattern childGuard
    simpa only [d1003, d867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2125 (pattern : Twelve) (guard : d1839 pattern = 1) : d1006 pattern ≤ (0 : Int) + d869 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1006, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2120 pattern childGuard
    simpa only [d1006, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1006, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2124 pattern childGuard
    simpa only [d1006, d869, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2126 (pattern : Twelve) (guard : d1839 pattern = 1) : d1008 pattern ≤ (0 : Int) + d871 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1008, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2125 pattern childGuard
    simpa only [d1008, d871, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1008, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2116 pattern childGuard
    simpa only [d1008, d871, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2127 (pattern : Twelve) (guard : d1839 pattern = 1) : d1009 pattern ≤ (0 : Int) + d871 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2117 pattern childGuard
    simpa only [d1009, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2126 pattern childGuard
    simpa only [d1009, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2128 (pattern : Twelve) (guard : d1839 pattern = 1) : d1010 pattern ≤ (0 : Int) + d871 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2127 pattern childGuard
    simpa only [d1010, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2126 pattern childGuard
    simpa only [d1010, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2129 (pattern : Twelve) (guard : d0 pattern = 1) : d1355 pattern ≤ (0 : Int) + d1294 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2130 (pattern : Twelve) (guard : d1839 pattern = 1) : d1412 pattern ≤ (0 : Int) + d1305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d1412, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c543 pattern childGuard
    simpa only [d1839, d1412, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d1412, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2129 pattern childGuard
    simpa only [d1839, d1412, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2131 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1296 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2132 (pattern : Twelve) (guard : d1839 pattern = 1) : d1413 pattern ≤ (0 : Int) + d1306 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d1413, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c546 pattern childGuard
    simpa only [d1839, d1413, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d1413, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2131 pattern childGuard
    simpa only [d1839, d1413, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2133 (pattern : Twelve) (guard : d1839 pattern = 1) : d1417 pattern ≤ (0 : Int) + d1313 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1417, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2130 pattern childGuard
    simpa only [d1417, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1417, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2132 pattern childGuard
    simpa only [d1417, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2134 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1294 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2135 (pattern : Twelve) (guard : d1839 pattern = 1) : d1414 pattern ≤ (0 : Int) + d1305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d1414, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c543 pattern childGuard
    simpa only [d1839, d1414, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d1414, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2134 pattern childGuard
    simpa only [d1839, d1414, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2136 (pattern : Twelve) (guard : d1839 pattern = 1) : d1418 pattern ≤ (0 : Int) + d1313 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1418, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2135 pattern childGuard
    simpa only [d1418, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1418, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2132 pattern childGuard
    simpa only [d1418, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2137 (pattern : Twelve) (guard : d1839 pattern = 1) : d1421 pattern ≤ (0 : Int) + d1313 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2133 pattern childGuard
    simpa only [d1421, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2136 pattern childGuard
    simpa only [d1421, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2138 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1298 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2139 (pattern : Twelve) (guard : d1839 pattern = 1) : d1415 pattern ≤ (0 : Int) + d1307 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d1415, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c554 pattern childGuard
    simpa only [d1839, d1415, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d1415, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2138 pattern childGuard
    simpa only [d1839, d1415, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2140 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1300 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2141 (pattern : Twelve) (guard : d1839 pattern = 1) : d1416 pattern ≤ (0 : Int) + d1308 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d1416, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c557 pattern childGuard
    simpa only [d1839, d1416, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d1416, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2140 pattern childGuard
    simpa only [d1839, d1416, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2142 (pattern : Twelve) (guard : d1839 pattern = 1) : d1419 pattern ≤ (0 : Int) + d1314 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1419, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2139 pattern childGuard
    simpa only [d1419, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1419, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2141 pattern childGuard
    simpa only [d1419, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2143 (pattern : Twelve) (guard : d1839 pattern = 1) : d1420 pattern ≤ (0 : Int) + d1315 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1420, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2132 pattern childGuard
    simpa only [d1420, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1420, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c445 pattern childGuard
    simpa only [d1420, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2144 (pattern : Twelve) (guard : d1839 pattern = 1) : d1422 pattern ≤ (0 : Int) + d1319 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1422, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2142 pattern childGuard
    simpa only [d1422, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1422, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2143 pattern childGuard
    simpa only [d1422, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2145 (pattern : Twelve) (guard : d1839 pattern = 1) : d1423 pattern ≤ (0 : Int) + d1321 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1423, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2137 pattern childGuard
    simpa only [d1423, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1423, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2144 pattern childGuard
    simpa only [d1423, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2146 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1301 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2147 (pattern : Twelve) (guard : d1839 pattern = 1) : d1414 pattern ≤ (0 : Int) + d1309 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d1414, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c543 pattern childGuard
    simpa only [d1839, d1414, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d1414, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2146 pattern childGuard
    simpa only [d1839, d1414, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2148 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1302 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2149 (pattern : Twelve) (guard : d1839 pattern = 1) : d1413 pattern ≤ (0 : Int) + d1310 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d1413, d1310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c546 pattern childGuard
    simpa only [d1839, d1413, d1310, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d1413, d1310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2148 pattern childGuard
    simpa only [d1839, d1413, d1310, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2150 (pattern : Twelve) (guard : d1839 pattern = 1) : d1418 pattern ≤ (0 : Int) + d1316 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1418, d1316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2147 pattern childGuard
    simpa only [d1418, d1316, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1418, d1316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2149 pattern childGuard
    simpa only [d1418, d1316, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2151 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1303 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2152 (pattern : Twelve) (guard : d1839 pattern = 1) : d1415 pattern ≤ (0 : Int) + d1311 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d1415, d1311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c554 pattern childGuard
    simpa only [d1839, d1415, d1311, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d1415, d1311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2151 pattern childGuard
    simpa only [d1839, d1415, d1311, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2153 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1304 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2154 (pattern : Twelve) (guard : d1839 pattern = 1) : d1416 pattern ≤ (0 : Int) + d1312 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d1416, d1312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c557 pattern childGuard
    simpa only [d1839, d1416, d1312, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d1416, d1312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2153 pattern childGuard
    simpa only [d1839, d1416, d1312, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2155 (pattern : Twelve) (guard : d1839 pattern = 1) : d1419 pattern ≤ (0 : Int) + d1317 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1419, d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2152 pattern childGuard
    simpa only [d1419, d1317, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1419, d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2154 pattern childGuard
    simpa only [d1419, d1317, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2156 (pattern : Twelve) (guard : d1839 pattern = 1) : d1420 pattern ≤ (0 : Int) + d1318 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1420, d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2149 pattern childGuard
    simpa only [d1420, d1318, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1420, d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c445 pattern childGuard
    simpa only [d1420, d1318, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2157 (pattern : Twelve) (guard : d1839 pattern = 1) : d1422 pattern ≤ (0 : Int) + d1320 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1422, d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2155 pattern childGuard
    simpa only [d1422, d1320, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1422, d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2156 pattern childGuard
    simpa only [d1422, d1320, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2158 (pattern : Twelve) (guard : d1839 pattern = 1) : d1424 pattern ≤ (0 : Int) + d1322 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1424, d1322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2150 pattern childGuard
    simpa only [d1424, d1322, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1424, d1322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2157 pattern childGuard
    simpa only [d1424, d1322, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2159 (pattern : Twelve) (guard : d1839 pattern = 1) : d1425 pattern ≤ (0 : Int) + d1323 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1425, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2145 pattern childGuard
    simpa only [d1425, d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1425, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2158 pattern childGuard
    simpa only [d1425, d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2160 (pattern : Twelve) (guard : d1839 pattern = 1) : d1424 pattern ≤ (0 : Int) + d1321 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1424, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2136 pattern childGuard
    simpa only [d1424, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1424, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2144 pattern childGuard
    simpa only [d1424, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2161 (pattern : Twelve) (guard : d1839 pattern = 1) : d1424 pattern ≤ (0 : Int) + d1323 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2160 pattern childGuard
    simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2158 pattern childGuard
    simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2162 (pattern : Twelve) (guard : d1839 pattern = 1) : d1426 pattern ≤ (0 : Int) + d1323 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2159 pattern childGuard
    simpa only [d1426, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2161 pattern childGuard
    simpa only [d1426, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2163 (pattern : Twelve) (guard : d1839 pattern = 1) : d1427 pattern ≤ (0 : Int) + d1323 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2162 pattern childGuard
    simpa only [d1427, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2161 pattern childGuard
    simpa only [d1427, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2164 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1650 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2165 (pattern : Twelve) (guard : d1839 pattern = 1) : d1705 pattern ≤ (0 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d1705, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c582 pattern childGuard
    simpa only [d1839, d1705, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d1705, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2164 pattern childGuard
    simpa only [d1839, d1705, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2166 (pattern : Twelve) (guard : d1839 pattern = 1) : d1706 pattern ≤ (0 : Int) + d1657 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d1706, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c585 pattern childGuard
    simpa only [d1839, d1706, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d1706, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2140 pattern childGuard
    simpa only [d1839, d1706, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2167 (pattern : Twelve) (guard : d1839 pattern = 1) : d1709 pattern ≤ (0 : Int) + d1660 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1709, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2165 pattern childGuard
    simpa only [d1709, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1709, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2166 pattern childGuard
    simpa only [d1709, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2168 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1653 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2169 (pattern : Twelve) (guard : d1839 pattern = 1) : d1707 pattern ≤ (0 : Int) + d1658 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d1707, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c588 pattern childGuard
    simpa only [d1839, d1707, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d1707, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2168 pattern childGuard
    simpa only [d1839, d1707, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2170 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1655 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2171 (pattern : Twelve) (guard : d1839 pattern = 1) : d1708 pattern ≤ (0 : Int) + d1659 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1839, d1708, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c591 pattern childGuard
    simpa only [d1839, d1708, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1839, d1708, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2170 pattern childGuard
    simpa only [d1839, d1708, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2172 (pattern : Twelve) (guard : d1839 pattern = 1) : d1710 pattern ≤ (0 : Int) + d1661 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1710, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2169 pattern childGuard
    simpa only [d1710, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1710, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2171 pattern childGuard
    simpa only [d1710, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2173 (pattern : Twelve) (guard : d1839 pattern = 1) : d1711 pattern ≤ (0 : Int) + d1662 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1711, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2166 pattern childGuard
    simpa only [d1711, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1711, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c445 pattern childGuard
    simpa only [d1711, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2174 (pattern : Twelve) (guard : d1839 pattern = 1) : d1712 pattern ≤ (0 : Int) + d1663 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1712, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2172 pattern childGuard
    simpa only [d1712, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1712, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2173 pattern childGuard
    simpa only [d1712, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2175 (pattern : Twelve) (guard : d1839 pattern = 1) : d1713 pattern ≤ (0 : Int) + d1664 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1713, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2167 pattern childGuard
    simpa only [d1713, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1839 pattern = 1 := by simpa only [d1713, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2174 pattern childGuard
    simpa only [d1713, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2176 (pattern : Twelve) (guard : d0 pattern = 1) : d50 pattern ≤ (0 : Int) + d185 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2177 (pattern : Twelve) (guard : d1852 pattern = 1) : d72 pattern ≤ (0 : Int) + d425 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d72, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1852, d72, d425, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d72, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2176 pattern childGuard
    simpa only [d1852, d72, d425, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2178 (pattern : Twelve) (guard : d0 pattern = 1) : d198 pattern ≤ (0 : Int) + d426 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2179 (pattern : Twelve) (guard : d1858 pattern = 1) : d304 pattern ≤ (0 : Int) + d444 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d304, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2177 pattern childGuard
    simpa only [d1858, d304, d444, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d304, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2178 pattern childGuard
    simpa only [d1858, d304, d444, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2180 (pattern : Twelve) (guard : d1 pattern = 1) : d52 pattern ≤ (0 : Int) + d52 pattern := by
  omega
theorem c2181 (pattern : Twelve) (guard : d0 pattern = 1) : d53 pattern ≤ (0 : Int) + d188 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2182 (pattern : Twelve) (guard : d1852 pattern = 1) : d74 pattern ≤ (0 : Int) + d427 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d74, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2180 pattern childGuard
    simpa only [d1852, d74, d427, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d74, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2181 pattern childGuard
    simpa only [d1852, d74, d427, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2183 (pattern : Twelve) (guard : d0 pattern = 1) : d200 pattern ≤ (0 : Int) + d428 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2184 (pattern : Twelve) (guard : d1858 pattern = 1) : d305 pattern ≤ (0 : Int) + d445 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d305, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2182 pattern childGuard
    simpa only [d1858, d305, d445, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d305, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2183 pattern childGuard
    simpa only [d1858, d305, d445, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2185 (pattern : Twelve) (guard : d1858 pattern = 1) : d320 pattern ≤ (0 : Int) + d455 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d320, d455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2179 pattern childGuard
    simpa only [d320, d455, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d320, d455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2184 pattern childGuard
    simpa only [d320, d455, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2186 (pattern : Twelve) (guard : d0 pattern = 1) : d50 pattern ≤ (0 : Int) + d188 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2187 (pattern : Twelve) (guard : d1852 pattern = 1) : d72 pattern ≤ (0 : Int) + d429 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d72, d429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1852, d72, d429, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d72, d429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2186 pattern childGuard
    simpa only [d1852, d72, d429, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2188 (pattern : Twelve) (guard : d0 pattern = 1) : d200 pattern ≤ (0 : Int) + d430 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2189 (pattern : Twelve) (guard : d1858 pattern = 1) : d306 pattern ≤ (0 : Int) + d446 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d306, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2187 pattern childGuard
    simpa only [d1858, d306, d446, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d306, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2188 pattern childGuard
    simpa only [d1858, d306, d446, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2190 (pattern : Twelve) (guard : d1 pattern = 1) : d56 pattern ≤ (0 : Int) + d56 pattern := by
  omega
theorem c2191 (pattern : Twelve) (guard : d0 pattern = 1) : d57 pattern ≤ (0 : Int) + d191 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2192 (pattern : Twelve) (guard : d1852 pattern = 1) : d77 pattern ≤ (0 : Int) + d431 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d77, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2190 pattern childGuard
    simpa only [d1852, d77, d431, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d77, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2191 pattern childGuard
    simpa only [d1852, d77, d431, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2193 (pattern : Twelve) (guard : d0 pattern = 1) : d202 pattern ≤ (0 : Int) + d432 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2194 (pattern : Twelve) (guard : d1858 pattern = 1) : d307 pattern ≤ (0 : Int) + d447 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d307, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2192 pattern childGuard
    simpa only [d1858, d307, d447, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d307, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2193 pattern childGuard
    simpa only [d1858, d307, d447, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2195 (pattern : Twelve) (guard : d1858 pattern = 1) : d321 pattern ≤ (0 : Int) + d456 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d321, d456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2189 pattern childGuard
    simpa only [d321, d456, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d321, d456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2194 pattern childGuard
    simpa only [d321, d456, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2196 (pattern : Twelve) (guard : d1858 pattern = 1) : d332 pattern ≤ (0 : Int) + d465 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d332, d465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2185 pattern childGuard
    simpa only [d332, d465, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d332, d465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2195 pattern childGuard
    simpa only [d332, d465, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2197 (pattern : Twelve) (guard : d0 pattern = 1) : d58 pattern ≤ (0 : Int) + d193 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2198 (pattern : Twelve) (guard : d1852 pattern = 1) : d79 pattern ≤ (0 : Int) + d433 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d79, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1852, d79, d433, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d79, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2197 pattern childGuard
    simpa only [d1852, d79, d433, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2199 (pattern : Twelve) (guard : d0 pattern = 1) : d204 pattern ≤ (0 : Int) + d434 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2200 (pattern : Twelve) (guard : d1858 pattern = 1) : d308 pattern ≤ (0 : Int) + d448 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d308, d448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2198 pattern childGuard
    simpa only [d1858, d308, d448, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d308, d448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2199 pattern childGuard
    simpa only [d1858, d308, d448, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2201 (pattern : Twelve) (guard : d1 pattern = 1) : d59 pattern ≤ (0 : Int) + d59 pattern := by
  omega
theorem c2202 (pattern : Twelve) (guard : d0 pattern = 1) : d60 pattern ≤ (0 : Int) + d196 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2203 (pattern : Twelve) (guard : d1852 pattern = 1) : d81 pattern ≤ (0 : Int) + d435 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d81, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2201 pattern childGuard
    simpa only [d1852, d81, d435, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d81, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2202 pattern childGuard
    simpa only [d1852, d81, d435, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2204 (pattern : Twelve) (guard : d0 pattern = 1) : d206 pattern ≤ (0 : Int) + d436 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2205 (pattern : Twelve) (guard : d1858 pattern = 1) : d309 pattern ≤ (0 : Int) + d449 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d309, d449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2203 pattern childGuard
    simpa only [d1858, d309, d449, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d309, d449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2204 pattern childGuard
    simpa only [d1858, d309, d449, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2206 (pattern : Twelve) (guard : d1858 pattern = 1) : d322 pattern ≤ (0 : Int) + d457 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d322, d457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2200 pattern childGuard
    simpa only [d322, d457, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d322, d457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2205 pattern childGuard
    simpa only [d322, d457, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2207 (pattern : Twelve) (guard : d0 pattern = 1) : d57 pattern ≤ (0 : Int) + d196 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2208 (pattern : Twelve) (guard : d1852 pattern = 1) : d77 pattern ≤ (0 : Int) + d437 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d77, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2190 pattern childGuard
    simpa only [d1852, d77, d437, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d77, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2207 pattern childGuard
    simpa only [d1852, d77, d437, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2209 (pattern : Twelve) (guard : d0 pattern = 1) : d206 pattern ≤ (0 : Int) + d432 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2210 (pattern : Twelve) (guard : d1858 pattern = 1) : d310 pattern ≤ (0 : Int) + d450 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d310, d450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2208 pattern childGuard
    simpa only [d1858, d310, d450, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d310, d450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2209 pattern childGuard
    simpa only [d1858, d310, d450, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2211 (pattern : Twelve) (guard : d1858 pattern = 1) : d6 pattern ≤ (0 : Int) + d6 pattern := by
  omega
theorem c2212 (pattern : Twelve) (guard : d1858 pattern = 1) : d323 pattern ≤ (0 : Int) + d458 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d323, d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2210 pattern childGuard
    simpa only [d323, d458, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d323, d458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2211 pattern childGuard
    simpa only [d323, d458, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2213 (pattern : Twelve) (guard : d1858 pattern = 1) : d333 pattern ≤ (0 : Int) + d466 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d333, d466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2206 pattern childGuard
    simpa only [d333, d466, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d333, d466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2212 pattern childGuard
    simpa only [d333, d466, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2214 (pattern : Twelve) (guard : d1858 pattern = 1) : d338 pattern ≤ (0 : Int) + d471 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d338, d471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2196 pattern childGuard
    simpa only [d338, d471, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d338, d471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2213 pattern childGuard
    simpa only [d338, d471, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2215 (pattern : Twelve) (guard : d0 pattern = 1) : d50 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2216 (pattern : Twelve) (guard : d1852 pattern = 1) : d72 pattern ≤ (0 : Int) + d438 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d72, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1852, d72, d438, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d72, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2215 pattern childGuard
    simpa only [d1852, d72, d438, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2217 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d438 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2218 (pattern : Twelve) (guard : d1858 pattern = 1) : d311 pattern ≤ (0 : Int) + d438 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2216 pattern childGuard
    simpa only [d1858, d311, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2217 pattern childGuard
    simpa only [d1858, d311, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2219 (pattern : Twelve) (guard : d0 pattern = 1) : d62 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2220 (pattern : Twelve) (guard : d1852 pattern = 1) : d83 pattern ≤ (0 : Int) + d439 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d83, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2180 pattern childGuard
    simpa only [d1852, d83, d439, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d83, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2219 pattern childGuard
    simpa only [d1852, d83, d439, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2221 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d440 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2222 (pattern : Twelve) (guard : d1858 pattern = 1) : d312 pattern ≤ (0 : Int) + d451 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d312, d451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2220 pattern childGuard
    simpa only [d1858, d312, d451, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d312, d451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2221 pattern childGuard
    simpa only [d1858, d312, d451, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2223 (pattern : Twelve) (guard : d1858 pattern = 1) : d324 pattern ≤ (0 : Int) + d459 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d324, d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2218 pattern childGuard
    simpa only [d324, d459, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d324, d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2222 pattern childGuard
    simpa only [d324, d459, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2224 (pattern : Twelve) (guard : d0 pattern = 1) : d65 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2225 (pattern : Twelve) (guard : d1852 pattern = 1) : d85 pattern ≤ (0 : Int) + d432 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d85, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2190 pattern childGuard
    simpa only [d1852, d85, d432, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d85, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2224 pattern childGuard
    simpa only [d1852, d85, d432, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2226 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d432 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2227 (pattern : Twelve) (guard : d1858 pattern = 1) : d313 pattern ≤ (0 : Int) + d432 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2225 pattern childGuard
    simpa only [d1858, d313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2226 pattern childGuard
    simpa only [d1858, d313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2228 (pattern : Twelve) (guard : d1858 pattern = 1) : d325 pattern ≤ (0 : Int) + d460 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d325, d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2218 pattern childGuard
    simpa only [d325, d460, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d325, d460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2227 pattern childGuard
    simpa only [d325, d460, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2229 (pattern : Twelve) (guard : d1858 pattern = 1) : d334 pattern ≤ (0 : Int) + d467 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d334, d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2223 pattern childGuard
    simpa only [d334, d467, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d334, d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2228 pattern childGuard
    simpa only [d334, d467, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2230 (pattern : Twelve) (guard : d0 pattern = 1) : d67 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2231 (pattern : Twelve) (guard : d1852 pattern = 1) : d87 pattern ≤ (0 : Int) + d441 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d87, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1852, d87, d441, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d87, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2230 pattern childGuard
    simpa only [d1852, d87, d441, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2232 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d441 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2233 (pattern : Twelve) (guard : d1858 pattern = 1) : d314 pattern ≤ (0 : Int) + d441 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2231 pattern childGuard
    simpa only [d1858, d314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2232 pattern childGuard
    simpa only [d1858, d314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2234 (pattern : Twelve) (guard : d0 pattern = 1) : d69 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2235 (pattern : Twelve) (guard : d1852 pattern = 1) : d89 pattern ≤ (0 : Int) + d436 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d89, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2201 pattern childGuard
    simpa only [d1852, d89, d436, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d89, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2234 pattern childGuard
    simpa only [d1852, d89, d436, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2236 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d436 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2237 (pattern : Twelve) (guard : d1858 pattern = 1) : d315 pattern ≤ (0 : Int) + d436 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1858, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2235 pattern childGuard
    simpa only [d1858, d315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1858, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2236 pattern childGuard
    simpa only [d1858, d315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2238 (pattern : Twelve) (guard : d1858 pattern = 1) : d326 pattern ≤ (0 : Int) + d461 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d326, d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2233 pattern childGuard
    simpa only [d326, d461, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d326, d461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2237 pattern childGuard
    simpa only [d326, d461, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2239 (pattern : Twelve) (guard : d1858 pattern = 1) : d327 pattern ≤ (0 : Int) + d462 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1858 pattern = 1 := by simpa only [d327, d462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2227 pattern childGuard
    simpa only [d327, d462, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1858 pattern = 1 := by simpa only [d327, d462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2211 pattern childGuard
    simpa only [d327, d462, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
