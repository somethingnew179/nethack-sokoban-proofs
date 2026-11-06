/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons045
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c6440 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d882 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6441 (pattern : Twelve) (guard : d1852 pattern = 1) : d438 pattern ≤ (0 : Int) + d890 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d438, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1852, d438, d890, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d438, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6440 pattern childGuard
    simpa only [d1852, d438, d890, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6442 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d883 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6443 (pattern : Twelve) (guard : d1852 pattern = 1) : d1073 pattern ≤ (0 : Int) + d891 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1073, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1852, d1073, d891, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1073, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6442 pattern childGuard
    simpa only [d1852, d1073, d891, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6444 (pattern : Twelve) (guard : d1852 pattern = 1) : d1084 pattern ≤ (0 : Int) + d898 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1084, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6441 pattern childGuard
    simpa only [d1084, d898, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1084, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6443 pattern childGuard
    simpa only [d1084, d898, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6445 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d884 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6446 (pattern : Twelve) (guard : d1852 pattern = 1) : d432 pattern ≤ (0 : Int) + d892 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d432, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2190 pattern childGuard
    simpa only [d1852, d432, d892, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d432, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6445 pattern childGuard
    simpa only [d1852, d432, d892, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6447 (pattern : Twelve) (guard : d1852 pattern = 1) : d1072 pattern ≤ (0 : Int) + d893 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1072, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2361 pattern childGuard
    simpa only [d1852, d1072, d893, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1072, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6442 pattern childGuard
    simpa only [d1852, d1072, d893, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6448 (pattern : Twelve) (guard : d1852 pattern = 1) : d1081 pattern ≤ (0 : Int) + d899 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1081, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6446 pattern childGuard
    simpa only [d1081, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1081, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6447 pattern childGuard
    simpa only [d1081, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6449 (pattern : Twelve) (guard : d1852 pattern = 1) : d1092 pattern ≤ (0 : Int) + d902 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1092, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6444 pattern childGuard
    simpa only [d1092, d902, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1092, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6448 pattern childGuard
    simpa only [d1092, d902, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6450 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d885 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6451 (pattern : Twelve) (guard : d1852 pattern = 1) : d441 pattern ≤ (0 : Int) + d894 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d441, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c92 pattern childGuard
    simpa only [d1852, d441, d894, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d441, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6450 pattern childGuard
    simpa only [d1852, d441, d894, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6452 (pattern : Twelve) (guard : d1 pattern = 1) : d886 pattern ≤ (0 : Int) + d886 pattern := by
  omega
theorem c6453 (pattern : Twelve) (guard : d1852 pattern = 1) : d1076 pattern ≤ (0 : Int) + d895 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1076, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6452 pattern childGuard
    simpa only [d1852, d1076, d895, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1076, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6442 pattern childGuard
    simpa only [d1852, d1076, d895, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6454 (pattern : Twelve) (guard : d1852 pattern = 1) : d1086 pattern ≤ (0 : Int) + d900 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1086, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6451 pattern childGuard
    simpa only [d1086, d900, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1086, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6453 pattern childGuard
    simpa only [d1086, d900, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6455 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d887 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6456 (pattern : Twelve) (guard : d1852 pattern = 1) : d436 pattern ≤ (0 : Int) + d896 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d436, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2201 pattern childGuard
    simpa only [d1852, d436, d896, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d436, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6455 pattern childGuard
    simpa only [d1852, d436, d896, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6457 (pattern : Twelve) (guard : d1 pattern = 1) : d888 pattern ≤ (0 : Int) + d888 pattern := by
  omega
theorem c6458 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d889 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6459 (pattern : Twelve) (guard : d1852 pattern = 1) : d1077 pattern ≤ (0 : Int) + d897 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1077, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6457 pattern childGuard
    simpa only [d1852, d1077, d897, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1077, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6458 pattern childGuard
    simpa only [d1852, d1077, d897, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6460 (pattern : Twelve) (guard : d1852 pattern = 1) : d1087 pattern ≤ (0 : Int) + d901 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1087, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6456 pattern childGuard
    simpa only [d1087, d901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1087, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6459 pattern childGuard
    simpa only [d1087, d901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6461 (pattern : Twelve) (guard : d1852 pattern = 1) : d1094 pattern ≤ (0 : Int) + d903 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1094, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6454 pattern childGuard
    simpa only [d1094, d903, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1094, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6460 pattern childGuard
    simpa only [d1094, d903, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6462 (pattern : Twelve) (guard : d1852 pattern = 1) : d1091 pattern ≤ (0 : Int) + d904 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1091, d904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6448 pattern childGuard
    simpa only [d1091, d904, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1091, d904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6359 pattern childGuard
    simpa only [d1091, d904, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6463 (pattern : Twelve) (guard : d1852 pattern = 1) : d1098 pattern ≤ (0 : Int) + d905 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1098, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6461 pattern childGuard
    simpa only [d1098, d905, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1098, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6462 pattern childGuard
    simpa only [d1098, d905, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6464 (pattern : Twelve) (guard : d1852 pattern = 1) : d1101 pattern ≤ (0 : Int) + d906 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1101, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6449 pattern childGuard
    simpa only [d1101, d906, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1101, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6463 pattern childGuard
    simpa only [d1101, d906, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6465 (pattern : Twelve) (guard : d1852 pattern = 1) : d1104 pattern ≤ (0 : Int) + d907 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1104, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6439 pattern childGuard
    simpa only [d1104, d907, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1104, d907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6464 pattern childGuard
    simpa only [d1104, d907, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6466 (pattern : Twelve) (guard : d1852 pattern = 1) : d1294 pattern ≤ (0 : Int) + d1294 pattern := by
  omega
theorem c6467 (pattern : Twelve) (guard : d1852 pattern = 1) : d1472 pattern ≤ (0 : Int) + d1305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1472, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6283 pattern childGuard
    simpa only [d1472, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1472, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6466 pattern childGuard
    simpa only [d1472, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6468 (pattern : Twelve) (guard : d1852 pattern = 1) : d1296 pattern ≤ (0 : Int) + d1296 pattern := by
  omega
theorem c6469 (pattern : Twelve) (guard : d1852 pattern = 1) : d1473 pattern ≤ (0 : Int) + d1306 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1473, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6286 pattern childGuard
    simpa only [d1473, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1473, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6468 pattern childGuard
    simpa only [d1473, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6470 (pattern : Twelve) (guard : d1852 pattern = 1) : d1479 pattern ≤ (0 : Int) + d1313 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1479, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6467 pattern childGuard
    simpa only [d1479, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1479, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6469 pattern childGuard
    simpa only [d1479, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6471 (pattern : Twelve) (guard : d1852 pattern = 1) : d1474 pattern ≤ (0 : Int) + d1305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1474, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6290 pattern childGuard
    simpa only [d1474, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1474, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6466 pattern childGuard
    simpa only [d1474, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6472 (pattern : Twelve) (guard : d1852 pattern = 1) : d1480 pattern ≤ (0 : Int) + d1313 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1480, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6471 pattern childGuard
    simpa only [d1480, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1480, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6469 pattern childGuard
    simpa only [d1480, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6473 (pattern : Twelve) (guard : d1852 pattern = 1) : d1484 pattern ≤ (0 : Int) + d1313 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6470 pattern childGuard
    simpa only [d1484, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6472 pattern childGuard
    simpa only [d1484, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6474 (pattern : Twelve) (guard : d1852 pattern = 1) : d1298 pattern ≤ (0 : Int) + d1298 pattern := by
  omega
theorem c6475 (pattern : Twelve) (guard : d1852 pattern = 1) : d1475 pattern ≤ (0 : Int) + d1307 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1475, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6295 pattern childGuard
    simpa only [d1475, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1475, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6474 pattern childGuard
    simpa only [d1475, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6476 (pattern : Twelve) (guard : d1852 pattern = 1) : d1300 pattern ≤ (0 : Int) + d1300 pattern := by
  omega
theorem c6477 (pattern : Twelve) (guard : d1852 pattern = 1) : d1476 pattern ≤ (0 : Int) + d1308 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1476, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6298 pattern childGuard
    simpa only [d1476, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1476, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6476 pattern childGuard
    simpa only [d1476, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6478 (pattern : Twelve) (guard : d1852 pattern = 1) : d1481 pattern ≤ (0 : Int) + d1314 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1481, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6475 pattern childGuard
    simpa only [d1481, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1481, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6477 pattern childGuard
    simpa only [d1481, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6479 (pattern : Twelve) (guard : d1852 pattern = 1) : d1482 pattern ≤ (0 : Int) + d1315 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1482, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6469 pattern childGuard
    simpa only [d1482, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1482, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6359 pattern childGuard
    simpa only [d1482, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6480 (pattern : Twelve) (guard : d1852 pattern = 1) : d1485 pattern ≤ (0 : Int) + d1319 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1485, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6478 pattern childGuard
    simpa only [d1485, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1485, d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6479 pattern childGuard
    simpa only [d1485, d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6481 (pattern : Twelve) (guard : d1852 pattern = 1) : d1487 pattern ≤ (0 : Int) + d1321 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1487, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6473 pattern childGuard
    simpa only [d1487, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1487, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6480 pattern childGuard
    simpa only [d1487, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6482 (pattern : Twelve) (guard : d1852 pattern = 1) : d1488 pattern ≤ (0 : Int) + d1321 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1488, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6472 pattern childGuard
    simpa only [d1488, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1488, d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6480 pattern childGuard
    simpa only [d1488, d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6483 (pattern : Twelve) (guard : d1852 pattern = 1) : d1490 pattern ≤ (0 : Int) + d1321 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6481 pattern childGuard
    simpa only [d1490, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6482 pattern childGuard
    simpa only [d1490, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6484 (pattern : Twelve) (guard : d1852 pattern = 1) : d1491 pattern ≤ (0 : Int) + d1321 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6483 pattern childGuard
    simpa only [d1491, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6482 pattern childGuard
    simpa only [d1491, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6485 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1333 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6486 (pattern : Twelve) (guard : d1852 pattern = 1) : d1073 pattern ≤ (0 : Int) + d1339 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1073, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1852, d1073, d1339, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1073, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6485 pattern childGuard
    simpa only [d1852, d1073, d1339, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6487 (pattern : Twelve) (guard : d1852 pattern = 1) : d1474 pattern ≤ (0 : Int) + d1345 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1474, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6486 pattern childGuard
    simpa only [d1474, d1345, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1474, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6466 pattern childGuard
    simpa only [d1474, d1345, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6488 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1334 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6489 (pattern : Twelve) (guard : d1852 pattern = 1) : d1072 pattern ≤ (0 : Int) + d1340 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1072, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2361 pattern childGuard
    simpa only [d1852, d1072, d1340, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1072, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6488 pattern childGuard
    simpa only [d1852, d1072, d1340, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6490 (pattern : Twelve) (guard : d1852 pattern = 1) : d1473 pattern ≤ (0 : Int) + d1346 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1473, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6489 pattern childGuard
    simpa only [d1473, d1346, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1473, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6468 pattern childGuard
    simpa only [d1473, d1346, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6491 (pattern : Twelve) (guard : d1852 pattern = 1) : d1480 pattern ≤ (0 : Int) + d1349 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1480, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6487 pattern childGuard
    simpa only [d1480, d1349, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1480, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6490 pattern childGuard
    simpa only [d1480, d1349, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6492 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1335 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6493 (pattern : Twelve) (guard : d1852 pattern = 1) : d1074 pattern ≤ (0 : Int) + d1341 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1074, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c100 pattern childGuard
    simpa only [d1852, d1074, d1341, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1074, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6492 pattern childGuard
    simpa only [d1852, d1074, d1341, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6494 (pattern : Twelve) (guard : d1852 pattern = 1) : d1342 pattern ≤ (0 : Int) + d1342 pattern := by
  omega
theorem c6495 (pattern : Twelve) (guard : d1852 pattern = 1) : d1477 pattern ≤ (0 : Int) + d1347 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1477, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6493 pattern childGuard
    simpa only [d1477, d1347, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1477, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6494 pattern childGuard
    simpa only [d1477, d1347, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6496 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1337 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6497 (pattern : Twelve) (guard : d1852 pattern = 1) : d1075 pattern ≤ (0 : Int) + d1343 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1075, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2374 pattern childGuard
    simpa only [d1852, d1075, d1343, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1075, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6496 pattern childGuard
    simpa only [d1852, d1075, d1343, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6498 (pattern : Twelve) (guard : d1852 pattern = 1) : d1344 pattern ≤ (0 : Int) + d1344 pattern := by
  omega
theorem c6499 (pattern : Twelve) (guard : d1852 pattern = 1) : d1478 pattern ≤ (0 : Int) + d1348 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1478, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6497 pattern childGuard
    simpa only [d1478, d1348, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1478, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6498 pattern childGuard
    simpa only [d1478, d1348, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6500 (pattern : Twelve) (guard : d1852 pattern = 1) : d1483 pattern ≤ (0 : Int) + d1350 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1483, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6495 pattern childGuard
    simpa only [d1483, d1350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1483, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6499 pattern childGuard
    simpa only [d1483, d1350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6501 (pattern : Twelve) (guard : d1852 pattern = 1) : d1482 pattern ≤ (0 : Int) + d1351 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1482, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6490 pattern childGuard
    simpa only [d1482, d1351, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1482, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6359 pattern childGuard
    simpa only [d1482, d1351, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6502 (pattern : Twelve) (guard : d1852 pattern = 1) : d1486 pattern ≤ (0 : Int) + d1352 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1486, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6500 pattern childGuard
    simpa only [d1486, d1352, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1486, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6501 pattern childGuard
    simpa only [d1486, d1352, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6503 (pattern : Twelve) (guard : d1852 pattern = 1) : d1489 pattern ≤ (0 : Int) + d1353 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1489, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6491 pattern childGuard
    simpa only [d1489, d1353, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1489, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6502 pattern childGuard
    simpa only [d1489, d1353, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6504 (pattern : Twelve) (guard : d1852 pattern = 1) : d1492 pattern ≤ (0 : Int) + d1354 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1492, d1354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6484 pattern childGuard
    simpa only [d1492, d1354, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1492, d1354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6503 pattern childGuard
    simpa only [d1492, d1354, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6505 (pattern : Twelve) (guard : d1852 pattern = 1) : d1650 pattern ≤ (0 : Int) + d1650 pattern := by
  omega
theorem c6506 (pattern : Twelve) (guard : d1852 pattern = 1) : d1730 pattern ≤ (0 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1730, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6315 pattern childGuard
    simpa only [d1730, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1730, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6505 pattern childGuard
    simpa only [d1730, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6507 (pattern : Twelve) (guard : d1852 pattern = 1) : d1731 pattern ≤ (0 : Int) + d1657 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1731, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6318 pattern childGuard
    simpa only [d1731, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1731, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6476 pattern childGuard
    simpa only [d1731, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6508 (pattern : Twelve) (guard : d1852 pattern = 1) : d1736 pattern ≤ (0 : Int) + d1660 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1736, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6506 pattern childGuard
    simpa only [d1736, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1736, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6507 pattern childGuard
    simpa only [d1736, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6509 (pattern : Twelve) (guard : d1852 pattern = 1) : d1653 pattern ≤ (0 : Int) + d1653 pattern := by
  omega
theorem c6510 (pattern : Twelve) (guard : d1852 pattern = 1) : d1732 pattern ≤ (0 : Int) + d1658 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1732, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6321 pattern childGuard
    simpa only [d1732, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1732, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6509 pattern childGuard
    simpa only [d1732, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6511 (pattern : Twelve) (guard : d1852 pattern = 1) : d1655 pattern ≤ (0 : Int) + d1655 pattern := by
  omega
theorem c6512 (pattern : Twelve) (guard : d1852 pattern = 1) : d1733 pattern ≤ (0 : Int) + d1659 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1733, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6324 pattern childGuard
    simpa only [d1733, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1733, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6511 pattern childGuard
    simpa only [d1733, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6513 (pattern : Twelve) (guard : d1852 pattern = 1) : d1737 pattern ≤ (0 : Int) + d1661 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1737, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6510 pattern childGuard
    simpa only [d1737, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1737, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6512 pattern childGuard
    simpa only [d1737, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6514 (pattern : Twelve) (guard : d1852 pattern = 1) : d1738 pattern ≤ (0 : Int) + d1662 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1738, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6507 pattern childGuard
    simpa only [d1738, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1738, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6359 pattern childGuard
    simpa only [d1738, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6515 (pattern : Twelve) (guard : d1852 pattern = 1) : d1740 pattern ≤ (0 : Int) + d1663 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1740, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6513 pattern childGuard
    simpa only [d1740, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1740, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6514 pattern childGuard
    simpa only [d1740, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6516 (pattern : Twelve) (guard : d1852 pattern = 1) : d1742 pattern ≤ (0 : Int) + d1664 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1742, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6508 pattern childGuard
    simpa only [d1742, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1742, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6515 pattern childGuard
    simpa only [d1742, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6517 (pattern : Twelve) (guard : d1852 pattern = 1) : d1294 pattern ≤ (0 : Int) + d1668 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1294, d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c328 pattern childGuard
    simpa only [d1852, d1294, d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1294, d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1114 pattern childGuard
    simpa only [d1852, d1294, d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6518 (pattern : Twelve) (guard : d1852 pattern = 1) : d1730 pattern ≤ (0 : Int) + d1671 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1730, d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6517 pattern childGuard
    simpa only [d1730, d1671, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1730, d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6505 pattern childGuard
    simpa only [d1730, d1671, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6519 (pattern : Twelve) (guard : d1852 pattern = 1) : d1736 pattern ≤ (0 : Int) + d1674 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1736, d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6518 pattern childGuard
    simpa only [d1736, d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1736, d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6507 pattern childGuard
    simpa only [d1736, d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6520 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1666 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6521 (pattern : Twelve) (guard : d1852 pattern = 1) : d1298 pattern ≤ (0 : Int) + d1669 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1298, d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c243 pattern childGuard
    simpa only [d1852, d1298, d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1298, d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6520 pattern childGuard
    simpa only [d1852, d1298, d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6522 (pattern : Twelve) (guard : d1852 pattern = 1) : d1734 pattern ≤ (0 : Int) + d1672 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1734, d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6521 pattern childGuard
    simpa only [d1734, d1672, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1734, d1672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6476 pattern childGuard
    simpa only [d1734, d1672, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6523 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1667 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6524 (pattern : Twelve) (guard : d1852 pattern = 1) : d1300 pattern ≤ (0 : Int) + d1670 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1852, d1300, d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2402 pattern childGuard
    simpa only [d1852, d1300, d1670, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1852, d1300, d1670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6523 pattern childGuard
    simpa only [d1852, d1300, d1670, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6525 (pattern : Twelve) (guard : d1852 pattern = 1) : d1626 pattern ≤ (0 : Int) + d1626 pattern := by
  omega
theorem c6526 (pattern : Twelve) (guard : d1852 pattern = 1) : d1735 pattern ≤ (0 : Int) + d1673 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1735, d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6524 pattern childGuard
    simpa only [d1735, d1673, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1735, d1673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6525 pattern childGuard
    simpa only [d1735, d1673, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6527 (pattern : Twelve) (guard : d1852 pattern = 1) : d1739 pattern ≤ (0 : Int) + d1675 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1739, d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6522 pattern childGuard
    simpa only [d1739, d1675, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1739, d1675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6526 pattern childGuard
    simpa only [d1739, d1675, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6528 (pattern : Twelve) (guard : d1852 pattern = 1) : d1741 pattern ≤ (0 : Int) + d1676 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1741, d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6527 pattern childGuard
    simpa only [d1741, d1676, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1741, d1676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6514 pattern childGuard
    simpa only [d1741, d1676, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6529 (pattern : Twelve) (guard : d1852 pattern = 1) : d1743 pattern ≤ (0 : Int) + d1677 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1743, d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6519 pattern childGuard
    simpa only [d1743, d1677, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1743, d1677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6528 pattern childGuard
    simpa only [d1743, d1677, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6530 (pattern : Twelve) (guard : d1852 pattern = 1) : d1744 pattern ≤ (0 : Int) + d1678 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1744, d1678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6516 pattern childGuard
    simpa only [d1744, d1678, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1852 pattern = 1 := by simpa only [d1744, d1678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6529 pattern childGuard
    simpa only [d1744, d1678, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6531 (pattern : Twelve) (guard : d0 pattern = 1) : d185 pattern ≤ (0 : Int) + d372 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6532 (pattern : Twelve) (guard : d1870 pattern = 1) : d425 pattern ≤ (0 : Int) + d389 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d425, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2546 pattern childGuard
    simpa only [d1870, d425, d389, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d425, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6531 pattern childGuard
    simpa only [d1870, d425, d389, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6533 (pattern : Twelve) (guard : d0 pattern = 1) : d186 pattern ≤ (0 : Int) + d374 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6534 (pattern : Twelve) (guard : d1870 pattern = 1) : d426 pattern ≤ (0 : Int) + d390 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d426, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2664 pattern childGuard
    simpa only [d1870, d426, d390, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d426, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6533 pattern childGuard
    simpa only [d1870, d426, d390, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6535 (pattern : Twelve) (guard : d1870 pattern = 1) : d444 pattern ≤ (0 : Int) + d402 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d444, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6532 pattern childGuard
    simpa only [d444, d402, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d444, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6534 pattern childGuard
    simpa only [d444, d402, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6536 (pattern : Twelve) (guard : d0 pattern = 1) : d188 pattern ≤ (0 : Int) + d376 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6537 (pattern : Twelve) (guard : d1870 pattern = 1) : d427 pattern ≤ (0 : Int) + d391 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d427, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2554 pattern childGuard
    simpa only [d1870, d427, d391, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d427, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6536 pattern childGuard
    simpa only [d1870, d427, d391, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6538 (pattern : Twelve) (guard : d1848 pattern = 1) : d33 pattern ≤ (0 : Int) + d35 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d33, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d33, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d33, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1537 pattern childGuard
    simpa only [d1848, d33, d35, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6539 (pattern : Twelve) (guard : d1848 pattern = 1) : d54 pattern ≤ (0 : Int) + d377 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d54, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1285 pattern childGuard
    simpa only [d54, d377, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d54, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6538 pattern childGuard
    simpa only [d54, d377, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6540 (pattern : Twelve) (guard : d0 pattern = 1) : d189 pattern ≤ (0 : Int) + d378 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6541 (pattern : Twelve) (guard : d1870 pattern = 1) : d428 pattern ≤ (0 : Int) + d392 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d428, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6539 pattern childGuard
    simpa only [d1870, d428, d392, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d428, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6540 pattern childGuard
    simpa only [d1870, d428, d392, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6542 (pattern : Twelve) (guard : d1870 pattern = 1) : d445 pattern ≤ (0 : Int) + d403 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d445, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6537 pattern childGuard
    simpa only [d445, d403, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d445, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6541 pattern childGuard
    simpa only [d445, d403, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6543 (pattern : Twelve) (guard : d1870 pattern = 1) : d455 pattern ≤ (0 : Int) + d409 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d455, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6535 pattern childGuard
    simpa only [d455, d409, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d455, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6542 pattern childGuard
    simpa only [d455, d409, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6544 (pattern : Twelve) (guard : d1870 pattern = 1) : d429 pattern ≤ (0 : Int) + d391 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d429, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2561 pattern childGuard
    simpa only [d1870, d429, d391, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d429, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6536 pattern childGuard
    simpa only [d1870, d429, d391, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6545 (pattern : Twelve) (guard : d1870 pattern = 1) : d430 pattern ≤ (0 : Int) + d392 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d430, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2677 pattern childGuard
    simpa only [d1870, d430, d392, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d430, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6540 pattern childGuard
    simpa only [d1870, d430, d392, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6546 (pattern : Twelve) (guard : d1870 pattern = 1) : d446 pattern ≤ (0 : Int) + d403 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d446, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6544 pattern childGuard
    simpa only [d446, d403, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d446, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6545 pattern childGuard
    simpa only [d446, d403, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6547 (pattern : Twelve) (guard : d0 pattern = 1) : d191 pattern ≤ (0 : Int) + d380 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6548 (pattern : Twelve) (guard : d1870 pattern = 1) : d431 pattern ≤ (0 : Int) + d393 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d431, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2567 pattern childGuard
    simpa only [d1870, d431, d393, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d431, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6547 pattern childGuard
    simpa only [d1870, d431, d393, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6549 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d378 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6550 (pattern : Twelve) (guard : d1870 pattern = 1) : d432 pattern ≤ (0 : Int) + d394 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d432, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2589 pattern childGuard
    simpa only [d1870, d432, d394, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d432, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6549 pattern childGuard
    simpa only [d1870, d432, d394, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6551 (pattern : Twelve) (guard : d1870 pattern = 1) : d447 pattern ≤ (0 : Int) + d404 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d447, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6548 pattern childGuard
    simpa only [d447, d404, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d447, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6550 pattern childGuard
    simpa only [d447, d404, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6552 (pattern : Twelve) (guard : d1870 pattern = 1) : d456 pattern ≤ (0 : Int) + d410 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d456, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6546 pattern childGuard
    simpa only [d456, d410, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d456, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6551 pattern childGuard
    simpa only [d456, d410, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6553 (pattern : Twelve) (guard : d1870 pattern = 1) : d465 pattern ≤ (0 : Int) + d415 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d465, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6543 pattern childGuard
    simpa only [d465, d415, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d465, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6552 pattern childGuard
    simpa only [d465, d415, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6554 (pattern : Twelve) (guard : d0 pattern = 1) : d193 pattern ≤ (0 : Int) + d382 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6555 (pattern : Twelve) (guard : d1870 pattern = 1) : d433 pattern ≤ (0 : Int) + d395 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d433, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2575 pattern childGuard
    simpa only [d1870, d433, d395, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d433, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6554 pattern childGuard
    simpa only [d1870, d433, d395, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6556 (pattern : Twelve) (guard : d0 pattern = 1) : d194 pattern ≤ (0 : Int) + d378 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6557 (pattern : Twelve) (guard : d1870 pattern = 1) : d434 pattern ≤ (0 : Int) + d396 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d434, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2686 pattern childGuard
    simpa only [d1870, d434, d396, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d434, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6556 pattern childGuard
    simpa only [d1870, d434, d396, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6558 (pattern : Twelve) (guard : d1870 pattern = 1) : d448 pattern ≤ (0 : Int) + d405 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d448, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6555 pattern childGuard
    simpa only [d448, d405, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d448, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6557 pattern childGuard
    simpa only [d448, d405, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6559 (pattern : Twelve) (guard : d0 pattern = 1) : d196 pattern ≤ (0 : Int) + d384 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6560 (pattern : Twelve) (guard : d1870 pattern = 1) : d435 pattern ≤ (0 : Int) + d397 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d435, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2582 pattern childGuard
    simpa only [d1870, d435, d397, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d435, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6559 pattern childGuard
    simpa only [d1870, d435, d397, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6561 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d385 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6562 (pattern : Twelve) (guard : d1870 pattern = 1) : d436 pattern ≤ (0 : Int) + d398 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d436, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2582 pattern childGuard
    simpa only [d1870, d436, d398, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d436, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6561 pattern childGuard
    simpa only [d1870, d436, d398, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6563 (pattern : Twelve) (guard : d1870 pattern = 1) : d449 pattern ≤ (0 : Int) + d406 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d449, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6560 pattern childGuard
    simpa only [d449, d406, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d449, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6562 pattern childGuard
    simpa only [d449, d406, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6564 (pattern : Twelve) (guard : d1870 pattern = 1) : d457 pattern ≤ (0 : Int) + d411 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d457, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6558 pattern childGuard
    simpa only [d457, d411, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d457, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6563 pattern childGuard
    simpa only [d457, d411, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6565 (pattern : Twelve) (guard : d0 pattern = 1) : d196 pattern ≤ (0 : Int) + d380 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6566 (pattern : Twelve) (guard : d1870 pattern = 1) : d437 pattern ≤ (0 : Int) + d399 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d437, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2589 pattern childGuard
    simpa only [d1870, d437, d399, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d437, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6565 pattern childGuard
    simpa only [d1870, d437, d399, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6567 (pattern : Twelve) (guard : d1870 pattern = 1) : d450 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d450, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6566 pattern childGuard
    simpa only [d450, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d450, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6550 pattern childGuard
    simpa only [d450, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6568 (pattern : Twelve) (guard : d1870 pattern = 1) : d458 pattern ≤ (0 : Int) + d412 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d458, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6567 pattern childGuard
    simpa only [d458, d412, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d458, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5294 pattern childGuard
    simpa only [d458, d412, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6569 (pattern : Twelve) (guard : d1870 pattern = 1) : d466 pattern ≤ (0 : Int) + d416 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d466, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6564 pattern childGuard
    simpa only [d466, d416, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d466, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6568 pattern childGuard
    simpa only [d466, d416, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6570 (pattern : Twelve) (guard : d1870 pattern = 1) : d471 pattern ≤ (0 : Int) + d419 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d471, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6553 pattern childGuard
    simpa only [d471, d419, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d471, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6569 pattern childGuard
    simpa only [d471, d419, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6571 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d380 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c6572 (pattern : Twelve) (guard : d1870 pattern = 1) : d438 pattern ≤ (0 : Int) + d399 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d438, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1354 pattern childGuard
    simpa only [d1870, d438, d399, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d438, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6571 pattern childGuard
    simpa only [d1870, d438, d399, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6573 (pattern : Twelve) (guard : d1870 pattern = 1) : d438 pattern ≤ (0 : Int) + d394 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d438, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1354 pattern childGuard
    simpa only [d1870, d438, d394, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d438, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6549 pattern childGuard
    simpa only [d1870, d438, d394, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6574 (pattern : Twelve) (guard : d1870 pattern = 1) : d438 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6572 pattern childGuard
    simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6573 pattern childGuard
    simpa only [d407, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6575 (pattern : Twelve) (guard : d1870 pattern = 1) : d439 pattern ≤ (0 : Int) + d399 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d439, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2602 pattern childGuard
    simpa only [d1870, d439, d399, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d439, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6571 pattern childGuard
    simpa only [d1870, d439, d399, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6576 (pattern : Twelve) (guard : d1848 pattern = 1) : d54 pattern ≤ (0 : Int) + d35 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1312 pattern childGuard
    simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6538 pattern childGuard
    simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6577 (pattern : Twelve) (guard : d1870 pattern = 1) : d440 pattern ≤ (0 : Int) + d394 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d440, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6576 pattern childGuard
    simpa only [d1870, d440, d394, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d440, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6549 pattern childGuard
    simpa only [d1870, d440, d394, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6578 (pattern : Twelve) (guard : d1870 pattern = 1) : d451 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d451, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6575 pattern childGuard
    simpa only [d451, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d451, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6577 pattern childGuard
    simpa only [d451, d407, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c6579 (pattern : Twelve) (guard : d1870 pattern = 1) : d459 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6574 pattern childGuard
    simpa only [d459, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6578 pattern childGuard
    simpa only [d459, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
