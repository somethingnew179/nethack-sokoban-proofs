/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons155
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c21840 (pattern : Twelve) (guard : d1 pattern = 1) : d852 pattern ≤ (18 : Int) + d1304 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d852, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21839 pattern childGuard
    simpa only [d852, d1304, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d852, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21814 pattern childGuard
    simpa only [d852, d1304, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21841 (pattern : Twelve) (guard : d1 pattern = 1) : d860 pattern ≤ (18 : Int) + d1312 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d860, d1312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21838 pattern childGuard
    simpa only [d860, d1312, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d860, d1312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21840 pattern childGuard
    simpa only [d860, d1312, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21842 (pattern : Twelve) (guard : d1 pattern = 1) : d865 pattern ≤ (18 : Int) + d1317 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d865, d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21836 pattern childGuard
    simpa only [d865, d1317, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d865, d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21841 pattern childGuard
    simpa only [d865, d1317, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21843 (pattern : Twelve) (guard : d1 pattern = 1) : d866 pattern ≤ (18 : Int) + d1318 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d866, d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21829 pattern childGuard
    simpa only [d866, d1318, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d866, d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d866, d1318, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21844 (pattern : Twelve) (guard : d1 pattern = 1) : d868 pattern ≤ (18 : Int) + d1320 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d868, d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21842 pattern childGuard
    simpa only [d868, d1320, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d868, d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21843 pattern childGuard
    simpa only [d868, d1320, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21845 (pattern : Twelve) (guard : d1 pattern = 1) : d870 pattern ≤ (18 : Int) + d1322 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d870, d1322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21830 pattern childGuard
    simpa only [d870, d1322, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d870, d1322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21844 pattern childGuard
    simpa only [d870, d1322, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21846 (pattern : Twelve) (guard : d1 pattern = 1) : d871 pattern ≤ (18 : Int) + d1323 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d871, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21820 pattern childGuard
    simpa only [d871, d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d871, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21845 pattern childGuard
    simpa only [d871, d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21847 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (18 : Int) + d11 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21541 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21550 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21848 (pattern : Twelve) (guard : d1 pattern = 1) : d872 pattern ≤ (18 : Int) + d1324 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21847 pattern childGuard
    simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21555 pattern childGuard
    simpa only [d872, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21849 (pattern : Twelve) (guard : d1 pattern = 1) : d874 pattern ≤ (18 : Int) + d1325 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d874, d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21770 pattern childGuard
    simpa only [d874, d1325, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d874, d1325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21848 pattern childGuard
    simpa only [d874, d1325, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21850 (pattern : Twelve) (guard : d1 pattern = 1) : d875 pattern ≤ (18 : Int) + d1326 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d875, d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21772 pattern childGuard
    simpa only [d875, d1326, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d875, d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21848 pattern childGuard
    simpa only [d875, d1326, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21851 (pattern : Twelve) (guard : d1 pattern = 1) : d882 pattern ≤ (18 : Int) + d1333 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d882, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21849 pattern childGuard
    simpa only [d882, d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d882, d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21850 pattern childGuard
    simpa only [d882, d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21852 (pattern : Twelve) (guard : d1 pattern = 1) : d890 pattern ≤ (18 : Int) + d1339 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d890, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21540 pattern childGuard
    simpa only [d890, d1339, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d890, d1339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21851 pattern childGuard
    simpa only [d890, d1339, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21853 (pattern : Twelve) (guard : d1 pattern = 1) : d876 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21781 pattern childGuard
    simpa only [d876, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21583 pattern childGuard
    simpa only [d876, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21854 (pattern : Twelve) (guard : d1 pattern = 1) : d883 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21853 pattern childGuard
    simpa only [d883, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21785 pattern childGuard
    simpa only [d883, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21855 (pattern : Twelve) (guard : d1 pattern = 1) : d891 pattern ≤ (18 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d891, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21552 pattern childGuard
    simpa only [d891, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d891, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21854 pattern childGuard
    simpa only [d891, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21856 (pattern : Twelve) (guard : d1 pattern = 1) : d898 pattern ≤ (18 : Int) + d1345 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d898, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21852 pattern childGuard
    simpa only [d898, d1345, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d898, d1345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21855 pattern childGuard
    simpa only [d898, d1345, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21857 (pattern : Twelve) (guard : d1 pattern = 1) : d877 pattern ≤ (18 : Int) + d1327 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d877, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21770 pattern childGuard
    simpa only [d877, d1327, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d877, d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21807 pattern childGuard
    simpa only [d877, d1327, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21858 (pattern : Twelve) (guard : d1 pattern = 1) : d884 pattern ≤ (18 : Int) + d1334 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d884, d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21857 pattern childGuard
    simpa only [d884, d1334, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d884, d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21792 pattern childGuard
    simpa only [d884, d1334, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21859 (pattern : Twelve) (guard : d1 pattern = 1) : d892 pattern ≤ (18 : Int) + d1340 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d892, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21604 pattern childGuard
    simpa only [d892, d1340, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d892, d1340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21858 pattern childGuard
    simpa only [d892, d1340, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21860 (pattern : Twelve) (guard : d1 pattern = 1) : d893 pattern ≤ (18 : Int) + d1296 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d893, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21796 pattern childGuard
    simpa only [d893, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d893, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21854 pattern childGuard
    simpa only [d893, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21861 (pattern : Twelve) (guard : d1 pattern = 1) : d899 pattern ≤ (18 : Int) + d1346 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d899, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21859 pattern childGuard
    simpa only [d899, d1346, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d899, d1346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21860 pattern childGuard
    simpa only [d899, d1346, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21862 (pattern : Twelve) (guard : d1 pattern = 1) : d902 pattern ≤ (18 : Int) + d1349 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d902, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21856 pattern childGuard
    simpa only [d902, d1349, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d902, d1349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21861 pattern childGuard
    simpa only [d902, d1349, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21863 (pattern : Twelve) (guard : d1 pattern = 1) : d878 pattern ≤ (18 : Int) + d1328 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d878, d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21772 pattern childGuard
    simpa only [d878, d1328, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d878, d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21805 pattern childGuard
    simpa only [d878, d1328, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21864 (pattern : Twelve) (guard : d1 pattern = 1) : d885 pattern ≤ (18 : Int) + d1335 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d885, d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21857 pattern childGuard
    simpa only [d885, d1335, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d885, d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21863 pattern childGuard
    simpa only [d885, d1335, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21865 (pattern : Twelve) (guard : d1 pattern = 1) : d894 pattern ≤ (18 : Int) + d1341 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d894, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21581 pattern childGuard
    simpa only [d894, d1341, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d894, d1341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21864 pattern childGuard
    simpa only [d894, d1341, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21866 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (18 : Int) + d12 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21609 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21557 pattern childGuard
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21867 (pattern : Twelve) (guard : d1 pattern = 1) : d117 pattern ≤ (18 : Int) + d13 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21709 pattern childGuard
    simpa only [d117, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21573 pattern childGuard
    simpa only [d117, d13, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21868 (pattern : Twelve) (guard : d1 pattern = 1) : d119 pattern ≤ (18 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21866 pattern childGuard
    simpa only [d119, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21867 pattern childGuard
    simpa only [d119, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21869 (pattern : Twelve) (guard : d1 pattern = 1) : d879 pattern ≤ (18 : Int) + d1329 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d879, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21552 pattern childGuard
    simpa only [d879, d1329, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d879, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21868 pattern childGuard
    simpa only [d879, d1329, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21870 (pattern : Twelve) (guard : d1 pattern = 1) : d886 pattern ≤ (18 : Int) + d1336 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d886, d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21592 pattern childGuard
    simpa only [d886, d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d886, d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21869 pattern childGuard
    simpa only [d886, d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21871 (pattern : Twelve) (guard : d1 pattern = 1) : d895 pattern ≤ (18 : Int) + d1342 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d895, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21870 pattern childGuard
    simpa only [d895, d1342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d895, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21854 pattern childGuard
    simpa only [d895, d1342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21872 (pattern : Twelve) (guard : d1 pattern = 1) : d900 pattern ≤ (18 : Int) + d1347 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d900, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21865 pattern childGuard
    simpa only [d900, d1347, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d900, d1347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21871 pattern childGuard
    simpa only [d900, d1347, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21873 (pattern : Twelve) (guard : d1 pattern = 1) : d127 pattern ≤ (18 : Int) + d1330 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d127, d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21790 pattern childGuard
    simpa only [d127, d1330, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d127, d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21587 pattern childGuard
    simpa only [d127, d1330, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21874 (pattern : Twelve) (guard : d1 pattern = 1) : d873 pattern ≤ (18 : Int) + d1277 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d873, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21720 pattern childGuard
    simpa only [d873, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d873, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21629 pattern childGuard
    simpa only [d873, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21875 (pattern : Twelve) (guard : d1 pattern = 1) : d880 pattern ≤ (18 : Int) + d1331 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d880, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21874 pattern childGuard
    simpa only [d880, d1331, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d880, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d880, d1331, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21876 (pattern : Twelve) (guard : d1 pattern = 1) : d887 pattern ≤ (18 : Int) + d1337 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d887, d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21873 pattern childGuard
    simpa only [d887, d1337, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d887, d1337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21875 pattern childGuard
    simpa only [d887, d1337, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21877 (pattern : Twelve) (guard : d1 pattern = 1) : d896 pattern ≤ (18 : Int) + d1343 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d896, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21627 pattern childGuard
    simpa only [d896, d1343, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d896, d1343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21876 pattern childGuard
    simpa only [d896, d1343, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21878 (pattern : Twelve) (guard : d1 pattern = 1) : d881 pattern ≤ (18 : Int) + d1332 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d881, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21591 pattern childGuard
    simpa only [d881, d1332, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d881, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21718 pattern childGuard
    simpa only [d881, d1332, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21879 (pattern : Twelve) (guard : d1 pattern = 1) : d125 pattern ≤ (18 : Int) + d128 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21868 pattern childGuard
    simpa only [d125, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d125, d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21880 (pattern : Twelve) (guard : d1 pattern = 1) : d888 pattern ≤ (18 : Int) + d1338 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d888, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21878 pattern childGuard
    simpa only [d888, d1338, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d888, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21879 pattern childGuard
    simpa only [d888, d1338, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21881 (pattern : Twelve) (guard : d1 pattern = 1) : d889 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21785 pattern childGuard
    simpa only [d889, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d889, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21882 (pattern : Twelve) (guard : d1 pattern = 1) : d897 pattern ≤ (18 : Int) + d1344 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d897, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21880 pattern childGuard
    simpa only [d897, d1344, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d897, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21881 pattern childGuard
    simpa only [d897, d1344, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21883 (pattern : Twelve) (guard : d1 pattern = 1) : d901 pattern ≤ (18 : Int) + d1348 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d901, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21877 pattern childGuard
    simpa only [d901, d1348, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d901, d1348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21882 pattern childGuard
    simpa only [d901, d1348, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21884 (pattern : Twelve) (guard : d1 pattern = 1) : d903 pattern ≤ (18 : Int) + d1350 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d903, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21872 pattern childGuard
    simpa only [d903, d1350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d903, d1350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21883 pattern childGuard
    simpa only [d903, d1350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21885 (pattern : Twelve) (guard : d1 pattern = 1) : d904 pattern ≤ (18 : Int) + d1351 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d904, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21861 pattern childGuard
    simpa only [d904, d1351, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d904, d1351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d904, d1351, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21886 (pattern : Twelve) (guard : d1 pattern = 1) : d905 pattern ≤ (18 : Int) + d1352 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d905, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21884 pattern childGuard
    simpa only [d905, d1352, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d905, d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21885 pattern childGuard
    simpa only [d905, d1352, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21887 (pattern : Twelve) (guard : d1 pattern = 1) : d906 pattern ≤ (18 : Int) + d1353 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d906, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21862 pattern childGuard
    simpa only [d906, d1353, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d906, d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21886 pattern childGuard
    simpa only [d906, d1353, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21888 (pattern : Twelve) (guard : d1 pattern = 1) : d779 pattern ≤ (18 : Int) + d1616 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d779, d1616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21790 pattern childGuard
    simpa only [d779, d1616, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d779, d1616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21711 pattern childGuard
    simpa only [d779, d1616, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21889 (pattern : Twelve) (guard : d1 pattern = 1) : d1247 pattern ≤ (18 : Int) + d119 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21807 pattern childGuard
    simpa only [d1247, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21711 pattern childGuard
    simpa only [d1247, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21890 (pattern : Twelve) (guard : d1 pattern = 1) : d1249 pattern ≤ (18 : Int) + d1619 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1249, d1619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21888 pattern childGuard
    simpa only [d1249, d1619, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1249, d1619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21889 pattern childGuard
    simpa only [d1249, d1619, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21891 (pattern : Twelve) (guard : d1 pattern = 1) : d1253 pattern ≤ (18 : Int) + d1622 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1253, d1622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21580 pattern childGuard
    simpa only [d1253, d1622, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1253, d1622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21890 pattern childGuard
    simpa only [d1253, d1622, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21892 (pattern : Twelve) (guard : d1 pattern = 1) : d1248 pattern ≤ (18 : Int) + d1617 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1248, d1617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21591 pattern childGuard
    simpa only [d1248, d1617, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1248, d1617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21619 pattern childGuard
    simpa only [d1248, d1617, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21893 (pattern : Twelve) (guard : d1 pattern = 1) : d1254 pattern ≤ (18 : Int) + d1623 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1254, d1623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21892 pattern childGuard
    simpa only [d1254, d1623, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1254, d1623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21814 pattern childGuard
    simpa only [d1254, d1623, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21894 (pattern : Twelve) (guard : d1 pattern = 1) : d1258 pattern ≤ (18 : Int) + d1627 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1258, d1627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21891 pattern childGuard
    simpa only [d1258, d1627, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1258, d1627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21893 pattern childGuard
    simpa only [d1258, d1627, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21895 (pattern : Twelve) (guard : d1 pattern = 1) : d1261 pattern ≤ (18 : Int) + d1630 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1261, d1630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21894 pattern childGuard
    simpa only [d1261, d1630, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1261, d1630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21841 pattern childGuard
    simpa only [d1261, d1630, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21896 (pattern : Twelve) (guard : d1 pattern = 1) : d780 pattern ≤ (18 : Int) + d1618 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d780, d1618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21711 pattern childGuard
    simpa only [d780, d1618, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d780, d1618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21725 pattern childGuard
    simpa only [d780, d1618, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21897 (pattern : Twelve) (guard : d1 pattern = 1) : d1250 pattern ≤ (18 : Int) + d1620 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1250, d1620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21806 pattern childGuard
    simpa only [d1250, d1620, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1250, d1620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21896 pattern childGuard
    simpa only [d1250, d1620, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21898 (pattern : Twelve) (guard : d1 pattern = 1) : d1255 pattern ≤ (18 : Int) + d1624 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1255, d1624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21620 pattern childGuard
    simpa only [d1255, d1624, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1255, d1624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21897 pattern childGuard
    simpa only [d1255, d1624, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21899 (pattern : Twelve) (guard : d1 pattern = 1) : d1259 pattern ≤ (18 : Int) + d1628 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1259, d1628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21898 pattern childGuard
    simpa only [d1259, d1628, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1259, d1628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21840 pattern childGuard
    simpa only [d1259, d1628, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21900 (pattern : Twelve) (guard : d1 pattern = 1) : d49 pattern ≤ (18 : Int) + d1331 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d49, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21805 pattern childGuard
    simpa only [d49, d1331, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d49, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d49, d1331, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21901 (pattern : Twelve) (guard : d1 pattern = 1) : d781 pattern ≤ (18 : Int) + d182 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d781, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21725 pattern childGuard
    simpa only [d781, d182, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d781, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d781, d182, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21902 (pattern : Twelve) (guard : d1 pattern = 1) : d1251 pattern ≤ (18 : Int) + d1621 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1251, d1621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21900 pattern childGuard
    simpa only [d1251, d1621, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1251, d1621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21901 pattern childGuard
    simpa only [d1251, d1621, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21903 (pattern : Twelve) (guard : d1 pattern = 1) : d1256 pattern ≤ (18 : Int) + d1625 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1256, d1625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21755 pattern childGuard
    simpa only [d1256, d1625, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1256, d1625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21902 pattern childGuard
    simpa only [d1256, d1625, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21904 (pattern : Twelve) (guard : d1 pattern = 1) : d1252 pattern ≤ (18 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21813 pattern childGuard
    simpa only [d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21905 (pattern : Twelve) (guard : d1 pattern = 1) : d1257 pattern ≤ (18 : Int) + d1626 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1257, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21760 pattern childGuard
    simpa only [d1257, d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1257, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21904 pattern childGuard
    simpa only [d1257, d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21906 (pattern : Twelve) (guard : d1 pattern = 1) : d1260 pattern ≤ (18 : Int) + d1629 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1260, d1629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21903 pattern childGuard
    simpa only [d1260, d1629, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1260, d1629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21905 pattern childGuard
    simpa only [d1260, d1629, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21907 (pattern : Twelve) (guard : d1 pattern = 1) : d1262 pattern ≤ (18 : Int) + d1631 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1262, d1631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21899 pattern childGuard
    simpa only [d1262, d1631, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1262, d1631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21906 pattern childGuard
    simpa only [d1262, d1631, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21908 (pattern : Twelve) (guard : d1 pattern = 1) : d1263 pattern ≤ (18 : Int) + d1632 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1263, d1632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21841 pattern childGuard
    simpa only [d1263, d1632, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1263, d1632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d1263, d1632, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21909 (pattern : Twelve) (guard : d1 pattern = 1) : d1264 pattern ≤ (18 : Int) + d1633 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1264, d1633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21907 pattern childGuard
    simpa only [d1264, d1633, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1264, d1633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21908 pattern childGuard
    simpa only [d1264, d1633, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21910 (pattern : Twelve) (guard : d1 pattern = 1) : d1265 pattern ≤ (18 : Int) + d1634 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1265, d1634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21895 pattern childGuard
    simpa only [d1265, d1634, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1265, d1634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21909 pattern childGuard
    simpa only [d1265, d1634, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21911 (pattern : Twelve) (guard : d1 pattern = 1) : d1266 pattern ≤ (18 : Int) + d1635 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1266, d1635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21887 pattern childGuard
    simpa only [d1266, d1635, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1266, d1635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21910 pattern childGuard
    simpa only [d1266, d1635, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21912 (pattern : Twelve) (guard : d1 pattern = 1) : d1267 pattern ≤ (18 : Int) + d1636 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1267, d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21846 pattern childGuard
    simpa only [d1267, d1636, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1267, d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21911 pattern childGuard
    simpa only [d1267, d1636, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21913 (pattern : Twelve) (guard : d1 pattern = 1) : d1275 pattern ≤ (18 : Int) + d1324 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1275, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21551 pattern childGuard
    simpa only [d1275, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1275, d1324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21555 pattern childGuard
    simpa only [d1275, d1324, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21914 (pattern : Twelve) (guard : d1 pattern = 1) : d1278 pattern ≤ (18 : Int) + d1324 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21913 pattern childGuard
    simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21848 pattern childGuard
    simpa only [d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21915 (pattern : Twelve) (guard : d1 pattern = 1) : d1284 pattern ≤ (18 : Int) + d1324 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21914 pattern childGuard
    simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21848 pattern childGuard
    simpa only [d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21916 (pattern : Twelve) (guard : d1 pattern = 1) : d1293 pattern ≤ (18 : Int) + d1649 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1293, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21552 pattern childGuard
    simpa only [d1293, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1293, d1649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21915 pattern childGuard
    simpa only [d1293, d1649, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21917 (pattern : Twelve) (guard : d1 pattern = 1) : d1294 pattern ≤ (18 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1294, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21563 pattern childGuard
    simpa only [d1294, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1294, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d1294, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21918 (pattern : Twelve) (guard : d1 pattern = 1) : d1305 pattern ≤ (18 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1305, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21916 pattern childGuard
    simpa only [d1305, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1305, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21917 pattern childGuard
    simpa only [d1305, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21919 (pattern : Twelve) (guard : d1 pattern = 1) : d1276 pattern ≤ (18 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21558 pattern childGuard
    simpa only [d1276, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1276, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21867 pattern childGuard
    simpa only [d1276, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21920 (pattern : Twelve) (guard : d1 pattern = 1) : d1279 pattern ≤ (18 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1279, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21913 pattern childGuard
    simpa only [d1279, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1279, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21919 pattern childGuard
    simpa only [d1279, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21921 (pattern : Twelve) (guard : d1 pattern = 1) : d1280 pattern ≤ (18 : Int) + d1645 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1280, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21848 pattern childGuard
    simpa only [d1280, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1280, d1645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d1280, d1645, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21922 (pattern : Twelve) (guard : d1 pattern = 1) : d1285 pattern ≤ (18 : Int) + d1647 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1285, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21920 pattern childGuard
    simpa only [d1285, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1285, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21921 pattern childGuard
    simpa only [d1285, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21923 (pattern : Twelve) (guard : d1 pattern = 1) : d1295 pattern ≤ (18 : Int) + d1651 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1295, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21796 pattern childGuard
    simpa only [d1295, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1295, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21922 pattern childGuard
    simpa only [d1295, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21924 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (18 : Int) + d821 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21563 pattern childGuard
    simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21634 pattern childGuard
    simpa only [d817, d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21925 (pattern : Twelve) (guard : d1 pattern = 1) : d1286 pattern ≤ (18 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21924 pattern childGuard
    simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21565 pattern childGuard
    simpa only [d1286, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21926 (pattern : Twelve) (guard : d1 pattern = 1) : d1296 pattern ≤ (18 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1296, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21925 pattern childGuard
    simpa only [d1296, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1296, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d1296, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21927 (pattern : Twelve) (guard : d1 pattern = 1) : d1306 pattern ≤ (18 : Int) + d1657 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1306, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21923 pattern childGuard
    simpa only [d1306, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1306, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21926 pattern childGuard
    simpa only [d1306, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21928 (pattern : Twelve) (guard : d1 pattern = 1) : d1313 pattern ≤ (18 : Int) + d1660 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1313, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21918 pattern childGuard
    simpa only [d1313, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1313, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21927 pattern childGuard
    simpa only [d1313, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21929 (pattern : Twelve) (guard : d1 pattern = 1) : d1281 pattern ≤ (18 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1281, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21848 pattern childGuard
    simpa only [d1281, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1281, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21868 pattern childGuard
    simpa only [d1281, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21930 (pattern : Twelve) (guard : d1 pattern = 1) : d1287 pattern ≤ (18 : Int) + d1644 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21920 pattern childGuard
    simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21929 pattern childGuard
    simpa only [d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21931 (pattern : Twelve) (guard : d1 pattern = 1) : d1297 pattern ≤ (18 : Int) + d1652 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1297, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21592 pattern childGuard
    simpa only [d1297, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1297, d1652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21930 pattern childGuard
    simpa only [d1297, d1652, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21932 (pattern : Twelve) (guard : d1 pattern = 1) : d1298 pattern ≤ (18 : Int) + d1653 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1298, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21924 pattern childGuard
    simpa only [d1298, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1298, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d1298, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21933 (pattern : Twelve) (guard : d1 pattern = 1) : d1307 pattern ≤ (18 : Int) + d1658 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1307, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21931 pattern childGuard
    simpa only [d1307, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1307, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21932 pattern childGuard
    simpa only [d1307, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21934 (pattern : Twelve) (guard : d1 pattern = 1) : d1277 pattern ≤ (18 : Int) + d22 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21629 pattern childGuard
    simpa only [d1277, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1277, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21582 pattern childGuard
    simpa only [d1277, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21935 (pattern : Twelve) (guard : d1 pattern = 1) : d1282 pattern ≤ (18 : Int) + d1646 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1282, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21919 pattern childGuard
    simpa only [d1282, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1282, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21934 pattern childGuard
    simpa only [d1282, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21936 (pattern : Twelve) (guard : d1 pattern = 1) : d1288 pattern ≤ (18 : Int) + d1648 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1288, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21935 pattern childGuard
    simpa only [d1288, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1288, d1648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21879 pattern childGuard
    simpa only [d1288, d1648, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21937 (pattern : Twelve) (guard : d1 pattern = 1) : d1299 pattern ≤ (18 : Int) + d1654 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1299, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21811 pattern childGuard
    simpa only [d1299, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1299, d1654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21936 pattern childGuard
    simpa only [d1299, d1654, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21938 (pattern : Twelve) (guard : d1 pattern = 1) : d821 pattern ≤ (18 : Int) + d822 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21634 pattern childGuard
    simpa only [d821, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21583 pattern childGuard
    simpa only [d821, d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21939 (pattern : Twelve) (guard : d1 pattern = 1) : d1289 pattern ≤ (18 : Int) + d822 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21938 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21635 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21940 (pattern : Twelve) (guard : d1 pattern = 1) : d1300 pattern ≤ (18 : Int) + d1655 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21939 pattern childGuard
    simpa only [d1300, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1300, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d1300, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21941 (pattern : Twelve) (guard : d1 pattern = 1) : d1308 pattern ≤ (18 : Int) + d1659 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1308, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21937 pattern childGuard
    simpa only [d1308, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1308, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21940 pattern childGuard
    simpa only [d1308, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21942 (pattern : Twelve) (guard : d1 pattern = 1) : d1314 pattern ≤ (18 : Int) + d1661 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1314, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21933 pattern childGuard
    simpa only [d1314, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1314, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21941 pattern childGuard
    simpa only [d1314, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21943 (pattern : Twelve) (guard : d1 pattern = 1) : d1315 pattern ≤ (18 : Int) + d1662 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1315, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21927 pattern childGuard
    simpa only [d1315, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1315, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d1315, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21944 (pattern : Twelve) (guard : d1 pattern = 1) : d1319 pattern ≤ (18 : Int) + d1663 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1319, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21942 pattern childGuard
    simpa only [d1319, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1319, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21943 pattern childGuard
    simpa only [d1319, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21945 (pattern : Twelve) (guard : d1 pattern = 1) : d1321 pattern ≤ (18 : Int) + d1664 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1321, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21928 pattern childGuard
    simpa only [d1321, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1321, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21944 pattern childGuard
    simpa only [d1321, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21946 (pattern : Twelve) (guard : d1 pattern = 1) : d1283 pattern ≤ (18 : Int) + d25 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21563 pattern childGuard
    simpa only [d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21591 pattern childGuard
    simpa only [d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21947 (pattern : Twelve) (guard : d1 pattern = 1) : d1301 pattern ≤ (18 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1301, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21946 pattern childGuard
    simpa only [d1301, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1301, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d1301, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21948 (pattern : Twelve) (guard : d1 pattern = 1) : d1309 pattern ≤ (18 : Int) + d1656 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1309, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21916 pattern childGuard
    simpa only [d1309, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1309, d1656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21947 pattern childGuard
    simpa only [d1309, d1656, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21949 (pattern : Twelve) (guard : d1 pattern = 1) : d1290 pattern ≤ (18 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1290, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21924 pattern childGuard
    simpa only [d1290, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1290, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21651 pattern childGuard
    simpa only [d1290, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21950 (pattern : Twelve) (guard : d1 pattern = 1) : d1302 pattern ≤ (18 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1302, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21949 pattern childGuard
    simpa only [d1302, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1302, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d1302, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21951 (pattern : Twelve) (guard : d1 pattern = 1) : d1310 pattern ≤ (18 : Int) + d1657 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1310, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21923 pattern childGuard
    simpa only [d1310, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1310, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21950 pattern childGuard
    simpa only [d1310, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21952 (pattern : Twelve) (guard : d1 pattern = 1) : d1316 pattern ≤ (18 : Int) + d1660 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1316, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21948 pattern childGuard
    simpa only [d1316, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1316, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21951 pattern childGuard
    simpa only [d1316, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21953 (pattern : Twelve) (guard : d1 pattern = 1) : d1291 pattern ≤ (18 : Int) + d821 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21924 pattern childGuard
    simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21631 pattern childGuard
    simpa only [d1291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21954 (pattern : Twelve) (guard : d1 pattern = 1) : d1303 pattern ≤ (18 : Int) + d1653 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1303, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21953 pattern childGuard
    simpa only [d1303, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1303, d1653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d1303, d1653, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21955 (pattern : Twelve) (guard : d1 pattern = 1) : d1311 pattern ≤ (18 : Int) + d1658 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1311, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21931 pattern childGuard
    simpa only [d1311, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1311, d1658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21954 pattern childGuard
    simpa only [d1311, d1658, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21956 (pattern : Twelve) (guard : d1 pattern = 1) : d1292 pattern ≤ (18 : Int) + d822 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21938 pattern childGuard
    simpa only [d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21677 pattern childGuard
    simpa only [d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21957 (pattern : Twelve) (guard : d1 pattern = 1) : d1304 pattern ≤ (18 : Int) + d1655 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1304, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21956 pattern childGuard
    simpa only [d1304, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1304, d1655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d1304, d1655, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21958 (pattern : Twelve) (guard : d1 pattern = 1) : d1312 pattern ≤ (18 : Int) + d1659 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1312, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21937 pattern childGuard
    simpa only [d1312, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1312, d1659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21957 pattern childGuard
    simpa only [d1312, d1659, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21959 (pattern : Twelve) (guard : d1 pattern = 1) : d1317 pattern ≤ (18 : Int) + d1661 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1317, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21955 pattern childGuard
    simpa only [d1317, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1317, d1661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21958 pattern childGuard
    simpa only [d1317, d1661, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21960 (pattern : Twelve) (guard : d1 pattern = 1) : d1318 pattern ≤ (18 : Int) + d1662 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1318, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21951 pattern childGuard
    simpa only [d1318, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1318, d1662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21564 pattern childGuard
    simpa only [d1318, d1662, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21961 (pattern : Twelve) (guard : d1 pattern = 1) : d1320 pattern ≤ (18 : Int) + d1663 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1320, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21959 pattern childGuard
    simpa only [d1320, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1320, d1663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21960 pattern childGuard
    simpa only [d1320, d1663, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21962 (pattern : Twelve) (guard : d1 pattern = 1) : d1322 pattern ≤ (18 : Int) + d1664 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1322, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21952 pattern childGuard
    simpa only [d1322, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1322, d1664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21961 pattern childGuard
    simpa only [d1322, d1664, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21963 (pattern : Twelve) (guard : d1 pattern = 1) : d1323 pattern ≤ (18 : Int) + d1664 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21945 pattern childGuard
    simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21962 pattern childGuard
    simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21964 (pattern : Twelve) (guard : d1 pattern = 1) : d1324 pattern ≤ (18 : Int) + d20 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21562 pattern childGuard
    simpa only [d1324, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1324, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21632 pattern childGuard
    simpa only [d1324, d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21965 (pattern : Twelve) (guard : d1 pattern = 1) : d1325 pattern ≤ (18 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1325, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21913 pattern childGuard
    simpa only [d1325, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1325, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21964 pattern childGuard
    simpa only [d1325, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21966 (pattern : Twelve) (guard : d1 pattern = 1) : d1326 pattern ≤ (18 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1326, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21848 pattern childGuard
    simpa only [d1326, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1326, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21964 pattern childGuard
    simpa only [d1326, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21967 (pattern : Twelve) (guard : d1 pattern = 1) : d1333 pattern ≤ (18 : Int) + d1644 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21965 pattern childGuard
    simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21966 pattern childGuard
    simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21968 (pattern : Twelve) (guard : d1 pattern = 1) : d1339 pattern ≤ (18 : Int) + d1668 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1339, d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21552 pattern childGuard
    simpa only [d1339, d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1339, d1668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21967 pattern childGuard
    simpa only [d1339, d1668, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21969 (pattern : Twelve) (guard : d1 pattern = 1) : d1345 pattern ≤ (18 : Int) + d1671 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1345, d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21968 pattern childGuard
    simpa only [d1345, d1671, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1345, d1671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21917 pattern childGuard
    simpa only [d1345, d1671, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21970 (pattern : Twelve) (guard : d1 pattern = 1) : d1327 pattern ≤ (18 : Int) + d1644 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1327, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21913 pattern childGuard
    simpa only [d1327, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1327, d1644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21868 pattern childGuard
    simpa only [d1327, d1644, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21971 (pattern : Twelve) (guard : d1 pattern = 1) : d1334 pattern ≤ (18 : Int) + d1647 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1334, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21970 pattern childGuard
    simpa only [d1334, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1334, d1647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21921 pattern childGuard
    simpa only [d1334, d1647, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21972 (pattern : Twelve) (guard : d1 pattern = 1) : d1340 pattern ≤ (18 : Int) + d1651 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1340, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21796 pattern childGuard
    simpa only [d1340, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1340, d1651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21971 pattern childGuard
    simpa only [d1340, d1651, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21973 (pattern : Twelve) (guard : d1 pattern = 1) : d1346 pattern ≤ (18 : Int) + d1657 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1346, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21972 pattern childGuard
    simpa only [d1346, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1346, d1657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21926 pattern childGuard
    simpa only [d1346, d1657, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21974 (pattern : Twelve) (guard : d1 pattern = 1) : d1349 pattern ≤ (18 : Int) + d1674 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1349, d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21969 pattern childGuard
    simpa only [d1349, d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1349, d1674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21973 pattern childGuard
    simpa only [d1349, d1674, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21975 (pattern : Twelve) (guard : d1 pattern = 1) : d1328 pattern ≤ (18 : Int) + d1665 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1328, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21848 pattern childGuard
    simpa only [d1328, d1665, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1328, d1665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21934 pattern childGuard
    simpa only [d1328, d1665, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21976 (pattern : Twelve) (guard : d1 pattern = 1) : d1335 pattern ≤ (18 : Int) + d1666 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1335, d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21970 pattern childGuard
    simpa only [d1335, d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1335, d1666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21975 pattern childGuard
    simpa only [d1335, d1666, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21977 (pattern : Twelve) (guard : d1 pattern = 1) : d1341 pattern ≤ (18 : Int) + d1669 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1341, d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21592 pattern childGuard
    simpa only [d1341, d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1341, d1669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21976 pattern childGuard
    simpa only [d1341, d1669, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21978 (pattern : Twelve) (guard : d1 pattern = 1) : d1329 pattern ≤ (18 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1329, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21563 pattern childGuard
    simpa only [d1329, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1329, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21575 pattern childGuard
    simpa only [d1329, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c21979 (pattern : Twelve) (guard : d1 pattern = 1) : d1336 pattern ≤ (18 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1336, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21924 pattern childGuard
    simpa only [d1336, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1336, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c21978 pattern childGuard
    simpa only [d1336, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
