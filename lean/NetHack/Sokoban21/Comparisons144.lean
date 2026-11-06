/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons143
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c20160 (pattern : Twelve) (guard : d1 pattern = 1) : d69 pattern ≤ (16 : Int) + d836 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d69, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19530 pattern childGuard
    simpa only [d69, d836, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d69, d836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20159 pattern childGuard
    simpa only [d69, d836, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20161 (pattern : Twelve) (guard : d1 pattern = 1) : d89 pattern ≤ (16 : Int) + d851 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d89, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19525 pattern childGuard
    simpa only [d89, d851, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d89, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20160 pattern childGuard
    simpa only [d89, d851, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20162 (pattern : Twelve) (guard : d1 pattern = 1) : d48 pattern ≤ (16 : Int) + d48 pattern := by
  omega
theorem c20163 (pattern : Twelve) (guard : d1 pattern = 1) : d70 pattern ≤ (16 : Int) + d837 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d70, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19530 pattern childGuard
    simpa only [d70, d837, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d70, d837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20162 pattern childGuard
    simpa only [d70, d837, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20164 (pattern : Twelve) (guard : d1 pattern = 1) : d90 pattern ≤ (16 : Int) + d852 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d90, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20163 pattern childGuard
    simpa only [d90, d852, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d90, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19544 pattern childGuard
    simpa only [d90, d852, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20165 (pattern : Twelve) (guard : d1 pattern = 1) : d101 pattern ≤ (16 : Int) + d860 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d101, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20161 pattern childGuard
    simpa only [d101, d860, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d101, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20164 pattern childGuard
    simpa only [d101, d860, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20166 (pattern : Twelve) (guard : d1 pattern = 1) : d108 pattern ≤ (16 : Int) + d865 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d108, d865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20158 pattern childGuard
    simpa only [d108, d865, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d108, d865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20165 pattern childGuard
    simpa only [d108, d865, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20167 (pattern : Twelve) (guard : d1 pattern = 1) : d109 pattern ≤ (16 : Int) + d866 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d109, d866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20149 pattern childGuard
    simpa only [d109, d866, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d109, d866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d109, d866, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20168 (pattern : Twelve) (guard : d1 pattern = 1) : d113 pattern ≤ (16 : Int) + d868 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d113, d868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20166 pattern childGuard
    simpa only [d113, d868, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d113, d868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20167 pattern childGuard
    simpa only [d113, d868, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20169 (pattern : Twelve) (guard : d1 pattern = 1) : d115 pattern ≤ (16 : Int) + d870 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d115, d870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20151 pattern childGuard
    simpa only [d115, d870, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d115, d870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20168 pattern childGuard
    simpa only [d115, d870, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20170 (pattern : Twelve) (guard : d1 pattern = 1) : d116 pattern ≤ (16 : Int) + d871 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d116, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19960 pattern childGuard
    simpa only [d116, d871, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d116, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20169 pattern childGuard
    simpa only [d116, d871, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20171 (pattern : Twelve) (guard : d1874 pattern = 1) : d116 pattern ≤ (16 : Int) + d871 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20131 pattern childGuard
    simpa only [d1874, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20170 pattern childGuard
    simpa only [d1874, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20172 (pattern : Twelve) (guard : d0 pattern = 1) : d805 pattern ≤ (16 : Int) + d1266 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c20173 (pattern : Twelve) (guard : d1 pattern = 1) : d778 pattern ≤ (16 : Int) + d779 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d778, d779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19485 pattern childGuard
    simpa only [d778, d779, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d778, d779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19513 pattern childGuard
    simpa only [d778, d779, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20174 (pattern : Twelve) (guard : d1 pattern = 1) : d779 pattern ≤ (16 : Int) + d1247 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d779, d1247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19949 pattern childGuard
    simpa only [d779, d1247, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d779, d1247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19513 pattern childGuard
    simpa only [d779, d1247, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20175 (pattern : Twelve) (guard : d1 pattern = 1) : d782 pattern ≤ (16 : Int) + d1249 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d782, d1249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20173 pattern childGuard
    simpa only [d782, d1249, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d782, d1249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20174 pattern childGuard
    simpa only [d782, d1249, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20176 (pattern : Twelve) (guard : d1 pattern = 1) : d788 pattern ≤ (16 : Int) + d1253 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d788, d1253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19459 pattern childGuard
    simpa only [d788, d1253, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d788, d1253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20175 pattern childGuard
    simpa only [d788, d1253, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20177 (pattern : Twelve) (guard : d1 pattern = 1) : d38 pattern ≤ (16 : Int) + d1248 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d1248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19485 pattern childGuard
    simpa only [d38, d1248, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d1248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19526 pattern childGuard
    simpa only [d38, d1248, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20178 (pattern : Twelve) (guard : d1 pattern = 1) : d789 pattern ≤ (16 : Int) + d1254 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d789, d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20177 pattern childGuard
    simpa only [d789, d1254, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d789, d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19954 pattern childGuard
    simpa only [d789, d1254, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20179 (pattern : Twelve) (guard : d1 pattern = 1) : d794 pattern ≤ (16 : Int) + d1258 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d794, d1258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20176 pattern childGuard
    simpa only [d794, d1258, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d794, d1258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20178 pattern childGuard
    simpa only [d794, d1258, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20180 (pattern : Twelve) (guard : d1 pattern = 1) : d783 pattern ≤ (16 : Int) + d59 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d783, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20155 pattern childGuard
    simpa only [d783, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d783, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20138 pattern childGuard
    simpa only [d783, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20181 (pattern : Twelve) (guard : d1 pattern = 1) : d790 pattern ≤ (16 : Int) + d851 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d790, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20180 pattern childGuard
    simpa only [d790, d851, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d790, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20160 pattern childGuard
    simpa only [d790, d851, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20182 (pattern : Twelve) (guard : d1 pattern = 1) : d795 pattern ≤ (16 : Int) + d860 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d795, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20181 pattern childGuard
    simpa only [d795, d860, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d795, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20164 pattern childGuard
    simpa only [d795, d860, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20183 (pattern : Twelve) (guard : d1 pattern = 1) : d798 pattern ≤ (16 : Int) + d1261 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d798, d1261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20179 pattern childGuard
    simpa only [d798, d1261, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d798, d1261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20182 pattern childGuard
    simpa only [d798, d1261, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20184 (pattern : Twelve) (guard : d1 pattern = 1) : d799 pattern ≤ (16 : Int) + d1261 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d799, d1261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20179 pattern childGuard
    simpa only [d799, d1261, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d799, d1261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20165 pattern childGuard
    simpa only [d799, d1261, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20185 (pattern : Twelve) (guard : d1 pattern = 1) : d802 pattern ≤ (16 : Int) + d1261 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20183 pattern childGuard
    simpa only [d802, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20184 pattern childGuard
    simpa only [d802, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20186 (pattern : Twelve) (guard : d1 pattern = 1) : d780 pattern ≤ (16 : Int) + d780 pattern := by
  omega
theorem c20187 (pattern : Twelve) (guard : d1 pattern = 1) : d784 pattern ≤ (16 : Int) + d1250 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d784, d1250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19530 pattern childGuard
    simpa only [d784, d1250, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d784, d1250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20186 pattern childGuard
    simpa only [d784, d1250, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20188 (pattern : Twelve) (guard : d1 pattern = 1) : d791 pattern ≤ (16 : Int) + d1255 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d791, d1255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20155 pattern childGuard
    simpa only [d791, d1255, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d791, d1255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20187 pattern childGuard
    simpa only [d791, d1255, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20189 (pattern : Twelve) (guard : d1 pattern = 1) : d796 pattern ≤ (16 : Int) + d1259 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d796, d1259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20188 pattern childGuard
    simpa only [d796, d1259, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d796, d1259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20164 pattern childGuard
    simpa only [d796, d1259, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20190 (pattern : Twelve) (guard : d1 pattern = 1) : d48 pattern ≤ (16 : Int) + d49 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19529 pattern childGuard
    simpa only [d48, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d48, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20191 (pattern : Twelve) (guard : d1 pattern = 1) : d781 pattern ≤ (16 : Int) + d781 pattern := by
  omega
theorem c20192 (pattern : Twelve) (guard : d1 pattern = 1) : d785 pattern ≤ (16 : Int) + d1251 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d785, d1251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20190 pattern childGuard
    simpa only [d785, d1251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d785, d1251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20191 pattern childGuard
    simpa only [d785, d1251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20193 (pattern : Twelve) (guard : d1 pattern = 1) : d792 pattern ≤ (16 : Int) + d1256 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d792, d1256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20162 pattern childGuard
    simpa only [d792, d1256, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d792, d1256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20192 pattern childGuard
    simpa only [d792, d1256, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20194 (pattern : Twelve) (guard : d1 pattern = 1) : d786 pattern ≤ (16 : Int) + d787 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d786, d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20190 pattern childGuard
    simpa only [d786, d787, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d786, d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d786, d787, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20195 (pattern : Twelve) (guard : d1 pattern = 1) : d787 pattern ≤ (16 : Int) + d1252 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d787, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19543 pattern childGuard
    simpa only [d787, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d787, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d787, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20196 (pattern : Twelve) (guard : d1 pattern = 1) : d793 pattern ≤ (16 : Int) + d1257 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d793, d1257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20194 pattern childGuard
    simpa only [d793, d1257, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d793, d1257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20195 pattern childGuard
    simpa only [d793, d1257, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20197 (pattern : Twelve) (guard : d1 pattern = 1) : d797 pattern ≤ (16 : Int) + d1260 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d797, d1260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20193 pattern childGuard
    simpa only [d797, d1260, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d797, d1260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20196 pattern childGuard
    simpa only [d797, d1260, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20198 (pattern : Twelve) (guard : d1 pattern = 1) : d800 pattern ≤ (16 : Int) + d1262 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d800, d1262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20189 pattern childGuard
    simpa only [d800, d1262, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d800, d1262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20197 pattern childGuard
    simpa only [d800, d1262, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20199 (pattern : Twelve) (guard : d1 pattern = 1) : d801 pattern ≤ (16 : Int) + d1263 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d801, d1263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20165 pattern childGuard
    simpa only [d801, d1263, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d801, d1263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d801, d1263, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20200 (pattern : Twelve) (guard : d1 pattern = 1) : d803 pattern ≤ (16 : Int) + d1264 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d803, d1264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20198 pattern childGuard
    simpa only [d803, d1264, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d803, d1264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20199 pattern childGuard
    simpa only [d803, d1264, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20201 (pattern : Twelve) (guard : d1 pattern = 1) : d804 pattern ≤ (16 : Int) + d1265 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d804, d1265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20185 pattern childGuard
    simpa only [d804, d1265, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d804, d1265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20200 pattern childGuard
    simpa only [d804, d1265, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20202 (pattern : Twelve) (guard : d1 pattern = 1) : d805 pattern ≤ (16 : Int) + d1266 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d805, d1266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20003 pattern childGuard
    simpa only [d805, d1266, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d805, d1266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20201 pattern childGuard
    simpa only [d805, d1266, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20203 (pattern : Twelve) (guard : d1874 pattern = 1) : d805 pattern ≤ (16 : Int) + d1266 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20172 pattern childGuard
    simpa only [d1874, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20202 pattern childGuard
    simpa only [d1874, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20204 (pattern : Twelve) (guard : d1874 pattern = 1) : d806 pattern ≤ (16 : Int) + d1267 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1874 pattern = 1 := by simpa only [d806, d1267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20171 pattern childGuard
    simpa only [d806, d1267, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1874 pattern = 1 := by simpa only [d806, d1267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20203 pattern childGuard
    simpa only [d806, d1267, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20205 (pattern : Twelve) (guard : d0 pattern = 1) : d871 pattern ≤ (16 : Int) + d1323 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c20206 (pattern : Twelve) (guard : d1 pattern = 1) : d823 pattern ≤ (16 : Int) + d1283 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d823, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19458 pattern childGuard
    simpa only [d823, d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d823, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19485 pattern childGuard
    simpa only [d823, d1283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20207 (pattern : Twelve) (guard : d1 pattern = 1) : d846 pattern ≤ (16 : Int) + d1301 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d846, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20206 pattern childGuard
    simpa only [d846, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d846, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19667 pattern childGuard
    simpa only [d846, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20208 (pattern : Twelve) (guard : d1 pattern = 1) : d857 pattern ≤ (16 : Int) + d1309 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d857, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19653 pattern childGuard
    simpa only [d857, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d857, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20207 pattern childGuard
    simpa only [d857, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20209 (pattern : Twelve) (guard : d1 pattern = 1) : d833 pattern ≤ (16 : Int) + d1290 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d833, d1290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19466 pattern childGuard
    simpa only [d833, d1290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d833, d1290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19695 pattern childGuard
    simpa only [d833, d1290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20210 (pattern : Twelve) (guard : d1 pattern = 1) : d848 pattern ≤ (16 : Int) + d1302 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d848, d1302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20209 pattern childGuard
    simpa only [d848, d1302, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d848, d1302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19667 pattern childGuard
    simpa only [d848, d1302, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20211 (pattern : Twelve) (guard : d1 pattern = 1) : d858 pattern ≤ (16 : Int) + d1310 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d858, d1310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19678 pattern childGuard
    simpa only [d858, d1310, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d858, d1310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20210 pattern childGuard
    simpa only [d858, d1310, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20212 (pattern : Twelve) (guard : d1 pattern = 1) : d864 pattern ≤ (16 : Int) + d1316 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d864, d1316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20208 pattern childGuard
    simpa only [d864, d1316, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d864, d1316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20211 pattern childGuard
    simpa only [d864, d1316, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20213 (pattern : Twelve) (guard : d1 pattern = 1) : d835 pattern ≤ (16 : Int) + d1291 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d835, d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19466 pattern childGuard
    simpa only [d835, d1291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d835, d1291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19530 pattern childGuard
    simpa only [d835, d1291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20214 (pattern : Twelve) (guard : d1 pattern = 1) : d850 pattern ≤ (16 : Int) + d1303 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d850, d1303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20213 pattern childGuard
    simpa only [d850, d1303, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d850, d1303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19667 pattern childGuard
    simpa only [d850, d1303, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20215 (pattern : Twelve) (guard : d1 pattern = 1) : d859 pattern ≤ (16 : Int) + d1311 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d859, d1311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19688 pattern childGuard
    simpa only [d859, d1311, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d859, d1311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20214 pattern childGuard
    simpa only [d859, d1311, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20216 (pattern : Twelve) (guard : d1 pattern = 1) : d837 pattern ≤ (16 : Int) + d1292 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d837, d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19542 pattern childGuard
    simpa only [d837, d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d837, d1292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20190 pattern childGuard
    simpa only [d837, d1292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20217 (pattern : Twelve) (guard : d1 pattern = 1) : d852 pattern ≤ (16 : Int) + d1304 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d852, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20216 pattern childGuard
    simpa only [d852, d1304, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d852, d1304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19706 pattern childGuard
    simpa only [d852, d1304, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20218 (pattern : Twelve) (guard : d1 pattern = 1) : d860 pattern ≤ (16 : Int) + d1312 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d860, d1312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19701 pattern childGuard
    simpa only [d860, d1312, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d860, d1312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20217 pattern childGuard
    simpa only [d860, d1312, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20219 (pattern : Twelve) (guard : d1 pattern = 1) : d865 pattern ≤ (16 : Int) + d1317 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d865, d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20215 pattern childGuard
    simpa only [d865, d1317, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d865, d1317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20218 pattern childGuard
    simpa only [d865, d1317, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20220 (pattern : Twelve) (guard : d1 pattern = 1) : d866 pattern ≤ (16 : Int) + d1318 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d866, d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20211 pattern childGuard
    simpa only [d866, d1318, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d866, d1318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d866, d1318, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20221 (pattern : Twelve) (guard : d1 pattern = 1) : d868 pattern ≤ (16 : Int) + d1320 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d868, d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20219 pattern childGuard
    simpa only [d868, d1320, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d868, d1320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20220 pattern childGuard
    simpa only [d868, d1320, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20222 (pattern : Twelve) (guard : d1 pattern = 1) : d870 pattern ≤ (16 : Int) + d1322 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d870, d1322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20212 pattern childGuard
    simpa only [d870, d1322, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d870, d1322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20221 pattern childGuard
    simpa only [d870, d1322, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20223 (pattern : Twelve) (guard : d1 pattern = 1) : d871 pattern ≤ (16 : Int) + d1323 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d871, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20028 pattern childGuard
    simpa only [d871, d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d871, d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20222 pattern childGuard
    simpa only [d871, d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20224 (pattern : Twelve) (guard : d1874 pattern = 1) : d871 pattern ≤ (16 : Int) + d1323 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20205 pattern childGuard
    simpa only [d1874, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20223 pattern childGuard
    simpa only [d1874, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20225 (pattern : Twelve) (guard : d0 pattern = 1) : d1266 pattern ≤ (16 : Int) + d1635 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c20226 (pattern : Twelve) (guard : d1 pattern = 1) : d779 pattern ≤ (16 : Int) + d1616 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d779, d1616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19674 pattern childGuard
    simpa only [d779, d1616, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d779, d1616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19685 pattern childGuard
    simpa only [d779, d1616, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20227 (pattern : Twelve) (guard : d1 pattern = 1) : d1247 pattern ≤ (16 : Int) + d119 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20019 pattern childGuard
    simpa only [d1247, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19685 pattern childGuard
    simpa only [d1247, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20228 (pattern : Twelve) (guard : d1 pattern = 1) : d1249 pattern ≤ (16 : Int) + d1619 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1249, d1619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20226 pattern childGuard
    simpa only [d1249, d1619, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1249, d1619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20227 pattern childGuard
    simpa only [d1249, d1619, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20229 (pattern : Twelve) (guard : d1 pattern = 1) : d1253 pattern ≤ (16 : Int) + d1622 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1253, d1622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19485 pattern childGuard
    simpa only [d1253, d1622, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1253, d1622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20228 pattern childGuard
    simpa only [d1253, d1622, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20230 (pattern : Twelve) (guard : d1 pattern = 1) : d1248 pattern ≤ (16 : Int) + d1617 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1248, d1617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19465 pattern childGuard
    simpa only [d1248, d1617, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1248, d1617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19529 pattern childGuard
    simpa only [d1248, d1617, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20231 (pattern : Twelve) (guard : d1 pattern = 1) : d1254 pattern ≤ (16 : Int) + d1623 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1254, d1623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20230 pattern childGuard
    simpa only [d1254, d1623, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1254, d1623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19706 pattern childGuard
    simpa only [d1254, d1623, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20232 (pattern : Twelve) (guard : d1 pattern = 1) : d1258 pattern ≤ (16 : Int) + d1627 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1258, d1627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20229 pattern childGuard
    simpa only [d1258, d1627, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1258, d1627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20231 pattern childGuard
    simpa only [d1258, d1627, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20233 (pattern : Twelve) (guard : d1 pattern = 1) : d1261 pattern ≤ (16 : Int) + d1630 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1261, d1630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20232 pattern childGuard
    simpa only [d1261, d1630, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1261, d1630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20218 pattern childGuard
    simpa only [d1261, d1630, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20234 (pattern : Twelve) (guard : d1 pattern = 1) : d780 pattern ≤ (16 : Int) + d1618 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d780, d1618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19685 pattern childGuard
    simpa only [d780, d1618, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d780, d1618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19993 pattern childGuard
    simpa only [d780, d1618, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20235 (pattern : Twelve) (guard : d1 pattern = 1) : d1250 pattern ≤ (16 : Int) + d1620 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1250, d1620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19698 pattern childGuard
    simpa only [d1250, d1620, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1250, d1620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20234 pattern childGuard
    simpa only [d1250, d1620, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20236 (pattern : Twelve) (guard : d1 pattern = 1) : d1255 pattern ≤ (16 : Int) + d1624 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1255, d1624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19530 pattern childGuard
    simpa only [d1255, d1624, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1255, d1624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20235 pattern childGuard
    simpa only [d1255, d1624, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20237 (pattern : Twelve) (guard : d1 pattern = 1) : d1259 pattern ≤ (16 : Int) + d1628 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1259, d1628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20236 pattern childGuard
    simpa only [d1259, d1628, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1259, d1628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20217 pattern childGuard
    simpa only [d1259, d1628, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20238 (pattern : Twelve) (guard : d1 pattern = 1) : d49 pattern ≤ (16 : Int) + d1331 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d49, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19697 pattern childGuard
    simpa only [d49, d1331, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d49, d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d49, d1331, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20239 (pattern : Twelve) (guard : d1 pattern = 1) : d781 pattern ≤ (16 : Int) + d182 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d781, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19993 pattern childGuard
    simpa only [d781, d182, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d781, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d781, d182, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20240 (pattern : Twelve) (guard : d1 pattern = 1) : d1251 pattern ≤ (16 : Int) + d1621 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1251, d1621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20238 pattern childGuard
    simpa only [d1251, d1621, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1251, d1621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20239 pattern childGuard
    simpa only [d1251, d1621, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20241 (pattern : Twelve) (guard : d1 pattern = 1) : d1256 pattern ≤ (16 : Int) + d1625 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1256, d1625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20190 pattern childGuard
    simpa only [d1256, d1625, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1256, d1625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20240 pattern childGuard
    simpa only [d1256, d1625, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20242 (pattern : Twelve) (guard : d1 pattern = 1) : d1257 pattern ≤ (16 : Int) + d1626 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1257, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20195 pattern childGuard
    simpa only [d1257, d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1257, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19768 pattern childGuard
    simpa only [d1257, d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20243 (pattern : Twelve) (guard : d1 pattern = 1) : d1260 pattern ≤ (16 : Int) + d1629 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1260, d1629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20241 pattern childGuard
    simpa only [d1260, d1629, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1260, d1629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20242 pattern childGuard
    simpa only [d1260, d1629, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20244 (pattern : Twelve) (guard : d1 pattern = 1) : d1262 pattern ≤ (16 : Int) + d1631 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1262, d1631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20237 pattern childGuard
    simpa only [d1262, d1631, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1262, d1631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20243 pattern childGuard
    simpa only [d1262, d1631, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20245 (pattern : Twelve) (guard : d1 pattern = 1) : d1263 pattern ≤ (16 : Int) + d1632 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1263, d1632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20218 pattern childGuard
    simpa only [d1263, d1632, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1263, d1632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d1263, d1632, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20246 (pattern : Twelve) (guard : d1 pattern = 1) : d1264 pattern ≤ (16 : Int) + d1633 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1264, d1633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20244 pattern childGuard
    simpa only [d1264, d1633, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1264, d1633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20245 pattern childGuard
    simpa only [d1264, d1633, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20247 (pattern : Twelve) (guard : d1 pattern = 1) : d1265 pattern ≤ (16 : Int) + d1634 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1265, d1634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20233 pattern childGuard
    simpa only [d1265, d1634, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1265, d1634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20246 pattern childGuard
    simpa only [d1265, d1634, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20248 (pattern : Twelve) (guard : d1 pattern = 1) : d1266 pattern ≤ (16 : Int) + d1635 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1266, d1635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20064 pattern childGuard
    simpa only [d1266, d1635, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1266, d1635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20247 pattern childGuard
    simpa only [d1266, d1635, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20249 (pattern : Twelve) (guard : d1874 pattern = 1) : d1266 pattern ≤ (16 : Int) + d1635 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20225 pattern childGuard
    simpa only [d1874, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20248 pattern childGuard
    simpa only [d1874, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20250 (pattern : Twelve) (guard : d1874 pattern = 1) : d1267 pattern ≤ (16 : Int) + d1636 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1874 pattern = 1 := by simpa only [d1267, d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20224 pattern childGuard
    simpa only [d1267, d1636, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1874 pattern = 1 := by simpa only [d1267, d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20249 pattern childGuard
    simpa only [d1267, d1636, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20251 (pattern : Twelve) (guard : d0 pattern = 1) : d1323 pattern ≤ (16 : Int) + d1664 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c20252 (pattern : Twelve) (guard : d1 pattern = 1) : d1323 pattern ≤ (16 : Int) + d1664 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20081 pattern childGuard
    simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19825 pattern childGuard
    simpa only [d1323, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20253 (pattern : Twelve) (guard : d1874 pattern = 1) : d1323 pattern ≤ (16 : Int) + d1664 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20251 pattern childGuard
    simpa only [d1874, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20252 pattern childGuard
    simpa only [d1874, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20254 (pattern : Twelve) (guard : d0 pattern = 1) : d1635 pattern ≤ (16 : Int) + d1826 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c20255 (pattern : Twelve) (guard : d1 pattern = 1) : d1616 pattern ≤ (16 : Int) + d20 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19791 pattern childGuard
    simpa only [d1616, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19805 pattern childGuard
    simpa only [d1616, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20256 (pattern : Twelve) (guard : d1 pattern = 1) : d1619 pattern ≤ (16 : Int) + d20 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20255 pattern childGuard
    simpa only [d1619, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19805 pattern childGuard
    simpa only [d1619, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20257 (pattern : Twelve) (guard : d1 pattern = 1) : d1622 pattern ≤ (16 : Int) + d1814 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1622, d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19465 pattern childGuard
    simpa only [d1622, d1814, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1622, d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20256 pattern childGuard
    simpa only [d1622, d1814, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20258 (pattern : Twelve) (guard : d1 pattern = 1) : d1617 pattern ≤ (16 : Int) + d21 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19798 pattern childGuard
    simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19541 pattern childGuard
    simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20259 (pattern : Twelve) (guard : d1 pattern = 1) : d1623 pattern ≤ (16 : Int) + d1815 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1623, d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20258 pattern childGuard
    simpa only [d1623, d1815, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1623, d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d1623, d1815, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20260 (pattern : Twelve) (guard : d1 pattern = 1) : d1627 pattern ≤ (16 : Int) + d1818 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1627, d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20257 pattern childGuard
    simpa only [d1627, d1818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1627, d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20259 pattern childGuard
    simpa only [d1627, d1818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20261 (pattern : Twelve) (guard : d1 pattern = 1) : d1630 pattern ≤ (16 : Int) + d1821 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1630, d1821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20260 pattern childGuard
    simpa only [d1630, d1821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1630, d1821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19821 pattern childGuard
    simpa only [d1630, d1821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20262 (pattern : Twelve) (guard : d1 pattern = 1) : d1618 pattern ≤ (16 : Int) + d1646 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1618, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19805 pattern childGuard
    simpa only [d1618, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1618, d1646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19852 pattern childGuard
    simpa only [d1618, d1646, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20263 (pattern : Twelve) (guard : d1 pattern = 1) : d1620 pattern ≤ (16 : Int) + d1646 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19814 pattern childGuard
    simpa only [d1620, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20262 pattern childGuard
    simpa only [d1620, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20264 (pattern : Twelve) (guard : d1 pattern = 1) : d1624 pattern ≤ (16 : Int) + d1816 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1624, d1816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19542 pattern childGuard
    simpa only [d1624, d1816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1624, d1816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20263 pattern childGuard
    simpa only [d1624, d1816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20265 (pattern : Twelve) (guard : d1 pattern = 1) : d1628 pattern ≤ (16 : Int) + d1819 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1628, d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20264 pattern childGuard
    simpa only [d1628, d1819, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1628, d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19820 pattern childGuard
    simpa only [d1628, d1819, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20266 (pattern : Twelve) (guard : d1 pattern = 1) : d1621 pattern ≤ (16 : Int) + d183 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20102 pattern childGuard
    simpa only [d1621, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19861 pattern childGuard
    simpa only [d1621, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20267 (pattern : Twelve) (guard : d1 pattern = 1) : d1625 pattern ≤ (16 : Int) + d1817 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1625, d1817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19543 pattern childGuard
    simpa only [d1625, d1817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1625, d1817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20266 pattern childGuard
    simpa only [d1625, d1817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20268 (pattern : Twelve) (guard : d1 pattern = 1) : d1629 pattern ≤ (16 : Int) + d1820 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1629, d1820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20267 pattern childGuard
    simpa only [d1629, d1820, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1629, d1820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20124 pattern childGuard
    simpa only [d1629, d1820, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20269 (pattern : Twelve) (guard : d1 pattern = 1) : d1631 pattern ≤ (16 : Int) + d1822 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1631, d1822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20265 pattern childGuard
    simpa only [d1631, d1822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1631, d1822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20268 pattern childGuard
    simpa only [d1631, d1822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20270 (pattern : Twelve) (guard : d1 pattern = 1) : d1632 pattern ≤ (16 : Int) + d1823 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1632, d1823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19821 pattern childGuard
    simpa only [d1632, d1823, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1632, d1823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19470 pattern childGuard
    simpa only [d1632, d1823, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20271 (pattern : Twelve) (guard : d1 pattern = 1) : d1633 pattern ≤ (16 : Int) + d1824 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1633, d1824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20269 pattern childGuard
    simpa only [d1633, d1824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1633, d1824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20270 pattern childGuard
    simpa only [d1633, d1824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20272 (pattern : Twelve) (guard : d1 pattern = 1) : d1634 pattern ≤ (16 : Int) + d1825 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1634, d1825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20261 pattern childGuard
    simpa only [d1634, d1825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1634, d1825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20271 pattern childGuard
    simpa only [d1634, d1825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20273 (pattern : Twelve) (guard : d1 pattern = 1) : d1635 pattern ≤ (16 : Int) + d1826 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1635, d1826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20112 pattern childGuard
    simpa only [d1635, d1826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1635, d1826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20272 pattern childGuard
    simpa only [d1635, d1826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20274 (pattern : Twelve) (guard : d1874 pattern = 1) : d1635 pattern ≤ (16 : Int) + d1826 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20254 pattern childGuard
    simpa only [d1874, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20273 pattern childGuard
    simpa only [d1874, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20275 (pattern : Twelve) (guard : d1874 pattern = 1) : d1636 pattern ≤ (16 : Int) + d1827 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1874 pattern = 1 := by simpa only [d1636, d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20253 pattern childGuard
    simpa only [d1636, d1827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1874 pattern = 1 := by simpa only [d1636, d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20274 pattern childGuard
    simpa only [d1636, d1827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20276 (pattern : Twelve) (guard : d1874 pattern = 1) : d1664 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19872 pattern childGuard
    simpa only [d1874, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19899 pattern childGuard
    simpa only [d1874, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20277 (pattern : Twelve) (guard : d0 pattern = 1) : d1826 pattern ≤ (16 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c20278 (pattern : Twelve) (guard : d1 pattern = 1) : d1826 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20128 pattern childGuard
    simpa only [d1826, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c19914 pattern childGuard
    simpa only [d1826, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20279 (pattern : Twelve) (guard : d1874 pattern = 1) : d1826 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d0 pattern = 1 := by simpa only [d1874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20277 pattern childGuard
    simpa only [d1874, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d1874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20278 pattern childGuard
    simpa only [d1874, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20280 (pattern : Twelve) (guard : d1874 pattern = 1) : d1827 pattern ≤ (16 : Int) + d6 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1874 pattern = 1 := by simpa only [d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20276 pattern childGuard
    simpa only [d1827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1874 pattern = 1 := by simpa only [d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20279 pattern childGuard
    simpa only [d1827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20281 (pattern : Twelve) (guard : d1874 pattern = 1) : d806 pattern ≤ (0 : Int) + d806 pattern := by
  omega
theorem c20282 (pattern : Twelve) (guard : d1874 pattern = 1) : d1267 pattern ≤ (0 : Int) + d1267 pattern := by
  omega
theorem c20283 (pattern : Twelve) (guard : d1874 pattern = 1) : d1636 pattern ≤ (0 : Int) + d1636 pattern := by
  omega
theorem c20284 (pattern : Twelve) (guard : d1874 pattern = 1) : d1827 pattern ≤ (0 : Int) + d1827 pattern := by
  omega
theorem c20285 (pattern : Twelve) (guard : d1 pattern = 1) : d72 pattern ≤ (2 : Int) + d72 pattern := by
  omega
theorem c20286 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (2 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13280 pattern childGuard
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13913 pattern childGuard
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20287 (pattern : Twelve) (guard : d1 pattern = 1) : d8 pattern ≤ (2 : Int) + d2 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14008 pattern childGuard
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13329 pattern childGuard
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20288 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (2 : Int) + d9 pattern := by
  omega
theorem c20289 (pattern : Twelve) (guard : d1 pattern = 1) : d18 pattern ≤ (2 : Int) + d23 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d18, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20287 pattern childGuard
    simpa only [d18, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d18, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20288 pattern childGuard
    simpa only [d18, d23, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20290 (pattern : Twelve) (guard : d1 pattern = 1) : d28 pattern ≤ (2 : Int) + d34 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d28, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13285 pattern childGuard
    simpa only [d28, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d28, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20289 pattern childGuard
    simpa only [d28, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20291 (pattern : Twelve) (guard : d1 pattern = 1) : d29 pattern ≤ (2 : Int) + d29 pattern := by
  omega
theorem c20292 (pattern : Twelve) (guard : d1 pattern = 1) : d51 pattern ≤ (2 : Int) + d55 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d51, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20290 pattern childGuard
    simpa only [d51, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d51, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20291 pattern childGuard
    simpa only [d51, d55, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20293 (pattern : Twelve) (guard : d1 pattern = 1) : d73 pattern ≤ (2 : Int) + d80 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d73, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20286 pattern childGuard
    simpa only [d73, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d73, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20292 pattern childGuard
    simpa only [d73, d80, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20294 (pattern : Twelve) (guard : d1 pattern = 1) : d91 pattern ≤ (2 : Int) + d97 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d91, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20285 pattern childGuard
    simpa only [d91, d97, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d91, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20293 pattern childGuard
    simpa only [d91, d97, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20295 (pattern : Twelve) (guard : d1 pattern = 1) : d52 pattern ≤ (2 : Int) + d52 pattern := by
  omega
theorem c20296 (pattern : Twelve) (guard : d1 pattern = 1) : d32 pattern ≤ (2 : Int) + d43 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d32, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13905 pattern childGuard
    simpa only [d32, d43, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d32, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c14323 pattern childGuard
    simpa only [d32, d43, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20297 (pattern : Twelve) (guard : d1 pattern = 1) : d53 pattern ≤ (2 : Int) + d62 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d53, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c13326 pattern childGuard
    simpa only [d53, d62, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d53, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20296 pattern childGuard
    simpa only [d53, d62, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20298 (pattern : Twelve) (guard : d1 pattern = 1) : d74 pattern ≤ (2 : Int) + d83 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d74, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20295 pattern childGuard
    simpa only [d74, d83, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d74, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c20297 pattern childGuard
    simpa only [d74, d83, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c20299 (pattern : Twelve) (guard : d1 pattern = 1) : d22 pattern ≤ (2 : Int) + d22 pattern := by
  omega
end NetHack.Sokoban21.Diagram
