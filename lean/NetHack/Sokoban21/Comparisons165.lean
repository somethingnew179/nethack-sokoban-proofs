/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons164
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c23100 (pattern : Twelve) (guard : d1 pattern = 1) : d90 pattern ≤ (20 : Int) + d852 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d90, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23097 pattern childGuard
    simpa only [d90, d852, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d90, d852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23099 pattern childGuard
    simpa only [d90, d852, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23101 (pattern : Twelve) (guard : d1 pattern = 1) : d101 pattern ≤ (20 : Int) + d860 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d101, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23095 pattern childGuard
    simpa only [d101, d860, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d101, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23100 pattern childGuard
    simpa only [d101, d860, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23102 (pattern : Twelve) (guard : d1 pattern = 1) : d108 pattern ≤ (20 : Int) + d865 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d108, d865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23092 pattern childGuard
    simpa only [d108, d865, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d108, d865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23101 pattern childGuard
    simpa only [d108, d865, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23103 (pattern : Twelve) (guard : d1 pattern = 1) : d109 pattern ≤ (20 : Int) + d866 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d109, d866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23083 pattern childGuard
    simpa only [d109, d866, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d109, d866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d109, d866, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23104 (pattern : Twelve) (guard : d1 pattern = 1) : d113 pattern ≤ (20 : Int) + d868 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d113, d868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23102 pattern childGuard
    simpa only [d113, d868, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d113, d868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23103 pattern childGuard
    simpa only [d113, d868, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23105 (pattern : Twelve) (guard : d1 pattern = 1) : d115 pattern ≤ (20 : Int) + d870 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d115, d870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23085 pattern childGuard
    simpa only [d115, d870, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d115, d870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23104 pattern childGuard
    simpa only [d115, d870, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23106 (pattern : Twelve) (guard : d1 pattern = 1) : d116 pattern ≤ (20 : Int) + d871 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d116, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23063 pattern childGuard
    simpa only [d116, d871, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d116, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23105 pattern childGuard
    simpa only [d116, d871, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23107 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (20 : Int) + d8 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22962 pattern childGuard
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22974 pattern childGuard
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23108 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (20 : Int) + d872 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22962 pattern childGuard
    simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23107 pattern childGuard
    simpa only [d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23109 (pattern : Twelve) (guard : d1 pattern = 1) : d26 pattern ≤ (20 : Int) + d874 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22961 pattern childGuard
    simpa only [d26, d874, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d26, d874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23108 pattern childGuard
    simpa only [d26, d874, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23110 (pattern : Twelve) (guard : d1 pattern = 1) : d27 pattern ≤ (20 : Int) + d875 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22965 pattern childGuard
    simpa only [d27, d875, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23108 pattern childGuard
    simpa only [d27, d875, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23111 (pattern : Twelve) (guard : d1 pattern = 1) : d50 pattern ≤ (20 : Int) + d882 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d50, d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23109 pattern childGuard
    simpa only [d50, d882, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d50, d882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23110 pattern childGuard
    simpa only [d50, d882, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23112 (pattern : Twelve) (guard : d1 pattern = 1) : d72 pattern ≤ (20 : Int) + d890 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d72, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22958 pattern childGuard
    simpa only [d72, d890, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d72, d890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23111 pattern childGuard
    simpa only [d72, d890, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23113 (pattern : Twelve) (guard : d1 pattern = 1) : d120 pattern ≤ (20 : Int) + d876 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d120, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22973 pattern childGuard
    simpa only [d120, d876, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d120, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23055 pattern childGuard
    simpa only [d120, d876, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23114 (pattern : Twelve) (guard : d1 pattern = 1) : d129 pattern ≤ (20 : Int) + d883 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d129, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23113 pattern childGuard
    simpa only [d129, d883, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d129, d883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22986 pattern childGuard
    simpa only [d129, d883, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23115 (pattern : Twelve) (guard : d1 pattern = 1) : d136 pattern ≤ (20 : Int) + d891 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d136, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22961 pattern childGuard
    simpa only [d136, d891, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d136, d891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23114 pattern childGuard
    simpa only [d136, d891, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23116 (pattern : Twelve) (guard : d1 pattern = 1) : d144 pattern ≤ (20 : Int) + d898 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d144, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23112 pattern childGuard
    simpa only [d144, d898, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d144, d898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23115 pattern childGuard
    simpa only [d144, d898, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23117 (pattern : Twelve) (guard : d1 pattern = 1) : d121 pattern ≤ (20 : Int) + d877 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d121, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22961 pattern childGuard
    simpa only [d121, d877, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d121, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23043 pattern childGuard
    simpa only [d121, d877, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23118 (pattern : Twelve) (guard : d1 pattern = 1) : d130 pattern ≤ (20 : Int) + d884 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d130, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23117 pattern childGuard
    simpa only [d130, d884, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d130, d884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23021 pattern childGuard
    simpa only [d130, d884, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23119 (pattern : Twelve) (guard : d1 pattern = 1) : d137 pattern ≤ (20 : Int) + d892 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d137, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22998 pattern childGuard
    simpa only [d137, d892, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d137, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23118 pattern childGuard
    simpa only [d137, d892, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23120 (pattern : Twelve) (guard : d1 pattern = 1) : d138 pattern ≤ (20 : Int) + d893 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d138, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23025 pattern childGuard
    simpa only [d138, d893, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d138, d893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23114 pattern childGuard
    simpa only [d138, d893, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23121 (pattern : Twelve) (guard : d1 pattern = 1) : d145 pattern ≤ (20 : Int) + d899 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d145, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23119 pattern childGuard
    simpa only [d145, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d145, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23120 pattern childGuard
    simpa only [d145, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23122 (pattern : Twelve) (guard : d1 pattern = 1) : d149 pattern ≤ (20 : Int) + d902 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d149, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23116 pattern childGuard
    simpa only [d149, d902, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d149, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23121 pattern childGuard
    simpa only [d149, d902, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23123 (pattern : Twelve) (guard : d1 pattern = 1) : d139 pattern ≤ (20 : Int) + d892 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d139, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23020 pattern childGuard
    simpa only [d139, d892, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d139, d892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23118 pattern childGuard
    simpa only [d139, d892, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23124 (pattern : Twelve) (guard : d1 pattern = 1) : d146 pattern ≤ (20 : Int) + d899 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d146, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23123 pattern childGuard
    simpa only [d146, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d146, d899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23120 pattern childGuard
    simpa only [d146, d899, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23125 (pattern : Twelve) (guard : d1 pattern = 1) : d150 pattern ≤ (20 : Int) + d902 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d150, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23116 pattern childGuard
    simpa only [d150, d902, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d150, d902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23124 pattern childGuard
    simpa only [d150, d902, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23126 (pattern : Twelve) (guard : d1 pattern = 1) : d153 pattern ≤ (20 : Int) + d902 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23122 pattern childGuard
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23125 pattern childGuard
    simpa only [d153, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23127 (pattern : Twelve) (guard : d1 pattern = 1) : d122 pattern ≤ (20 : Int) + d878 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d122, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22965 pattern childGuard
    simpa only [d122, d878, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d122, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23040 pattern childGuard
    simpa only [d122, d878, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23128 (pattern : Twelve) (guard : d1 pattern = 1) : d131 pattern ≤ (20 : Int) + d885 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d131, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23117 pattern childGuard
    simpa only [d131, d885, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d131, d885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23127 pattern childGuard
    simpa only [d131, d885, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23129 (pattern : Twelve) (guard : d1 pattern = 1) : d140 pattern ≤ (20 : Int) + d894 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d140, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22990 pattern childGuard
    simpa only [d140, d894, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d140, d894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23128 pattern childGuard
    simpa only [d140, d894, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23130 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (20 : Int) + d4 pattern := by
  change (3 : Int) ≤ (20 : Int) + 4
  decide
theorem c23131 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (20 : Int) + d117 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23030 pattern childGuard
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23130 pattern childGuard
    simpa only [d117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23132 (pattern : Twelve) (guard : d1 pattern = 1) : d3 pattern ≤ (20 : Int) + d119 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23030 pattern childGuard
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23131 pattern childGuard
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23133 (pattern : Twelve) (guard : d1 pattern = 1) : d123 pattern ≤ (20 : Int) + d879 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d123, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22961 pattern childGuard
    simpa only [d123, d879, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d123, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23132 pattern childGuard
    simpa only [d123, d879, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23134 (pattern : Twelve) (guard : d1 pattern = 1) : d132 pattern ≤ (20 : Int) + d886 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d132, d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23002 pattern childGuard
    simpa only [d132, d886, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d132, d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23133 pattern childGuard
    simpa only [d132, d886, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23135 (pattern : Twelve) (guard : d1 pattern = 1) : d141 pattern ≤ (20 : Int) + d895 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d141, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23134 pattern childGuard
    simpa only [d141, d895, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d141, d895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23114 pattern childGuard
    simpa only [d141, d895, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23136 (pattern : Twelve) (guard : d1 pattern = 1) : d147 pattern ≤ (20 : Int) + d900 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d147, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23129 pattern childGuard
    simpa only [d147, d900, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d147, d900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23135 pattern childGuard
    simpa only [d147, d900, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23137 (pattern : Twelve) (guard : d1 pattern = 1) : d5 pattern ≤ (20 : Int) + d5 pattern := by
  omega
theorem c23138 (pattern : Twelve) (guard : d1 pattern = 1) : d5 pattern ≤ (20 : Int) + d14 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23137 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22992 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23139 (pattern : Twelve) (guard : d1 pattern = 1) : d118 pattern ≤ (20 : Int) + d22 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d118, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23138 pattern childGuard
    simpa only [d118, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d118, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23003 pattern childGuard
    simpa only [d118, d22, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23140 (pattern : Twelve) (guard : d1 pattern = 1) : d124 pattern ≤ (20 : Int) + d127 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d124, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23001 pattern childGuard
    simpa only [d124, d127, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d124, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23139 pattern childGuard
    simpa only [d124, d127, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23141 (pattern : Twelve) (guard : d1 pattern = 1) : d117 pattern ≤ (20 : Int) + d15 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23130 pattern childGuard
    simpa only [d117, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d117, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23038 pattern childGuard
    simpa only [d117, d15, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23142 (pattern : Twelve) (guard : d1 pattern = 1) : d119 pattern ≤ (20 : Int) + d873 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23131 pattern childGuard
    simpa only [d119, d873, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d119, d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23141 pattern childGuard
    simpa only [d119, d873, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23143 (pattern : Twelve) (guard : d1 pattern = 1) : d125 pattern ≤ (20 : Int) + d880 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23142 pattern childGuard
    simpa only [d125, d880, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d125, d880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d125, d880, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23144 (pattern : Twelve) (guard : d1 pattern = 1) : d133 pattern ≤ (20 : Int) + d887 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d133, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23140 pattern childGuard
    simpa only [d133, d887, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d133, d887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23143 pattern childGuard
    simpa only [d133, d887, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23145 (pattern : Twelve) (guard : d1 pattern = 1) : d142 pattern ≤ (20 : Int) + d896 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d142, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23036 pattern childGuard
    simpa only [d142, d896, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d142, d896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23144 pattern childGuard
    simpa only [d142, d896, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23146 (pattern : Twelve) (guard : d1 pattern = 1) : d5 pattern ≤ (20 : Int) + d118 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23137 pattern childGuard
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23138 pattern childGuard
    simpa only [d118, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23147 (pattern : Twelve) (guard : d1 pattern = 1) : d126 pattern ≤ (20 : Int) + d881 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d126, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23001 pattern childGuard
    simpa only [d126, d881, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d126, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23146 pattern childGuard
    simpa only [d126, d881, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23148 (pattern : Twelve) (guard : d1 pattern = 1) : d47 pattern ≤ (20 : Int) + d125 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d47, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23132 pattern childGuard
    simpa only [d47, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d47, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d47, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23149 (pattern : Twelve) (guard : d1 pattern = 1) : d134 pattern ≤ (20 : Int) + d888 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d134, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23147 pattern childGuard
    simpa only [d134, d888, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d134, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23148 pattern childGuard
    simpa only [d134, d888, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23150 (pattern : Twelve) (guard : d1 pattern = 1) : d127 pattern ≤ (20 : Int) + d42 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d127, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23012 pattern childGuard
    simpa only [d127, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d127, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23008 pattern childGuard
    simpa only [d127, d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23151 (pattern : Twelve) (guard : d1 pattern = 1) : d128 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22996 pattern childGuard
    simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d128, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23152 (pattern : Twelve) (guard : d1 pattern = 1) : d135 pattern ≤ (20 : Int) + d889 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d135, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23150 pattern childGuard
    simpa only [d135, d889, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d135, d889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23151 pattern childGuard
    simpa only [d135, d889, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23153 (pattern : Twelve) (guard : d1 pattern = 1) : d143 pattern ≤ (20 : Int) + d897 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d143, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23149 pattern childGuard
    simpa only [d143, d897, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d143, d897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23152 pattern childGuard
    simpa only [d143, d897, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23154 (pattern : Twelve) (guard : d1 pattern = 1) : d148 pattern ≤ (20 : Int) + d901 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d148, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23145 pattern childGuard
    simpa only [d148, d901, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d148, d901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23153 pattern childGuard
    simpa only [d148, d901, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23155 (pattern : Twelve) (guard : d1 pattern = 1) : d151 pattern ≤ (20 : Int) + d903 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d151, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23136 pattern childGuard
    simpa only [d151, d903, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d151, d903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23154 pattern childGuard
    simpa only [d151, d903, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23156 (pattern : Twelve) (guard : d1 pattern = 1) : d152 pattern ≤ (20 : Int) + d904 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d152, d904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23124 pattern childGuard
    simpa only [d152, d904, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d152, d904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d152, d904, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23157 (pattern : Twelve) (guard : d1 pattern = 1) : d154 pattern ≤ (20 : Int) + d905 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d154, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23155 pattern childGuard
    simpa only [d154, d905, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d154, d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23156 pattern childGuard
    simpa only [d154, d905, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23158 (pattern : Twelve) (guard : d1 pattern = 1) : d155 pattern ≤ (20 : Int) + d906 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d155, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23126 pattern childGuard
    simpa only [d155, d906, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d155, d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23157 pattern childGuard
    simpa only [d155, d906, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23159 (pattern : Twelve) (guard : d1 pattern = 1) : d778 pattern ≤ (20 : Int) + d779 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d778, d779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23001 pattern childGuard
    simpa only [d778, d779, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d778, d779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23030 pattern childGuard
    simpa only [d778, d779, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23160 (pattern : Twelve) (guard : d1 pattern = 1) : d779 pattern ≤ (20 : Int) + d1247 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d779, d1247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23043 pattern childGuard
    simpa only [d779, d1247, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d779, d1247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23030 pattern childGuard
    simpa only [d779, d1247, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23161 (pattern : Twelve) (guard : d1 pattern = 1) : d782 pattern ≤ (20 : Int) + d1249 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d782, d1249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23159 pattern childGuard
    simpa only [d782, d1249, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d782, d1249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23160 pattern childGuard
    simpa only [d782, d1249, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23162 (pattern : Twelve) (guard : d1 pattern = 1) : d788 pattern ≤ (20 : Int) + d1253 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d788, d1253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22999 pattern childGuard
    simpa only [d788, d1253, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d788, d1253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23161 pattern childGuard
    simpa only [d788, d1253, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23163 (pattern : Twelve) (guard : d1 pattern = 1) : d38 pattern ≤ (20 : Int) + d1248 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d1248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23001 pattern childGuard
    simpa only [d38, d1248, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d38, d1248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23037 pattern childGuard
    simpa only [d38, d1248, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23164 (pattern : Twelve) (guard : d1 pattern = 1) : d789 pattern ≤ (20 : Int) + d1254 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d789, d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23163 pattern childGuard
    simpa only [d789, d1254, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d789, d1254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23057 pattern childGuard
    simpa only [d789, d1254, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23165 (pattern : Twelve) (guard : d1 pattern = 1) : d794 pattern ≤ (20 : Int) + d1258 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d794, d1258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23162 pattern childGuard
    simpa only [d794, d1258, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d794, d1258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23164 pattern childGuard
    simpa only [d794, d1258, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23166 (pattern : Twelve) (guard : d1 pattern = 1) : d783 pattern ≤ (20 : Int) + d59 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d783, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23089 pattern childGuard
    simpa only [d783, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d783, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23070 pattern childGuard
    simpa only [d783, d59, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23167 (pattern : Twelve) (guard : d1 pattern = 1) : d790 pattern ≤ (20 : Int) + d851 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d790, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23166 pattern childGuard
    simpa only [d790, d851, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d790, d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23094 pattern childGuard
    simpa only [d790, d851, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23168 (pattern : Twelve) (guard : d1 pattern = 1) : d795 pattern ≤ (20 : Int) + d860 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d795, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23167 pattern childGuard
    simpa only [d795, d860, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d795, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23100 pattern childGuard
    simpa only [d795, d860, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23169 (pattern : Twelve) (guard : d1 pattern = 1) : d798 pattern ≤ (20 : Int) + d1261 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d798, d1261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23165 pattern childGuard
    simpa only [d798, d1261, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d798, d1261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23168 pattern childGuard
    simpa only [d798, d1261, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23170 (pattern : Twelve) (guard : d1 pattern = 1) : d799 pattern ≤ (20 : Int) + d1261 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d799, d1261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23165 pattern childGuard
    simpa only [d799, d1261, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d799, d1261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23101 pattern childGuard
    simpa only [d799, d1261, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23171 (pattern : Twelve) (guard : d1 pattern = 1) : d802 pattern ≤ (20 : Int) + d1261 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23169 pattern childGuard
    simpa only [d802, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23170 pattern childGuard
    simpa only [d802, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23172 (pattern : Twelve) (guard : d1 pattern = 1) : d780 pattern ≤ (20 : Int) + d780 pattern := by
  omega
theorem c23173 (pattern : Twelve) (guard : d1 pattern = 1) : d784 pattern ≤ (20 : Int) + d1250 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d784, d1250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23041 pattern childGuard
    simpa only [d784, d1250, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d784, d1250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23172 pattern childGuard
    simpa only [d784, d1250, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23174 (pattern : Twelve) (guard : d1 pattern = 1) : d791 pattern ≤ (20 : Int) + d1255 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d791, d1255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23089 pattern childGuard
    simpa only [d791, d1255, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d791, d1255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23173 pattern childGuard
    simpa only [d791, d1255, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23175 (pattern : Twelve) (guard : d1 pattern = 1) : d796 pattern ≤ (20 : Int) + d1259 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d796, d1259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23174 pattern childGuard
    simpa only [d796, d1259, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d796, d1259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23100 pattern childGuard
    simpa only [d796, d1259, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23176 (pattern : Twelve) (guard : d1 pattern = 1) : d48 pattern ≤ (20 : Int) + d49 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23040 pattern childGuard
    simpa only [d48, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d48, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d48, d49, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23177 (pattern : Twelve) (guard : d1 pattern = 1) : d781 pattern ≤ (20 : Int) + d781 pattern := by
  omega
theorem c23178 (pattern : Twelve) (guard : d1 pattern = 1) : d785 pattern ≤ (20 : Int) + d1251 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d785, d1251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23176 pattern childGuard
    simpa only [d785, d1251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d785, d1251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23177 pattern childGuard
    simpa only [d785, d1251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23179 (pattern : Twelve) (guard : d1 pattern = 1) : d792 pattern ≤ (20 : Int) + d1256 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d792, d1256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23096 pattern childGuard
    simpa only [d792, d1256, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d792, d1256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23178 pattern childGuard
    simpa only [d792, d1256, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23180 (pattern : Twelve) (guard : d1 pattern = 1) : d786 pattern ≤ (20 : Int) + d787 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d786, d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23176 pattern childGuard
    simpa only [d786, d787, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d786, d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d786, d787, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23181 (pattern : Twelve) (guard : d1 pattern = 1) : d787 pattern ≤ (20 : Int) + d1252 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d787, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23098 pattern childGuard
    simpa only [d787, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d787, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d787, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23182 (pattern : Twelve) (guard : d1 pattern = 1) : d793 pattern ≤ (20 : Int) + d1257 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d793, d1257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23180 pattern childGuard
    simpa only [d793, d1257, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d793, d1257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23181 pattern childGuard
    simpa only [d793, d1257, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23183 (pattern : Twelve) (guard : d1 pattern = 1) : d797 pattern ≤ (20 : Int) + d1260 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d797, d1260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23179 pattern childGuard
    simpa only [d797, d1260, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d797, d1260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23182 pattern childGuard
    simpa only [d797, d1260, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23184 (pattern : Twelve) (guard : d1 pattern = 1) : d800 pattern ≤ (20 : Int) + d1262 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d800, d1262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23175 pattern childGuard
    simpa only [d800, d1262, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d800, d1262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23183 pattern childGuard
    simpa only [d800, d1262, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23185 (pattern : Twelve) (guard : d1 pattern = 1) : d801 pattern ≤ (20 : Int) + d1263 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d801, d1263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23101 pattern childGuard
    simpa only [d801, d1263, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d801, d1263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d801, d1263, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23186 (pattern : Twelve) (guard : d1 pattern = 1) : d803 pattern ≤ (20 : Int) + d1264 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d803, d1264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23184 pattern childGuard
    simpa only [d803, d1264, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d803, d1264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23185 pattern childGuard
    simpa only [d803, d1264, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23187 (pattern : Twelve) (guard : d1 pattern = 1) : d804 pattern ≤ (20 : Int) + d1265 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d804, d1265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23171 pattern childGuard
    simpa only [d804, d1265, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d804, d1265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23186 pattern childGuard
    simpa only [d804, d1265, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23188 (pattern : Twelve) (guard : d1 pattern = 1) : d805 pattern ≤ (20 : Int) + d1266 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d805, d1266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23158 pattern childGuard
    simpa only [d805, d1266, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d805, d1266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23187 pattern childGuard
    simpa only [d805, d1266, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23189 (pattern : Twelve) (guard : d1 pattern = 1) : d806 pattern ≤ (20 : Int) + d1267 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d806, d1267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23106 pattern childGuard
    simpa only [d806, d1267, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d806, d1267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23188 pattern childGuard
    simpa only [d806, d1267, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23190 (pattern : Twelve) (guard : d1 pattern = 1) : d7 pattern ≤ (20 : Int) + d8 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22959 pattern childGuard
    simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22974 pattern childGuard
    simpa only [d7, d8, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23191 (pattern : Twelve) (guard : d1 pattern = 1) : d17 pattern ≤ (20 : Int) + d1275 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22960 pattern childGuard
    simpa only [d17, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d17, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23190 pattern childGuard
    simpa only [d17, d1275, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23192 (pattern : Twelve) (guard : d1 pattern = 1) : d27 pattern ≤ (20 : Int) + d1278 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23191 pattern childGuard
    simpa only [d27, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d27, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23108 pattern childGuard
    simpa only [d27, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23193 (pattern : Twelve) (guard : d1 pattern = 1) : d814 pattern ≤ (20 : Int) + d872 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22964 pattern childGuard
    simpa only [d814, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d814, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23107 pattern childGuard
    simpa only [d814, d872, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23194 (pattern : Twelve) (guard : d1 pattern = 1) : d816 pattern ≤ (20 : Int) + d872 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23193 pattern childGuard
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23108 pattern childGuard
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23195 (pattern : Twelve) (guard : d1 pattern = 1) : d824 pattern ≤ (20 : Int) + d1284 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d824, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23192 pattern childGuard
    simpa only [d824, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d824, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23194 pattern childGuard
    simpa only [d824, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23196 (pattern : Twelve) (guard : d1 pattern = 1) : d838 pattern ≤ (20 : Int) + d1293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d838, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22961 pattern childGuard
    simpa only [d838, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d838, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23195 pattern childGuard
    simpa only [d838, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23197 (pattern : Twelve) (guard : d1 pattern = 1) : d0 pattern ≤ (20 : Int) + d6 pattern := by
  change (0 : Int) ≤ (20 : Int) + 6
  decide
theorem c23198 (pattern : Twelve) (guard : d1 pattern = 1) : d2 pattern ≤ (20 : Int) + d6 pattern := by
  change (2 : Int) ≤ (20 : Int) + 6
  decide
theorem c23199 (pattern : Twelve) (guard : d1 pattern = 1) : d10 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23197 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23198 pattern childGuard
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23200 (pattern : Twelve) (guard : d1 pattern = 1) : d1 pattern ≤ (20 : Int) + d6 pattern := by
  change (1 : Int) ≤ (20 : Int) + 6
  decide
theorem c23201 (pattern : Twelve) (guard : d1 pattern = 1) : d11 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23200 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22991 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23202 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23199 pattern childGuard
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23201 pattern childGuard
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23203 (pattern : Twelve) (guard : d1 pattern = 1) : d16 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23198 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22994 pattern childGuard
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23204 (pattern : Twelve) (guard : d1 pattern = 1) : d25 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23203 pattern childGuard
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22993 pattern childGuard
    simpa only [d25, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23205 (pattern : Twelve) (guard : d1 pattern = 1) : d817 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23202 pattern childGuard
    simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23204 pattern childGuard
    simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23206 (pattern : Twelve) (guard : d1 pattern = 1) : d42 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23204 pattern childGuard
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23207 (pattern : Twelve) (guard : d1 pattern = 1) : d825 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23205 pattern childGuard
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23206 pattern childGuard
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23208 (pattern : Twelve) (guard : d1 pattern = 1) : d839 pattern ≤ (20 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d839, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22973 pattern childGuard
    simpa only [d839, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d839, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23207 pattern childGuard
    simpa only [d839, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23209 (pattern : Twelve) (guard : d1 pattern = 1) : d853 pattern ≤ (20 : Int) + d1305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d853, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23196 pattern childGuard
    simpa only [d853, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d853, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23208 pattern childGuard
    simpa only [d853, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23210 (pattern : Twelve) (guard : d1 pattern = 1) : d9 pattern ≤ (20 : Int) + d117 pattern := by
  cases selected : pattern.l with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22977 pattern childGuard
    simpa only [d9, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d9, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23130 pattern childGuard
    simpa only [d9, d117, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23211 (pattern : Twelve) (guard : d1 pattern = 1) : d23 pattern ≤ (20 : Int) + d1276 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23000 pattern childGuard
    simpa only [d23, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d23, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23210 pattern childGuard
    simpa only [d23, d1276, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23212 (pattern : Twelve) (guard : d1 pattern = 1) : d34 pattern ≤ (20 : Int) + d1279 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23191 pattern childGuard
    simpa only [d34, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d34, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23211 pattern childGuard
    simpa only [d34, d1279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23213 (pattern : Twelve) (guard : d1 pattern = 1) : d818 pattern ≤ (20 : Int) + d1280 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d818, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23193 pattern childGuard
    simpa only [d818, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d818, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d818, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23214 (pattern : Twelve) (guard : d1 pattern = 1) : d826 pattern ≤ (20 : Int) + d1285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d826, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23212 pattern childGuard
    simpa only [d826, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d826, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23213 pattern childGuard
    simpa only [d826, d1285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23215 (pattern : Twelve) (guard : d1 pattern = 1) : d840 pattern ≤ (20 : Int) + d1295 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d840, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23025 pattern childGuard
    simpa only [d840, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d840, d1295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23214 pattern childGuard
    simpa only [d840, d1295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23216 (pattern : Twelve) (guard : d1 pattern = 1) : d36 pattern ≤ (20 : Int) + d29 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22973 pattern childGuard
    simpa only [d36, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d36, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d36, d29, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23217 (pattern : Twelve) (guard : d1 pattern = 1) : d827 pattern ≤ (20 : Int) + d1286 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d827, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23013 pattern childGuard
    simpa only [d827, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d827, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23216 pattern childGuard
    simpa only [d827, d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23218 (pattern : Twelve) (guard : d1 pattern = 1) : d841 pattern ≤ (20 : Int) + d1296 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d841, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23217 pattern childGuard
    simpa only [d841, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d841, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23207 pattern childGuard
    simpa only [d841, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23219 (pattern : Twelve) (guard : d1 pattern = 1) : d854 pattern ≤ (20 : Int) + d1306 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d854, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23215 pattern childGuard
    simpa only [d854, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d854, d1306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23218 pattern childGuard
    simpa only [d854, d1306, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23220 (pattern : Twelve) (guard : d1 pattern = 1) : d861 pattern ≤ (20 : Int) + d1313 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d861, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23209 pattern childGuard
    simpa only [d861, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d861, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23219 pattern childGuard
    simpa only [d861, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23221 (pattern : Twelve) (guard : d1 pattern = 1) : d819 pattern ≤ (20 : Int) + d1281 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d819, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23193 pattern childGuard
    simpa only [d819, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d819, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23132 pattern childGuard
    simpa only [d819, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23222 (pattern : Twelve) (guard : d1 pattern = 1) : d828 pattern ≤ (20 : Int) + d1287 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d828, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23212 pattern childGuard
    simpa only [d828, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d828, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23221 pattern childGuard
    simpa only [d828, d1287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23223 (pattern : Twelve) (guard : d1 pattern = 1) : d842 pattern ≤ (20 : Int) + d1297 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d842, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23002 pattern childGuard
    simpa only [d842, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d842, d1297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23222 pattern childGuard
    simpa only [d842, d1297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23224 (pattern : Twelve) (guard : d1 pattern = 1) : d843 pattern ≤ (20 : Int) + d1298 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d843, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23013 pattern childGuard
    simpa only [d843, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d843, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23207 pattern childGuard
    simpa only [d843, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23225 (pattern : Twelve) (guard : d1 pattern = 1) : d855 pattern ≤ (20 : Int) + d1307 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d855, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23223 pattern childGuard
    simpa only [d855, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d855, d1307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23224 pattern childGuard
    simpa only [d855, d1307, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23226 (pattern : Twelve) (guard : d1 pattern = 1) : d24 pattern ≤ (20 : Int) + d1277 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23039 pattern childGuard
    simpa only [d24, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d24, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23050 pattern childGuard
    simpa only [d24, d1277, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23227 (pattern : Twelve) (guard : d1 pattern = 1) : d41 pattern ≤ (20 : Int) + d1282 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23211 pattern childGuard
    simpa only [d41, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d41, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23226 pattern childGuard
    simpa only [d41, d1282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23228 (pattern : Twelve) (guard : d1 pattern = 1) : d815 pattern ≤ (20 : Int) + d119 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23042 pattern childGuard
    simpa only [d815, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d815, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23131 pattern childGuard
    simpa only [d815, d119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23229 (pattern : Twelve) (guard : d1 pattern = 1) : d820 pattern ≤ (20 : Int) + d125 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d820, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23228 pattern childGuard
    simpa only [d820, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d820, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d820, d125, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23230 (pattern : Twelve) (guard : d1 pattern = 1) : d829 pattern ≤ (20 : Int) + d1288 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d829, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23227 pattern childGuard
    simpa only [d829, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d829, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23229 pattern childGuard
    simpa only [d829, d1288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23231 (pattern : Twelve) (guard : d1 pattern = 1) : d844 pattern ≤ (20 : Int) + d1299 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d844, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23048 pattern childGuard
    simpa only [d844, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d844, d1299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23230 pattern childGuard
    simpa only [d844, d1299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23232 (pattern : Twelve) (guard : d1 pattern = 1) : d830 pattern ≤ (20 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23052 pattern childGuard
    simpa only [d830, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d830, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23072 pattern childGuard
    simpa only [d830, d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23233 (pattern : Twelve) (guard : d1 pattern = 1) : d821 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23204 pattern childGuard
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23004 pattern childGuard
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23234 (pattern : Twelve) (guard : d1 pattern = 1) : d822 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23004 pattern childGuard
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23235 (pattern : Twelve) (guard : d1 pattern = 1) : d831 pattern ≤ (20 : Int) + d6 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23233 pattern childGuard
    simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23234 pattern childGuard
    simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23236 (pattern : Twelve) (guard : d1 pattern = 1) : d845 pattern ≤ (20 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d845, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23232 pattern childGuard
    simpa only [d845, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d845, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23235 pattern childGuard
    simpa only [d845, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23237 (pattern : Twelve) (guard : d1 pattern = 1) : d856 pattern ≤ (20 : Int) + d1308 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d856, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23231 pattern childGuard
    simpa only [d856, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d856, d1308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23236 pattern childGuard
    simpa only [d856, d1308, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23238 (pattern : Twelve) (guard : d1 pattern = 1) : d862 pattern ≤ (20 : Int) + d1314 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d862, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23225 pattern childGuard
    simpa only [d862, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d862, d1314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23237 pattern childGuard
    simpa only [d862, d1314, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c23239 (pattern : Twelve) (guard : d1 pattern = 1) : d863 pattern ≤ (20 : Int) + d1315 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d863, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c23219 pattern childGuard
    simpa only [d863, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d863, d1315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c22985 pattern childGuard
    simpa only [d863, d1315, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
