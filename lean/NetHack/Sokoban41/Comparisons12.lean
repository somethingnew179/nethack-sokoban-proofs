/- Staged soko4-1 certificate. No result until all kernel checks pass. -/
import NetHack.Sokoban41.Comparisons11
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban41.Diagram
theorem c1920 (pattern : Ten) (guard : d352 pattern = 1) : d20 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d352 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1918 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d352 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1917 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1921 (pattern : Ten) (guard : d352 pattern = 1) : d24 pattern ≤ (1 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d352 pattern = 1 := by simpa only [d24, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1919 pattern childGuard
    simpa only [d24, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d352 pattern = 1 := by simpa only [d24, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1920 pattern childGuard
    simpa only [d24, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1922 (pattern : Ten) (guard : d352 pattern = 1) : d29 pattern ≤ (1 : Int) + d408 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d352 pattern = 1 := by simpa only [d29, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1911 pattern childGuard
    simpa only [d29, d408, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d352 pattern = 1 := by simpa only [d29, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1921 pattern childGuard
    simpa only [d29, d408, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1923 (pattern : Ten) (guard : d352 pattern = 1) : d25 pattern ≤ (1 : Int) + d25 pattern := by
  omega
theorem c1924 (pattern : Ten) (guard : d352 pattern = 1) : d30 pattern ≤ (1 : Int) + d227 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d352 pattern = 1 := by simpa only [d30, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1923 pattern childGuard
    simpa only [d30, d227, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d352 pattern = 1 := by simpa only [d30, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1921 pattern childGuard
    simpa only [d30, d227, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1925 (pattern : Ten) (guard : d352 pattern = 1) : d33 pattern ≤ (1 : Int) + d409 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d352 pattern = 1 := by simpa only [d33, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1922 pattern childGuard
    simpa only [d33, d409, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d352 pattern = 1 := by simpa only [d33, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1924 pattern childGuard
    simpa only [d33, d409, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1926 (pattern : Ten) (guard : d352 pattern = 1) : d26 pattern ≤ (1 : Int) + d26 pattern := by
  omega
theorem c1927 (pattern : Ten) (guard : d352 pattern = 1) : d27 pattern ≤ (1 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d352 pattern = 1 := by simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1920 pattern childGuard
    simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d352 pattern = 1 := by simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1917 pattern childGuard
    simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1928 (pattern : Ten) (guard : d352 pattern = 1) : d31 pattern ≤ (1 : Int) + d228 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d352 pattern = 1 := by simpa only [d31, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1926 pattern childGuard
    simpa only [d31, d228, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d352 pattern = 1 := by simpa only [d31, d228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1927 pattern childGuard
    simpa only [d31, d228, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1929 (pattern : Ten) (guard : d352 pattern = 1) : d28 pattern ≤ (1 : Int) + d28 pattern := by
  omega
theorem c1930 (pattern : Ten) (guard : d352 pattern = 1) : d32 pattern ≤ (1 : Int) + d229 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d352 pattern = 1 := by simpa only [d32, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1929 pattern childGuard
    simpa only [d32, d229, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d352 pattern = 1 := by simpa only [d32, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1927 pattern childGuard
    simpa only [d32, d229, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1931 (pattern : Ten) (guard : d352 pattern = 1) : d34 pattern ≤ (1 : Int) + d231 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d352 pattern = 1 := by simpa only [d34, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1928 pattern childGuard
    simpa only [d34, d231, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d352 pattern = 1 := by simpa only [d34, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1930 pattern childGuard
    simpa only [d34, d231, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1932 (pattern : Ten) (guard : d352 pattern = 1) : d35 pattern ≤ (1 : Int) + d410 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d352 pattern = 1 := by simpa only [d35, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1925 pattern childGuard
    simpa only [d35, d410, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d352 pattern = 1 := by simpa only [d35, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1931 pattern childGuard
    simpa only [d35, d410, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1933 (pattern : Ten) (guard : d352 pattern = 1) : d36 pattern ≤ (1 : Int) + d233 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d352 pattern = 1 := by simpa only [d36, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1931 pattern childGuard
    simpa only [d36, d233, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d352 pattern = 1 := by simpa only [d36, d233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1917 pattern childGuard
    simpa only [d36, d233, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1934 (pattern : Ten) (guard : d352 pattern = 1) : d37 pattern ≤ (1 : Int) + d411 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d352 pattern = 1 := by simpa only [d37, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1932 pattern childGuard
    simpa only [d37, d411, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d352 pattern = 1 := by simpa only [d37, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1933 pattern childGuard
    simpa only [d37, d411, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1935 (pattern : Ten) (guard : d0 pattern = 1) : d1 pattern ≤ (1 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1936 (pattern : Ten) (guard : d351 pattern = 1) : d171 pattern ≤ (1 : Int) + d1 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d351, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1848 pattern childGuard
    simpa only [d351, d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d351, d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1935 pattern childGuard
    simpa only [d351, d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1937 (pattern : Ten) (guard : d351 pattern = 1) : d10 pattern ≤ (1 : Int) + d10 pattern := by
  omega
theorem c1938 (pattern : Ten) (guard : d351 pattern = 1) : d173 pattern ≤ (1 : Int) + d412 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d173, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1936 pattern childGuard
    simpa only [d173, d412, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d173, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1937 pattern childGuard
    simpa only [d173, d412, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1939 (pattern : Ten) (guard : d351 pattern = 1) : d176 pattern ≤ (1 : Int) + d413 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d176, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1936 pattern childGuard
    simpa only [d176, d413, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d176, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1938 pattern childGuard
    simpa only [d176, d413, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1940 (pattern : Ten) (guard : d351 pattern = 1) : d177 pattern ≤ (1 : Int) + d414 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d177, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1938 pattern childGuard
    simpa only [d177, d414, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d177, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1937 pattern childGuard
    simpa only [d177, d414, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1941 (pattern : Ten) (guard : d351 pattern = 1) : d180 pattern ≤ (1 : Int) + d415 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d180, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1939 pattern childGuard
    simpa only [d180, d415, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d180, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1940 pattern childGuard
    simpa only [d180, d415, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1942 (pattern : Ten) (guard : d351 pattern = 1) : d181 pattern ≤ (1 : Int) + d416 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d181, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1940 pattern childGuard
    simpa only [d181, d416, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d181, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1937 pattern childGuard
    simpa only [d181, d416, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1943 (pattern : Ten) (guard : d351 pattern = 1) : d184 pattern ≤ (1 : Int) + d417 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d184, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1941 pattern childGuard
    simpa only [d184, d417, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d184, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1942 pattern childGuard
    simpa only [d184, d417, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1944 (pattern : Ten) (guard : d0 pattern = 1) : d3 pattern ≤ (1 : Int) + d3 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1945 (pattern : Ten) (guard : d351 pattern = 1) : d172 pattern ≤ (1 : Int) + d3 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d351, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1867 pattern childGuard
    simpa only [d351, d172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d351, d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1944 pattern childGuard
    simpa only [d351, d172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1946 (pattern : Ten) (guard : d351 pattern = 1) : d174 pattern ≤ (1 : Int) + d418 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d174, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1936 pattern childGuard
    simpa only [d174, d418, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d174, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1945 pattern childGuard
    simpa only [d174, d418, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1947 (pattern : Ten) (guard : d351 pattern = 1) : d175 pattern ≤ (1 : Int) + d419 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d175, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1945 pattern childGuard
    simpa only [d175, d419, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d175, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1937 pattern childGuard
    simpa only [d175, d419, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1948 (pattern : Ten) (guard : d351 pattern = 1) : d178 pattern ≤ (1 : Int) + d420 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d178, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1946 pattern childGuard
    simpa only [d178, d420, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d178, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1947 pattern childGuard
    simpa only [d178, d420, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1949 (pattern : Ten) (guard : d351 pattern = 1) : d179 pattern ≤ (1 : Int) + d421 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d179, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1947 pattern childGuard
    simpa only [d179, d421, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d179, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1937 pattern childGuard
    simpa only [d179, d421, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1950 (pattern : Ten) (guard : d351 pattern = 1) : d182 pattern ≤ (1 : Int) + d422 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d182, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1948 pattern childGuard
    simpa only [d182, d422, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d182, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1949 pattern childGuard
    simpa only [d182, d422, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1951 (pattern : Ten) (guard : d351 pattern = 1) : d185 pattern ≤ (1 : Int) + d423 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d185, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1950 pattern childGuard
    simpa only [d185, d423, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d185, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1942 pattern childGuard
    simpa only [d185, d423, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1952 (pattern : Ten) (guard : d351 pattern = 1) : d188 pattern ≤ (1 : Int) + d424 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d188, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1943 pattern childGuard
    simpa only [d188, d424, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d188, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1951 pattern childGuard
    simpa only [d188, d424, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1953 (pattern : Ten) (guard : d351 pattern = 1) : d186 pattern ≤ (1 : Int) + d425 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d186, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1942 pattern childGuard
    simpa only [d186, d425, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d186, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1937 pattern childGuard
    simpa only [d186, d425, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1954 (pattern : Ten) (guard : d351 pattern = 1) : d183 pattern ≤ (1 : Int) + d426 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d183, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1949 pattern childGuard
    simpa only [d183, d426, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d183, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1937 pattern childGuard
    simpa only [d183, d426, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1955 (pattern : Ten) (guard : d351 pattern = 1) : d187 pattern ≤ (1 : Int) + d427 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d187, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1954 pattern childGuard
    simpa only [d187, d427, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d187, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1937 pattern childGuard
    simpa only [d187, d427, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1956 (pattern : Ten) (guard : d351 pattern = 1) : d189 pattern ≤ (1 : Int) + d428 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d189, d428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1953 pattern childGuard
    simpa only [d189, d428, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d189, d428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1955 pattern childGuard
    simpa only [d189, d428, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1957 (pattern : Ten) (guard : d351 pattern = 1) : d190 pattern ≤ (1 : Int) + d429 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d190, d429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1952 pattern childGuard
    simpa only [d190, d429, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d190, d429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1956 pattern childGuard
    simpa only [d190, d429, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1958 (pattern : Ten) (guard : d351 pattern = 1) : d191 pattern ≤ (1 : Int) + d430 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d191, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1956 pattern childGuard
    simpa only [d191, d430, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d191, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1937 pattern childGuard
    simpa only [d191, d430, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1959 (pattern : Ten) (guard : d351 pattern = 1) : d192 pattern ≤ (1 : Int) + d431 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d351 pattern = 1 := by simpa only [d192, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1957 pattern childGuard
    simpa only [d192, d431, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d351 pattern = 1 := by simpa only [d192, d431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1958 pattern childGuard
    simpa only [d192, d431, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1960 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (2 : Int) + d0 pattern := by
  omega
theorem c1961 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (2 : Int) + d1 pattern := by
  change (0 : Int) ≤ (2 : Int) + 1
  decide
theorem c1962 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (2 : Int) + d171 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1960 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1961 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1963 (pattern : Ten) (guard : d0 pattern = 1) : d0 pattern ≤ (2 : Int) + d171 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1964 (pattern : Ten) (guard : d350 pattern = 1) : d0 pattern ≤ (2 : Int) + d171 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1962 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1963 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1965 (pattern : Ten) (guard : d350 pattern = 1) : d10 pattern ≤ (2 : Int) + d10 pattern := by
  omega
theorem c1966 (pattern : Ten) (guard : d350 pattern = 1) : d12 pattern ≤ (2 : Int) + d173 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d12, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1964 pattern childGuard
    simpa only [d12, d173, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d12, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d12, d173, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1967 (pattern : Ten) (guard : d350 pattern = 1) : d17 pattern ≤ (2 : Int) + d176 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d17, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1964 pattern childGuard
    simpa only [d17, d176, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d17, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1966 pattern childGuard
    simpa only [d17, d176, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1968 (pattern : Ten) (guard : d350 pattern = 1) : d18 pattern ≤ (2 : Int) + d177 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d18, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1966 pattern childGuard
    simpa only [d18, d177, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d18, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d18, d177, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1969 (pattern : Ten) (guard : d350 pattern = 1) : d23 pattern ≤ (2 : Int) + d180 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d23, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1967 pattern childGuard
    simpa only [d23, d180, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d23, d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1968 pattern childGuard
    simpa only [d23, d180, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1970 (pattern : Ten) (guard : d1 pattern = 1) : d9 pattern ≤ (2 : Int) + d10 pattern := by
  change (9 : Int) ≤ (2 : Int) + 10
  decide
theorem c1971 (pattern : Ten) (guard : d1 pattern = 1) : d10 pattern ≤ (2 : Int) + d10 pattern := by
  omega
theorem c1972 (pattern : Ten) (guard : d1 pattern = 1) : d11 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1970 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1973 (pattern : Ten) (guard : d0 pattern = 1) : d11 pattern ≤ (2 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1974 (pattern : Ten) (guard : d350 pattern = 1) : d11 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1972 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1973 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1975 (pattern : Ten) (guard : d350 pattern = 1) : d13 pattern ≤ (2 : Int) + d173 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d13, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1964 pattern childGuard
    simpa only [d13, d173, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d13, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1974 pattern childGuard
    simpa only [d13, d173, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1976 (pattern : Ten) (guard : d350 pattern = 1) : d14 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1974 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1977 (pattern : Ten) (guard : d350 pattern = 1) : d19 pattern ≤ (2 : Int) + d177 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d19, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1975 pattern childGuard
    simpa only [d19, d177, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d19, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1976 pattern childGuard
    simpa only [d19, d177, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1978 (pattern : Ten) (guard : d350 pattern = 1) : d20 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1976 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1979 (pattern : Ten) (guard : d350 pattern = 1) : d24 pattern ≤ (2 : Int) + d181 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d24, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1977 pattern childGuard
    simpa only [d24, d181, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d24, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1978 pattern childGuard
    simpa only [d24, d181, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1980 (pattern : Ten) (guard : d350 pattern = 1) : d29 pattern ≤ (2 : Int) + d184 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d29, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1969 pattern childGuard
    simpa only [d29, d184, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d29, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1979 pattern childGuard
    simpa only [d29, d184, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1981 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (2 : Int) + d2 pattern := by
  omega
theorem c1982 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (2 : Int) + d3 pattern := by
  change (2 : Int) ≤ (2 : Int) + 3
  decide
theorem c1983 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (2 : Int) + d172 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1981 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1982 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1984 (pattern : Ten) (guard : d0 pattern = 1) : d2 pattern ≤ (2 : Int) + d172 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c1985 (pattern : Ten) (guard : d350 pattern = 1) : d2 pattern ≤ (2 : Int) + d172 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1983 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1984 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1986 (pattern : Ten) (guard : d350 pattern = 1) : d15 pattern ≤ (2 : Int) + d174 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1964 pattern childGuard
    simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1985 pattern childGuard
    simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1987 (pattern : Ten) (guard : d350 pattern = 1) : d16 pattern ≤ (2 : Int) + d175 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d16, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1985 pattern childGuard
    simpa only [d16, d175, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d16, d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d16, d175, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1988 (pattern : Ten) (guard : d350 pattern = 1) : d21 pattern ≤ (2 : Int) + d178 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d21, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1986 pattern childGuard
    simpa only [d21, d178, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d21, d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1987 pattern childGuard
    simpa only [d21, d178, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1989 (pattern : Ten) (guard : d350 pattern = 1) : d22 pattern ≤ (2 : Int) + d179 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d22, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1987 pattern childGuard
    simpa only [d22, d179, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d22, d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d22, d179, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1990 (pattern : Ten) (guard : d350 pattern = 1) : d25 pattern ≤ (2 : Int) + d182 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d25, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1988 pattern childGuard
    simpa only [d25, d182, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d25, d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1989 pattern childGuard
    simpa only [d25, d182, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1991 (pattern : Ten) (guard : d350 pattern = 1) : d30 pattern ≤ (2 : Int) + d185 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d30, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1990 pattern childGuard
    simpa only [d30, d185, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d30, d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1979 pattern childGuard
    simpa only [d30, d185, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1992 (pattern : Ten) (guard : d350 pattern = 1) : d33 pattern ≤ (2 : Int) + d188 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d33, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1980 pattern childGuard
    simpa only [d33, d188, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d33, d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1991 pattern childGuard
    simpa only [d33, d188, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1993 (pattern : Ten) (guard : d350 pattern = 1) : d26 pattern ≤ (2 : Int) + d181 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d26, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1968 pattern childGuard
    simpa only [d26, d181, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d26, d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d26, d181, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1994 (pattern : Ten) (guard : d350 pattern = 1) : d27 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1978 pattern childGuard
    simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1995 (pattern : Ten) (guard : d350 pattern = 1) : d31 pattern ≤ (2 : Int) + d186 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d31, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1993 pattern childGuard
    simpa only [d31, d186, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d31, d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1994 pattern childGuard
    simpa only [d31, d186, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1996 (pattern : Ten) (guard : d350 pattern = 1) : d28 pattern ≤ (2 : Int) + d183 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d28, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1989 pattern childGuard
    simpa only [d28, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d28, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d28, d183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1997 (pattern : Ten) (guard : d350 pattern = 1) : d32 pattern ≤ (2 : Int) + d187 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d32, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1996 pattern childGuard
    simpa only [d32, d187, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d32, d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1994 pattern childGuard
    simpa only [d32, d187, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1998 (pattern : Ten) (guard : d350 pattern = 1) : d34 pattern ≤ (2 : Int) + d189 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d34, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1995 pattern childGuard
    simpa only [d34, d189, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d34, d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1997 pattern childGuard
    simpa only [d34, d189, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c1999 (pattern : Ten) (guard : d350 pattern = 1) : d35 pattern ≤ (2 : Int) + d190 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d35, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1992 pattern childGuard
    simpa only [d35, d190, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d35, d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1998 pattern childGuard
    simpa only [d35, d190, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2000 (pattern : Ten) (guard : d350 pattern = 1) : d36 pattern ≤ (2 : Int) + d191 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d36, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1998 pattern childGuard
    simpa only [d36, d191, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d36, d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1965 pattern childGuard
    simpa only [d36, d191, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2001 (pattern : Ten) (guard : d350 pattern = 1) : d37 pattern ≤ (2 : Int) + d192 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d37, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1999 pattern childGuard
    simpa only [d37, d192, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d37, d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2000 pattern childGuard
    simpa only [d37, d192, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2002 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (2 : Int) + d10 pattern := by
  change (0 : Int) ≤ (2 : Int) + 10
  decide
theorem c2003 (pattern : Ten) (guard : d1 pattern = 1) : d1 pattern ≤ (2 : Int) + d10 pattern := by
  change (1 : Int) ≤ (2 : Int) + 10
  decide
theorem c2004 (pattern : Ten) (guard : d1 pattern = 1) : d171 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2002 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2003 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2005 (pattern : Ten) (guard : d1 pattern = 1) : d173 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2004 pattern childGuard
    simpa only [d173, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d173, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2006 (pattern : Ten) (guard : d1 pattern = 1) : d176 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2004 pattern childGuard
    simpa only [d176, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2005 pattern childGuard
    simpa only [d176, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2007 (pattern : Ten) (guard : d1 pattern = 1) : d177 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2005 pattern childGuard
    simpa only [d177, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d177, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2008 (pattern : Ten) (guard : d1 pattern = 1) : d180 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2006 pattern childGuard
    simpa only [d180, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2007 pattern childGuard
    simpa only [d180, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2009 (pattern : Ten) (guard : d1 pattern = 1) : d181 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2007 pattern childGuard
    simpa only [d181, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d181, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2010 (pattern : Ten) (guard : d1 pattern = 1) : d184 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2008 pattern childGuard
    simpa only [d184, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2009 pattern childGuard
    simpa only [d184, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2011 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (2 : Int) + d10 pattern := by
  change (2 : Int) ≤ (2 : Int) + 10
  decide
theorem c2012 (pattern : Ten) (guard : d1 pattern = 1) : d3 pattern ≤ (2 : Int) + d10 pattern := by
  change (3 : Int) ≤ (2 : Int) + 10
  decide
theorem c2013 (pattern : Ten) (guard : d1 pattern = 1) : d172 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2011 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2012 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2014 (pattern : Ten) (guard : d1 pattern = 1) : d174 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2004 pattern childGuard
    simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2013 pattern childGuard
    simpa only [d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2015 (pattern : Ten) (guard : d1 pattern = 1) : d175 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2013 pattern childGuard
    simpa only [d175, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d175, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2016 (pattern : Ten) (guard : d1 pattern = 1) : d178 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2014 pattern childGuard
    simpa only [d178, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2015 pattern childGuard
    simpa only [d178, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2017 (pattern : Ten) (guard : d1 pattern = 1) : d179 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2015 pattern childGuard
    simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d179, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2018 (pattern : Ten) (guard : d1 pattern = 1) : d182 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2016 pattern childGuard
    simpa only [d182, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2017 pattern childGuard
    simpa only [d182, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2019 (pattern : Ten) (guard : d1 pattern = 1) : d185 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2018 pattern childGuard
    simpa only [d185, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2009 pattern childGuard
    simpa only [d185, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2020 (pattern : Ten) (guard : d1 pattern = 1) : d188 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2010 pattern childGuard
    simpa only [d188, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2019 pattern childGuard
    simpa only [d188, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2021 (pattern : Ten) (guard : d1 pattern = 1) : d186 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2009 pattern childGuard
    simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d186, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2022 (pattern : Ten) (guard : d1 pattern = 1) : d183 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2017 pattern childGuard
    simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d183, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2023 (pattern : Ten) (guard : d1 pattern = 1) : d187 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2022 pattern childGuard
    simpa only [d187, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d187, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2024 (pattern : Ten) (guard : d1 pattern = 1) : d189 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2021 pattern childGuard
    simpa only [d189, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2023 pattern childGuard
    simpa only [d189, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2025 (pattern : Ten) (guard : d1 pattern = 1) : d190 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2020 pattern childGuard
    simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2024 pattern childGuard
    simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2026 (pattern : Ten) (guard : d1 pattern = 1) : d191 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2024 pattern childGuard
    simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1971 pattern childGuard
    simpa only [d191, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2027 (pattern : Ten) (guard : d1 pattern = 1) : d192 pattern ≤ (2 : Int) + d10 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2025 pattern childGuard
    simpa only [d192, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2026 pattern childGuard
    simpa only [d192, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2028 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (7 : Int) + d0 pattern := by
  omega
theorem c2029 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (7 : Int) + d1 pattern := by
  change (0 : Int) ≤ (7 : Int) + 1
  decide
theorem c2030 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (7 : Int) + d171 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2028 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2029 pattern childGuard
    simpa only [d171, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2031 (pattern : Ten) (guard : d0 pattern = 1) : d0 pattern ≤ (7 : Int) + d171 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2032 (pattern : Ten) (guard : d350 pattern = 1) : d0 pattern ≤ (7 : Int) + d171 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2030 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2031 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2033 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (7 : Int) + d2 pattern := by
  omega
theorem c2034 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (7 : Int) + d3 pattern := by
  change (2 : Int) ≤ (7 : Int) + 3
  decide
theorem c2035 (pattern : Ten) (guard : d1 pattern = 1) : d2 pattern ≤ (7 : Int) + d172 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2033 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2034 pattern childGuard
    simpa only [d172, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2036 (pattern : Ten) (guard : d0 pattern = 1) : d2 pattern ≤ (7 : Int) + d172 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2037 (pattern : Ten) (guard : d350 pattern = 1) : d2 pattern ≤ (7 : Int) + d172 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2035 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2036 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2038 (pattern : Ten) (guard : d350 pattern = 1) : d15 pattern ≤ (7 : Int) + d174 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2032 pattern childGuard
    simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2037 pattern childGuard
    simpa only [d15, d174, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2039 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (7 : Int) + d4 pattern := by
  omega
theorem c2040 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (7 : Int) + d5 pattern := by
  change (4 : Int) ≤ (7 : Int) + 5
  decide
theorem c2041 (pattern : Ten) (guard : d1 pattern = 1) : d4 pattern ≤ (7 : Int) + d193 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2039 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2040 pattern childGuard
    simpa only [d193, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2042 (pattern : Ten) (guard : d0 pattern = 1) : d4 pattern ≤ (7 : Int) + d193 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2043 (pattern : Ten) (guard : d350 pattern = 1) : d4 pattern ≤ (7 : Int) + d193 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2041 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2042 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2044 (pattern : Ten) (guard : d350 pattern = 1) : d10 pattern ≤ (7 : Int) + d10 pattern := by
  omega
theorem c2045 (pattern : Ten) (guard : d350 pattern = 1) : d42 pattern ≤ (7 : Int) + d197 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d42, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2043 pattern childGuard
    simpa only [d42, d197, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d42, d197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2044 pattern childGuard
    simpa only [d42, d197, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2046 (pattern : Ten) (guard : d350 pattern = 1) : d48 pattern ≤ (7 : Int) + d202 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d48, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2038 pattern childGuard
    simpa only [d48, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d48, d202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2045 pattern childGuard
    simpa only [d48, d202, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2047 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (7 : Int) + d6 pattern := by
  omega
theorem c2048 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (7 : Int) + d7 pattern := by
  change (6 : Int) ≤ (7 : Int) + 7
  decide
theorem c2049 (pattern : Ten) (guard : d1 pattern = 1) : d6 pattern ≤ (7 : Int) + d194 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2047 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2048 pattern childGuard
    simpa only [d194, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2050 (pattern : Ten) (guard : d0 pattern = 1) : d6 pattern ≤ (7 : Int) + d194 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2051 (pattern : Ten) (guard : d350 pattern = 1) : d6 pattern ≤ (7 : Int) + d194 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2049 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2050 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2052 (pattern : Ten) (guard : d350 pattern = 1) : d43 pattern ≤ (7 : Int) + d198 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d43, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2051 pattern childGuard
    simpa only [d43, d198, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d43, d198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2044 pattern childGuard
    simpa only [d43, d198, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2053 (pattern : Ten) (guard : d350 pattern = 1) : d49 pattern ≤ (7 : Int) + d203 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d49, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2052 pattern childGuard
    simpa only [d49, d203, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d49, d203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2044 pattern childGuard
    simpa only [d49, d203, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2054 (pattern : Ten) (guard : d350 pattern = 1) : d54 pattern ≤ (7 : Int) + d207 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d54, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2046 pattern childGuard
    simpa only [d54, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d54, d207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2053 pattern childGuard
    simpa only [d54, d207, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2055 (pattern : Ten) (guard : d1 pattern = 1) : d9 pattern ≤ (7 : Int) + d10 pattern := by
  change (9 : Int) ≤ (7 : Int) + 10
  decide
theorem c2056 (pattern : Ten) (guard : d1 pattern = 1) : d10 pattern ≤ (7 : Int) + d10 pattern := by
  omega
theorem c2057 (pattern : Ten) (guard : d1 pattern = 1) : d11 pattern ≤ (7 : Int) + d10 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2055 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2056 pattern childGuard
    simpa only [d11, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2058 (pattern : Ten) (guard : d0 pattern = 1) : d11 pattern ≤ (7 : Int) + d10 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2059 (pattern : Ten) (guard : d350 pattern = 1) : d11 pattern ≤ (7 : Int) + d10 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2057 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2058 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2060 (pattern : Ten) (guard : d350 pattern = 1) : d14 pattern ≤ (7 : Int) + d10 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2059 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2044 pattern childGuard
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2061 (pattern : Ten) (guard : d350 pattern = 1) : d20 pattern ≤ (7 : Int) + d10 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2060 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2044 pattern childGuard
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2062 (pattern : Ten) (guard : d350 pattern = 1) : d27 pattern ≤ (7 : Int) + d10 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2061 pattern childGuard
    simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2044 pattern childGuard
    simpa only [d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2063 (pattern : Ten) (guard : d350 pattern = 1) : d58 pattern ≤ (7 : Int) + d211 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d58, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2054 pattern childGuard
    simpa only [d58, d211, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d58, d211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2062 pattern childGuard
    simpa only [d58, d211, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2064 (pattern : Ten) (guard : d350 pattern = 1) : d44 pattern ≤ (7 : Int) + d199 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d44, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2037 pattern childGuard
    simpa only [d44, d199, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d44, d199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2043 pattern childGuard
    simpa only [d44, d199, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2065 (pattern : Ten) (guard : d350 pattern = 1) : d50 pattern ≤ (7 : Int) + d204 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d50, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2064 pattern childGuard
    simpa only [d50, d204, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d50, d204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2052 pattern childGuard
    simpa only [d50, d204, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2066 (pattern : Ten) (guard : d1 pattern = 1) : d8 pattern ≤ (7 : Int) + d8 pattern := by
  omega
theorem c2067 (pattern : Ten) (guard : d1 pattern = 1) : d8 pattern ≤ (7 : Int) + d9 pattern := by
  change (8 : Int) ≤ (7 : Int) + 9
  decide
theorem c2068 (pattern : Ten) (guard : d1 pattern = 1) : d8 pattern ≤ (7 : Int) + d195 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2066 pattern childGuard
    simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1 pattern = 1 := by simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2067 pattern childGuard
    simpa only [d195, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2069 (pattern : Ten) (guard : d0 pattern = 1) : d8 pattern ≤ (7 : Int) + d195 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2070 (pattern : Ten) (guard : d350 pattern = 1) : d8 pattern ≤ (7 : Int) + d195 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2068 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2069 pattern childGuard
    simpa only [d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2071 (pattern : Ten) (guard : d350 pattern = 1) : d45 pattern ≤ (7 : Int) + d200 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d45, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2070 pattern childGuard
    simpa only [d45, d200, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d45, d200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2044 pattern childGuard
    simpa only [d45, d200, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2072 (pattern : Ten) (guard : d350 pattern = 1) : d51 pattern ≤ (7 : Int) + d205 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d51, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2071 pattern childGuard
    simpa only [d51, d205, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d51, d205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2044 pattern childGuard
    simpa only [d51, d205, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2073 (pattern : Ten) (guard : d350 pattern = 1) : d55 pattern ≤ (7 : Int) + d208 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d55, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2065 pattern childGuard
    simpa only [d55, d208, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d55, d208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2072 pattern childGuard
    simpa only [d55, d208, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2074 (pattern : Ten) (guard : d350 pattern = 1) : d59 pattern ≤ (7 : Int) + d212 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d59, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2073 pattern childGuard
    simpa only [d59, d212, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d59, d212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2062 pattern childGuard
    simpa only [d59, d212, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2075 (pattern : Ten) (guard : d350 pattern = 1) : d62 pattern ≤ (7 : Int) + d215 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d62, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2063 pattern childGuard
    simpa only [d62, d215, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d62, d215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2074 pattern childGuard
    simpa only [d62, d215, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2076 (pattern : Ten) (guard : d350 pattern = 1) : d64 pattern ≤ (7 : Int) + d218 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d64, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2054 pattern childGuard
    simpa only [d64, d218, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d350 pattern = 1 := by simpa only [d64, d218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2075 pattern childGuard
    simpa only [d64, d218, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2077 (pattern : Ten) (guard : d0 pattern = 1) : d7 pattern ≤ (7 : Int) + d219 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c2078 (pattern : Ten) (guard : d362 pattern = 1) : d133 pattern ≤ (7 : Int) + d220 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d350 pattern = 1 := by simpa only [d362, d133, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2076 pattern childGuard
    simpa only [d362, d133, d220, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d362, d133, d220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2077 pattern childGuard
    simpa only [d362, d133, d220, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c2079 (pattern : Ten) (guard : d1 pattern = 1) : d0 pattern ≤ (7 : Int) + d10 pattern := by
  change (0 : Int) ≤ (7 : Int) + 10
  decide
end NetHack.Sokoban41.Diagram
